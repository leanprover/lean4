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
lean_object* v_a_225_; lean_object* v_toCommandContextInfo_228_; lean_object* v_env_229_; lean_object* v_options_230_; lean_object* v_currNamespace_231_; lean_object* v_openDecls_232_; lean_object* v_ngen_233_; uint8_t v___x_234_; lean_object* v_env_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint16_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint16_t v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; uint16_t v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; uint8_t v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v_fileName_369_; lean_object* v_fileMap_370_; lean_object* v_currNamespace_371_; lean_object* v_openDecls_372_; lean_object* v_initHeartbeats_373_; lean_object* v_maxHeartbeats_374_; lean_object* v_quotContext_375_; lean_object* v_currMacroScope_376_; lean_object* v_cancelTk_x3f_377_; lean_object* v_inheritedTraceOptions_378_; lean_object* v_currRecDepth_379_; lean_object* v_ref_380_; uint8_t v_suppressElabErrors_381_; uint8_t v_isRecordingDeps_382_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___y_391_; lean_object* v_env_412_; uint8_t v___x_413_; uint8_t v___x_414_; 
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
v___x_246_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3);
v___x_247_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4));
v___x_248_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7);
v___x_249_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10);
v___x_250_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11));
v___x_251_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12);
v___x_252_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13);
v___x_253_ = 1;
v___x_254_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14);
v___x_255_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_255_, 0, v_env_235_);
lean_ctor_set(v___x_255_, 1, v___x_246_);
lean_ctor_set(v___x_255_, 2, v_ngen_233_);
lean_ctor_set(v___x_255_, 3, v___x_247_);
lean_ctor_set(v___x_255_, 4, v___x_248_);
lean_ctor_set(v___x_255_, 5, v___x_249_);
lean_ctor_set(v___x_255_, 6, v___x_251_);
lean_ctor_set(v___x_255_, 7, v___x_252_);
lean_ctor_set(v___x_255_, 8, v___x_254_);
lean_ctor_set(v___x_255_, 9, v___x_250_);
v___x_256_ = lean_io_get_num_heartbeats();
v___x_257_ = lean_st_mk_ref(v___x_255_);
v___x_387_ = l_Lean_inheritedTraceOptions;
v___x_388_ = lean_st_ref_get(v___x_387_);
v___x_389_ = lean_st_ref_get(v___x_257_);
v_env_412_ = lean_ctor_get(v___x_389_, 0);
lean_inc_ref(v_env_412_);
lean_dec(v___x_389_);
v___x_413_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_412_);
lean_dec_ref(v_env_412_);
v___x_414_ = lean_uint8_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__20, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__20_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__20);
if (v___x_414_ == 0)
{
if (v___x_413_ == 0)
{
v___y_391_ = v___x_253_;
goto v___jp_390_;
}
else
{
v_fileName_369_ = v___x_236_;
v_fileMap_370_ = v___x_237_;
v_currNamespace_371_ = v_currNamespace_231_;
v_openDecls_372_ = v_openDecls_232_;
v_initHeartbeats_373_ = v___x_256_;
v_maxHeartbeats_374_ = v___x_240_;
v_quotContext_375_ = v___x_241_;
v_currMacroScope_376_ = v___x_242_;
v_cancelTk_x3f_377_ = v___x_243_;
v_inheritedTraceOptions_378_ = v___x_388_;
v_currRecDepth_379_ = v___x_239_;
v_ref_380_ = v___x_244_;
v_suppressElabErrors_381_ = v___x_234_;
v_isRecordingDeps_382_ = v___x_234_;
goto v___jp_368_;
}
}
else
{
if (v___x_413_ == 0)
{
v_fileName_369_ = v___x_236_;
v_fileMap_370_ = v___x_237_;
v_currNamespace_371_ = v_currNamespace_231_;
v_openDecls_372_ = v_openDecls_232_;
v_initHeartbeats_373_ = v___x_256_;
v_maxHeartbeats_374_ = v___x_240_;
v_quotContext_375_ = v___x_241_;
v_currMacroScope_376_ = v___x_242_;
v_cancelTk_x3f_377_ = v___x_243_;
v_inheritedTraceOptions_378_ = v___x_388_;
v_currRecDepth_379_ = v___x_239_;
v_ref_380_ = v___x_244_;
v_suppressElabErrors_381_ = v___x_234_;
v_isRecordingDeps_382_ = v___x_234_;
goto v___jp_368_;
}
else
{
v___y_391_ = v___x_234_;
goto v___jp_390_;
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
v___jp_258_:
{
lean_object* v_toCold_264_; lean_object* v_currRecDepth_265_; lean_object* v_ref_266_; uint8_t v_suppressElabErrors_267_; uint8_t v_isRecordingDeps_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_327_; 
v_toCold_264_ = lean_ctor_get(v___y_262_, 0);
v_currRecDepth_265_ = lean_ctor_get(v___y_262_, 1);
v_ref_266_ = lean_ctor_get(v___y_262_, 2);
v_suppressElabErrors_267_ = lean_ctor_get_uint8(v___y_262_, sizeof(void*)*3 + 2);
v_isRecordingDeps_268_ = lean_ctor_get_uint8(v___y_262_, sizeof(void*)*3 + 3);
v_isSharedCheck_327_ = !lean_is_exclusive(v___y_262_);
if (v_isSharedCheck_327_ == 0)
{
v___x_270_ = v___y_262_;
v_isShared_271_ = v_isSharedCheck_327_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_ref_266_);
lean_inc(v_currRecDepth_265_);
lean_inc(v_toCold_264_);
lean_dec(v___y_262_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_327_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v_fileName_272_; lean_object* v_fileMap_273_; lean_object* v_currNamespace_274_; lean_object* v_openDecls_275_; lean_object* v_initHeartbeats_276_; lean_object* v_maxHeartbeats_277_; lean_object* v_quotContext_278_; lean_object* v_currMacroScope_279_; lean_object* v_cancelTk_x3f_280_; lean_object* v_inheritedTraceOptions_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_324_; 
v_fileName_272_ = lean_ctor_get(v_toCold_264_, 0);
v_fileMap_273_ = lean_ctor_get(v_toCold_264_, 1);
v_currNamespace_274_ = lean_ctor_get(v_toCold_264_, 4);
v_openDecls_275_ = lean_ctor_get(v_toCold_264_, 5);
v_initHeartbeats_276_ = lean_ctor_get(v_toCold_264_, 6);
v_maxHeartbeats_277_ = lean_ctor_get(v_toCold_264_, 7);
v_quotContext_278_ = lean_ctor_get(v_toCold_264_, 8);
v_currMacroScope_279_ = lean_ctor_get(v_toCold_264_, 9);
v_cancelTk_x3f_280_ = lean_ctor_get(v_toCold_264_, 10);
v_inheritedTraceOptions_281_ = lean_ctor_get(v_toCold_264_, 11);
v_isSharedCheck_324_ = !lean_is_exclusive(v_toCold_264_);
if (v_isSharedCheck_324_ == 0)
{
lean_object* v_unused_325_; lean_object* v_unused_326_; 
v_unused_325_ = lean_ctor_get(v_toCold_264_, 3);
lean_dec(v_unused_325_);
v_unused_326_ = lean_ctor_get(v_toCold_264_, 2);
lean_dec(v_unused_326_);
v___x_283_ = v_toCold_264_;
v_isShared_284_ = v_isSharedCheck_324_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_inheritedTraceOptions_281_);
lean_inc(v_cancelTk_x3f_280_);
lean_inc(v_currMacroScope_279_);
lean_inc(v_quotContext_278_);
lean_inc(v_maxHeartbeats_277_);
lean_inc(v_initHeartbeats_276_);
lean_inc(v_openDecls_275_);
lean_inc(v_currNamespace_274_);
lean_inc(v_fileMap_273_);
lean_inc(v_fileName_272_);
lean_dec(v_toCold_264_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_324_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v___y_261_, v___y_260_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 3, v___x_285_);
lean_ctor_set(v___x_283_, 2, v___y_261_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_fileName_272_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_fileMap_273_);
lean_ctor_set(v_reuseFailAlloc_323_, 2, v___y_261_);
lean_ctor_set(v_reuseFailAlloc_323_, 3, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_323_, 4, v_currNamespace_274_);
lean_ctor_set(v_reuseFailAlloc_323_, 5, v_openDecls_275_);
lean_ctor_set(v_reuseFailAlloc_323_, 6, v_initHeartbeats_276_);
lean_ctor_set(v_reuseFailAlloc_323_, 7, v_maxHeartbeats_277_);
lean_ctor_set(v_reuseFailAlloc_323_, 8, v_quotContext_278_);
lean_ctor_set(v_reuseFailAlloc_323_, 9, v_currMacroScope_279_);
lean_ctor_set(v_reuseFailAlloc_323_, 10, v_cancelTk_x3f_280_);
lean_ctor_set(v_reuseFailAlloc_323_, 11, v_inheritedTraceOptions_281_);
v___x_287_ = v_reuseFailAlloc_323_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_289_; 
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_287_);
v___x_289_ = v___x_270_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_currRecDepth_265_);
lean_ctor_set(v_reuseFailAlloc_322_, 2, v_ref_266_);
lean_ctor_set_uint8(v_reuseFailAlloc_322_, sizeof(void*)*3 + 2, v_suppressElabErrors_267_);
lean_ctor_set_uint8(v_reuseFailAlloc_322_, sizeof(void*)*3 + 3, v_isRecordingDeps_268_);
v___x_289_ = v_reuseFailAlloc_322_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; 
lean_ctor_set_uint16(v___x_289_, sizeof(void*)*3, v___y_259_);
v___x_290_ = lean_apply_3(v_x_222_, v___x_289_, v___y_263_, lean_box(0));
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_299_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_299_ == 0)
{
v___x_293_ = v___x_290_;
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_295_ = lean_st_ref_get(v___x_257_);
lean_dec(v___x_257_);
lean_dec(v___x_295_);
if (v_isShared_294_ == 0)
{
v___x_297_ = v___x_293_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_291_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_321_; 
lean_dec(v___x_257_);
v_a_300_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_321_ == 0)
{
v___x_302_ = v___x_290_;
v_isShared_303_ = v_isSharedCheck_321_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_290_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_321_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
if (lean_obj_tag(v_a_300_) == 0)
{
lean_object* v_msg_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
v_msg_304_ = lean_ctor_get(v_a_300_, 1);
lean_inc_ref(v_msg_304_);
lean_dec_ref_known(v_a_300_, 2);
v___x_305_ = l_Lean_MessageData_toString(v_msg_304_);
v___x_306_ = lean_mk_io_user_error(v___x_305_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_306_);
v___x_308_ = v___x_302_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
else
{
lean_object* v_id_310_; lean_object* v___x_311_; 
lean_del_object(v___x_302_);
v_id_310_ = lean_ctor_get(v_a_300_, 0);
lean_inc(v_id_310_);
lean_dec_ref_known(v_a_300_, 2);
v___x_311_ = l_Lean_InternalExceptionId_getName(v_id_310_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_id_310_);
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref_known(v___x_311_, 1);
v___x_313_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15));
v___x_314_ = l_Lean_Name_toString(v_a_312_, v___x_253_);
v___x_315_ = lean_string_append(v___x_313_, v___x_314_);
lean_dec_ref(v___x_314_);
v_a_225_ = v___x_315_;
goto v___jp_224_;
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref_known(v___x_311_, 1);
v___x_316_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16));
v___x_317_ = l_Nat_reprFast(v_id_310_);
v___x_318_ = lean_string_append(v___x_316_, v___x_317_);
lean_dec_ref(v___x_317_);
v___x_319_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17));
v___x_320_ = lean_string_append(v___x_318_, v___x_319_);
v_a_225_ = v___x_320_;
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
v___jp_328_:
{
lean_object* v___x_335_; lean_object* v_env_336_; lean_object* v_nextMacroScope_337_; lean_object* v_ngen_338_; lean_object* v_auxDeclNGen_339_; lean_object* v_traceState_340_; lean_object* v_recordedDeps_341_; lean_object* v_messages_342_; lean_object* v_infoState_343_; lean_object* v_snapshotTasks_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_353_; 
v___x_335_ = lean_st_ref_take(v___y_334_);
v_env_336_ = lean_ctor_get(v___x_335_, 0);
v_nextMacroScope_337_ = lean_ctor_get(v___x_335_, 1);
v_ngen_338_ = lean_ctor_get(v___x_335_, 2);
v_auxDeclNGen_339_ = lean_ctor_get(v___x_335_, 3);
v_traceState_340_ = lean_ctor_get(v___x_335_, 4);
v_recordedDeps_341_ = lean_ctor_get(v___x_335_, 6);
v_messages_342_ = lean_ctor_get(v___x_335_, 7);
v_infoState_343_ = lean_ctor_get(v___x_335_, 8);
v_snapshotTasks_344_ = lean_ctor_get(v___x_335_, 9);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; 
v_unused_354_ = lean_ctor_get(v___x_335_, 5);
lean_dec(v_unused_354_);
v___x_346_ = v___x_335_;
v_isShared_347_ = v_isSharedCheck_353_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_snapshotTasks_344_);
lean_inc(v_infoState_343_);
lean_inc(v_messages_342_);
lean_inc(v_recordedDeps_341_);
lean_inc(v_traceState_340_);
lean_inc(v_auxDeclNGen_339_);
lean_inc(v_ngen_338_);
lean_inc(v_nextMacroScope_337_);
lean_inc(v_env_336_);
lean_dec(v___x_335_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_353_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_348_ = l_Lean_Kernel_enableDiag(v_env_336_, v___y_332_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 5, v___x_249_);
lean_ctor_set(v___x_346_, 0, v___x_348_);
v___x_350_ = v___x_346_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_nextMacroScope_337_);
lean_ctor_set(v_reuseFailAlloc_352_, 2, v_ngen_338_);
lean_ctor_set(v_reuseFailAlloc_352_, 3, v_auxDeclNGen_339_);
lean_ctor_set(v_reuseFailAlloc_352_, 4, v_traceState_340_);
lean_ctor_set(v_reuseFailAlloc_352_, 5, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_352_, 6, v_recordedDeps_341_);
lean_ctor_set(v_reuseFailAlloc_352_, 7, v_messages_342_);
lean_ctor_set(v_reuseFailAlloc_352_, 8, v_infoState_343_);
lean_ctor_set(v_reuseFailAlloc_352_, 9, v_snapshotTasks_344_);
v___x_350_ = v_reuseFailAlloc_352_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; 
v___x_351_ = lean_st_ref_put(v___y_334_, v___x_350_);
v___y_259_ = v___y_329_;
v___y_260_ = v___y_330_;
v___y_261_ = v___y_333_;
v___y_262_ = v___y_331_;
v___y_263_ = v___y_334_;
goto v___jp_258_;
}
}
}
v___jp_355_:
{
uint16_t v___x_360_; lean_object* v___x_361_; lean_object* v_env_362_; uint8_t v___x_363_; uint16_t v___x_364_; uint16_t v___x_365_; uint16_t v___x_366_; uint8_t v___x_367_; 
v___x_360_ = l_Lean_OptionFlags_ofOptions(v___y_359_);
v___x_361_ = lean_st_ref_get(v___y_358_);
v_env_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc_ref(v_env_362_);
lean_dec(v___x_361_);
v___x_363_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_362_);
lean_dec_ref(v_env_362_);
v___x_364_ = 512;
v___x_365_ = lean_uint16_land(v___x_360_, v___x_364_);
v___x_366_ = 0;
v___x_367_ = lean_uint16_dec_eq(v___x_365_, v___x_366_);
if (v___x_367_ == 0)
{
if (v___x_363_ == 0)
{
v___y_329_ = v___x_360_;
v___y_330_ = v___y_357_;
v___y_331_ = v___y_356_;
v___y_332_ = v___x_253_;
v___y_333_ = v___y_359_;
v___y_334_ = v___y_358_;
goto v___jp_328_;
}
else
{
v___y_259_ = v___x_360_;
v___y_260_ = v___y_357_;
v___y_261_ = v___y_359_;
v___y_262_ = v___y_356_;
v___y_263_ = v___y_358_;
goto v___jp_258_;
}
}
else
{
if (v___x_363_ == 0)
{
v___y_259_ = v___x_360_;
v___y_260_ = v___y_357_;
v___y_261_ = v___y_359_;
v___y_262_ = v___y_356_;
v___y_263_ = v___y_358_;
goto v___jp_258_;
}
else
{
v___y_329_ = v___x_360_;
v___y_330_ = v___y_357_;
v___y_331_ = v___y_356_;
v___y_332_ = v___x_234_;
v___y_333_ = v___y_359_;
v___y_334_ = v___y_358_;
goto v___jp_328_;
}
}
}
v___jp_368_:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_383_ = l_Lean_maxRecDepth;
v___x_384_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18);
lean_inc(v_cancelTk_x3f_377_);
lean_inc(v_currMacroScope_376_);
lean_inc(v_quotContext_375_);
lean_inc(v_maxHeartbeats_374_);
lean_inc_ref(v_fileMap_370_);
lean_inc_ref(v_fileName_369_);
v___x_385_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_385_, 0, v_fileName_369_);
lean_ctor_set(v___x_385_, 1, v_fileMap_370_);
lean_ctor_set(v___x_385_, 2, v___x_238_);
lean_ctor_set(v___x_385_, 3, v___x_384_);
lean_ctor_set(v___x_385_, 4, v_currNamespace_371_);
lean_ctor_set(v___x_385_, 5, v_openDecls_372_);
lean_ctor_set(v___x_385_, 6, v_initHeartbeats_373_);
lean_ctor_set(v___x_385_, 7, v_maxHeartbeats_374_);
lean_ctor_set(v___x_385_, 8, v_quotContext_375_);
lean_ctor_set(v___x_385_, 9, v_currMacroScope_376_);
lean_ctor_set(v___x_385_, 10, v_cancelTk_x3f_377_);
lean_ctor_set(v___x_385_, 11, v_inheritedTraceOptions_378_);
lean_inc(v_ref_380_);
v___x_386_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v_currRecDepth_379_);
lean_ctor_set(v___x_386_, 2, v_ref_380_);
lean_ctor_set_uint16(v___x_386_, sizeof(void*)*3, v___x_245_);
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*3 + 2, v_suppressElabErrors_381_);
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*3 + 3, v_isRecordingDeps_382_);
lean_inc(v___x_257_);
v___y_356_ = v___x_386_;
v___y_357_ = v___x_383_;
v___y_358_ = v___x_257_;
v___y_359_ = v_options_230_;
goto v___jp_355_;
}
v___jp_390_:
{
lean_object* v___x_392_; lean_object* v_env_393_; lean_object* v_nextMacroScope_394_; lean_object* v_ngen_395_; lean_object* v_auxDeclNGen_396_; lean_object* v_traceState_397_; lean_object* v_recordedDeps_398_; lean_object* v_messages_399_; lean_object* v_infoState_400_; lean_object* v_snapshotTasks_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_410_; 
v___x_392_ = lean_st_ref_take(v___x_257_);
v_env_393_ = lean_ctor_get(v___x_392_, 0);
v_nextMacroScope_394_ = lean_ctor_get(v___x_392_, 1);
v_ngen_395_ = lean_ctor_get(v___x_392_, 2);
v_auxDeclNGen_396_ = lean_ctor_get(v___x_392_, 3);
v_traceState_397_ = lean_ctor_get(v___x_392_, 4);
v_recordedDeps_398_ = lean_ctor_get(v___x_392_, 6);
v_messages_399_ = lean_ctor_get(v___x_392_, 7);
v_infoState_400_ = lean_ctor_get(v___x_392_, 8);
v_snapshotTasks_401_ = lean_ctor_get(v___x_392_, 9);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v___x_392_, 5);
lean_dec(v_unused_411_);
v___x_403_ = v___x_392_;
v_isShared_404_ = v_isSharedCheck_410_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_snapshotTasks_401_);
lean_inc(v_infoState_400_);
lean_inc(v_messages_399_);
lean_inc(v_recordedDeps_398_);
lean_inc(v_traceState_397_);
lean_inc(v_auxDeclNGen_396_);
lean_inc(v_ngen_395_);
lean_inc(v_nextMacroScope_394_);
lean_inc(v_env_393_);
lean_dec(v___x_392_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_410_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = l_Lean_Kernel_enableDiag(v_env_393_, v___y_391_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 5, v___x_249_);
lean_ctor_set(v___x_403_, 0, v___x_405_);
v___x_407_ = v___x_403_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_nextMacroScope_394_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_ngen_395_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v_auxDeclNGen_396_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v_traceState_397_);
lean_ctor_set(v_reuseFailAlloc_409_, 5, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_409_, 6, v_recordedDeps_398_);
lean_ctor_set(v_reuseFailAlloc_409_, 7, v_messages_399_);
lean_ctor_set(v_reuseFailAlloc_409_, 8, v_infoState_400_);
lean_ctor_set(v_reuseFailAlloc_409_, 9, v_snapshotTasks_401_);
v___x_407_ = v_reuseFailAlloc_409_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_408_; 
v___x_408_ = lean_st_ref_put(v___x_257_, v___x_407_);
v_fileName_369_ = v___x_236_;
v_fileMap_370_ = v___x_237_;
v_currNamespace_371_ = v_currNamespace_231_;
v_openDecls_372_ = v_openDecls_232_;
v_initHeartbeats_373_ = v___x_256_;
v_maxHeartbeats_374_ = v___x_240_;
v_quotContext_375_ = v___x_241_;
v_currMacroScope_376_ = v___x_242_;
v_cancelTk_x3f_377_ = v___x_243_;
v_inheritedTraceOptions_378_ = v___x_388_;
v_currRecDepth_379_ = v___x_239_;
v_ref_380_ = v___x_244_;
v_suppressElabErrors_381_ = v___x_234_;
v_isRecordingDeps_382_ = v___x_234_;
goto v___jp_368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___boxed(lean_object* v_info_415_, lean_object* v_x_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_415_, v_x_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM(lean_object* v_00_u03b1_419_, lean_object* v_info_420_, lean_object* v_x_421_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_420_, v_x_421_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___boxed(lean_object* v_00_u03b1_424_, lean_object* v_info_425_, lean_object* v_x_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Elab_ContextInfo_runCoreM(v_00_u03b1_424_, v_info_425_, v_x_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(lean_object* v___x_429_, lean_object* v_x_430_, lean_object* v___x_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_st_mk_ref(v___x_429_);
lean_inc(v___x_435_);
v___x_436_ = lean_apply_5(v_x_430_, v___x_431_, v___x_435_, v___y_432_, v___y_433_, lean_box(0));
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_446_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_446_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_446_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_446_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_441_ = lean_st_ref_get(v___x_435_);
lean_dec(v___x_435_);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v_a_437_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_442_);
v___x_444_ = v___x_439_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec(v___x_435_);
v_a_447_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_436_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_436_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed(lean_object* v___x_455_, lean_object* v_x_456_, lean_object* v___x_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(v___x_455_, v_x_456_, v___x_457_, v___y_458_, v___y_459_);
return v_res_461_;
}
}
static uint64_t _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1(void){
_start:
{
lean_object* v___x_468_; uint64_t v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_469_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_468_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2(void){
_start:
{
uint64_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_uint64_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1);
v___x_471_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_472_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set_uint64(v___x_472_, sizeof(void*)*1, v___x_470_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_478_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
lean_ctor_set(v___x_478_, 2, v___x_477_);
lean_ctor_set(v___x_478_, 3, v___x_477_);
lean_ctor_set(v___x_478_, 4, v___x_477_);
lean_ctor_set(v___x_478_, 5, v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_unsigned_to_nat(32u);
v___x_480_ = lean_mk_empty_array_with_capacity(v___x_479_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7(void){
_start:
{
size_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_482_ = ((size_t)5ULL);
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = lean_unsigned_to_nat(32u);
v___x_485_ = lean_mk_empty_array_with_capacity(v___x_484_);
v___x_486_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6);
v___x_487_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v___x_485_);
lean_ctor_set(v___x_487_, 2, v___x_483_);
lean_ctor_set(v___x_487_, 3, v___x_483_);
lean_ctor_set_usize(v___x_487_, 4, v___x_482_);
return v___x_487_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
lean_ctor_set(v___x_489_, 2, v___x_488_);
lean_ctor_set(v___x_489_, 3, v___x_488_);
lean_ctor_set(v___x_489_, 4, v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object* v_info_490_, lean_object* v_lctx_491_, lean_object* v_x_492_){
_start:
{
lean_object* v___x_494_; uint8_t v___x_495_; uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v_toCommandContextInfo_502_; lean_object* v_mctx_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___f_508_; lean_object* v___x_509_; 
v___x_494_ = lean_box(1);
v___x_495_ = 0;
v___x_496_ = 1;
v___x_497_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2);
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3));
v___x_500_ = lean_box(0);
v___x_501_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_501_, 0, v___x_497_);
lean_ctor_set(v___x_501_, 1, v___x_494_);
lean_ctor_set(v___x_501_, 2, v_lctx_491_);
lean_ctor_set(v___x_501_, 3, v___x_499_);
lean_ctor_set(v___x_501_, 4, v___x_500_);
lean_ctor_set(v___x_501_, 5, v___x_498_);
lean_ctor_set(v___x_501_, 6, v___x_500_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*7, v___x_495_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*7 + 1, v___x_495_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*7 + 2, v___x_495_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*7 + 3, v___x_496_);
v_toCommandContextInfo_502_ = lean_ctor_get(v_info_490_, 0);
v_mctx_503_ = lean_ctor_get(v_toCommandContextInfo_502_, 3);
v___x_504_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_505_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7);
v___x_506_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8);
lean_inc_ref(v_mctx_503_);
v___x_507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_507_, 0, v_mctx_503_);
lean_ctor_set(v___x_507_, 1, v___x_504_);
lean_ctor_set(v___x_507_, 2, v___x_494_);
lean_ctor_set(v___x_507_, 3, v___x_505_);
lean_ctor_set(v___x_507_, 4, v___x_506_);
v___f_508_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_508_, 0, v___x_507_);
lean_closure_set(v___f_508_, 1, v_x_492_);
lean_closure_set(v___f_508_, 2, v___x_501_);
v___x_509_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_490_, v___f_508_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_518_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_518_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v_fst_514_; lean_object* v___x_516_; 
v_fst_514_ = lean_ctor_get(v_a_510_, 0);
lean_inc(v_fst_514_);
lean_dec(v_a_510_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v_fst_514_);
v___x_516_ = v___x_512_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_fst_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
v_a_519_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_509_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_509_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object* v_info_527_, lean_object* v_lctx_528_, lean_object* v_x_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_527_, v_lctx_528_, v_x_529_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object* v_00_u03b1_532_, lean_object* v_info_533_, lean_object* v_lctx_534_, lean_object* v_x_535_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_533_, v_lctx_534_, v_x_535_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object* v_00_u03b1_538_, lean_object* v_info_539_, lean_object* v_lctx_540_, lean_object* v_x_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Elab_ContextInfo_runMetaM(v_00_u03b1_538_, v_info_539_, v_lctx_540_, v_x_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object* v_info_544_, lean_object* v_lctx_545_){
_start:
{
lean_object* v_toCommandContextInfo_546_; lean_object* v_env_547_; lean_object* v_mctx_548_; lean_object* v_options_549_; lean_object* v_currNamespace_550_; lean_object* v_openDecls_551_; lean_object* v___x_552_; 
v_toCommandContextInfo_546_ = lean_ctor_get(v_info_544_, 0);
v_env_547_ = lean_ctor_get(v_toCommandContextInfo_546_, 0);
v_mctx_548_ = lean_ctor_get(v_toCommandContextInfo_546_, 3);
v_options_549_ = lean_ctor_get(v_toCommandContextInfo_546_, 4);
v_currNamespace_550_ = lean_ctor_get(v_toCommandContextInfo_546_, 5);
v_openDecls_551_ = lean_ctor_get(v_toCommandContextInfo_546_, 6);
lean_inc(v_openDecls_551_);
lean_inc(v_currNamespace_550_);
lean_inc_ref(v_options_549_);
lean_inc_ref(v_mctx_548_);
lean_inc_ref(v_env_547_);
v___x_552_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_552_, 0, v_env_547_);
lean_ctor_set(v___x_552_, 1, v_mctx_548_);
lean_ctor_set(v___x_552_, 2, v_lctx_545_);
lean_ctor_set(v___x_552_, 3, v_options_549_);
lean_ctor_set(v___x_552_, 4, v_currNamespace_550_);
lean_ctor_set(v___x_552_, 5, v_openDecls_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object* v_info_553_, lean_object* v_lctx_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_553_, v_lctx_554_);
lean_dec_ref(v_info_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object* v_info_556_, lean_object* v_lctx_557_, lean_object* v_stx_558_){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_560_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_556_, v_lctx_557_);
v___x_561_ = l_Lean_ppTerm(v___x_560_, v_stx_558_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object* v_info_563_, lean_object* v_lctx_564_, lean_object* v_stx_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Elab_ContextInfo_ppSyntax(v_info_563_, v_lctx_564_, v_stx_565_);
lean_dec_ref(v_info_563_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(lean_object* v_ctx_583_, lean_object* v_pos_584_, lean_object* v_info_585_){
_start:
{
lean_object* v_toCommandContextInfo_586_; lean_object* v_fileMap_587_; lean_object* v___x_588_; lean_object* v_line_589_; lean_object* v_column_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_613_; 
v_toCommandContextInfo_586_ = lean_ctor_get(v_ctx_583_, 0);
lean_inc_ref(v_toCommandContextInfo_586_);
lean_dec_ref(v_ctx_583_);
v_fileMap_587_ = lean_ctor_get(v_toCommandContextInfo_586_, 2);
lean_inc_ref(v_fileMap_587_);
lean_dec_ref(v_toCommandContextInfo_586_);
v___x_588_ = l_Lean_FileMap_toPosition(v_fileMap_587_, v_pos_584_);
v_line_589_ = lean_ctor_get(v___x_588_, 0);
v_column_590_ = lean_ctor_get(v___x_588_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_613_ == 0)
{
v___x_592_ = v___x_588_;
v_isShared_593_ = v_isSharedCheck_613_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_column_590_);
lean_inc(v_line_589_);
lean_dec(v___x_588_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_613_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_594_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_595_ = l_Nat_reprFast(v_line_589_);
v___x_596_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 5);
lean_ctor_set(v___x_592_, 1, v___x_596_);
lean_ctor_set(v___x_592_, 0, v___x_594_);
v___x_598_ = v___x_592_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v___x_596_);
v___x_598_ = v_reuseFailAlloc_612_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v_pos_605_; 
v___x_599_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
v___x_600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = l_Nat_reprFast(v_column_590_);
v___x_602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
v___x_603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_600_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v_pos_605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_pos_605_, 0, v___x_603_);
lean_ctor_set(v_pos_605_, 1, v___x_604_);
switch(lean_obj_tag(v_info_585_))
{
case 0:
{
return v_pos_605_;
}
case 1:
{
uint8_t v_canonical_609_; 
v_canonical_609_ = lean_ctor_get_uint8(v_info_585_, sizeof(void*)*2);
if (v_canonical_609_ == 1)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9));
v___x_611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_611_, 0, v_pos_605_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
return v___x_611_;
}
else
{
goto v___jp_606_;
}
}
default: 
{
goto v___jp_606_;
}
}
v___jp_606_:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7));
v___x_608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_608_, 0, v_pos_605_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
return v___x_608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(lean_object* v_ctx_614_, lean_object* v_pos_615_, lean_object* v_info_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_614_, v_pos_615_, v_info_616_);
lean_dec(v_info_616_);
lean_dec(v_pos_615_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(lean_object* v_ctx_621_, lean_object* v_stx_622_){
_start:
{
lean_object* v___y_624_; lean_object* v___y_625_; uint8_t v___x_633_; lean_object* v___y_635_; lean_object* v___x_638_; 
v___x_633_ = 0;
v___x_638_ = l_Lean_Syntax_getPos_x3f(v_stx_622_, v___x_633_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v___x_639_; 
v___x_639_ = lean_unsigned_to_nat(0u);
v___y_635_ = v___x_639_;
goto v___jp_634_;
}
else
{
lean_object* v_val_640_; 
v_val_640_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_val_640_);
lean_dec_ref_known(v___x_638_, 1);
v___y_635_ = v_val_640_;
goto v___jp_634_;
}
v___jp_623_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_626_ = l_Lean_Syntax_getHeadInfo(v_stx_622_);
lean_inc_ref(v_ctx_621_);
v___x_627_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_621_, v___y_624_, v___x_626_);
lean_dec(v___x_626_);
lean_dec(v___y_624_);
v___x_628_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = l_Lean_Syntax_getTailInfo(v_stx_622_);
v___x_631_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_621_, v___y_625_, v___x_630_);
lean_dec(v___x_630_);
lean_dec(v___y_625_);
v___x_632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_629_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
return v___x_632_;
}
v___jp_634_:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Syntax_getTailPos_x3f(v_stx_622_, v___x_633_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_inc(v___y_635_);
v___y_624_ = v___y_635_;
v___y_625_ = v___y_635_;
goto v___jp_623_;
}
else
{
lean_object* v_val_637_; 
v_val_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_val_637_);
lean_dec_ref_known(v___x_636_, 1);
v___y_624_ = v___y_635_;
v___y_625_ = v_val_637_;
goto v___jp_623_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(lean_object* v_ctx_641_, lean_object* v_stx_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_641_, v_stx_642_);
lean_dec(v_stx_642_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(lean_object* v_ctx_647_, lean_object* v_info_648_){
_start:
{
lean_object* v_elaborator_649_; lean_object* v_stx_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_665_; 
v_elaborator_649_ = lean_ctor_get(v_info_648_, 0);
v_stx_650_ = lean_ctor_get(v_info_648_, 1);
v_isSharedCheck_665_ = !lean_is_exclusive(v_info_648_);
if (v_isSharedCheck_665_ == 0)
{
v___x_652_ = v_info_648_;
v_isShared_653_ = v_isSharedCheck_665_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_stx_650_);
lean_inc(v_elaborator_649_);
lean_dec(v_info_648_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_665_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
uint8_t v___x_654_; 
v___x_654_ = l_Lean_Name_isAnonymous(v_elaborator_649_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_655_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_647_, v_stx_650_);
lean_dec(v_stx_650_);
v___x_656_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
if (v_isShared_653_ == 0)
{
lean_ctor_set_tag(v___x_652_, 5);
lean_ctor_set(v___x_652_, 1, v___x_656_);
lean_ctor_set(v___x_652_, 0, v___x_655_);
v___x_658_ = v___x_652_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_656_);
v___x_658_ = v_reuseFailAlloc_663_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
uint8_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_659_ = 1;
v___x_660_ = l_Lean_Name_toString(v_elaborator_649_, v___x_659_);
v___x_661_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
v___x_662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_658_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
return v___x_662_;
}
}
else
{
lean_object* v___x_664_; 
lean_del_object(v___x_652_);
lean_dec(v_elaborator_649_);
v___x_664_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_647_, v_stx_650_);
lean_dec(v_stx_650_);
return v___x_664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object* v_info_666_, lean_object* v_ctx_667_, lean_object* v_x_668_){
_start:
{
lean_object* v_lctx_670_; lean_object* v___x_671_; 
v_lctx_670_ = lean_ctor_get(v_info_666_, 1);
lean_inc_ref(v_lctx_670_);
lean_dec_ref(v_info_666_);
v___x_671_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_667_, v_lctx_670_, v_x_668_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(lean_object* v_info_672_, lean_object* v_ctx_673_, lean_object* v_x_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_672_, v_ctx_673_, v_x_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM(lean_object* v_00_u03b1_677_, lean_object* v_info_678_, lean_object* v_ctx_679_, lean_object* v_x_680_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_678_, v_ctx_679_, v_x_680_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___boxed(lean_object* v_00_u03b1_683_, lean_object* v_info_684_, lean_object* v_ctx_685_, lean_object* v_x_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_Elab_TermInfo_runMetaM(v_00_u03b1_683_, v_info_684_, v_ctx_685_, v_x_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0(lean_object* v_ctx_703_, lean_object* v_toElabInfo_704_, lean_object* v_expr_705_, uint8_t v_isBinder_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v_a_727_; lean_object* v___y_737_; lean_object* v_a_738_; lean_object* v___x_742_; 
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
lean_inc_ref(v_expr_705_);
v___x_742_ = lean_infer_type(v_expr_705_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_744_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
v___x_744_ = l_Lean_Meta_ppExpr(v_a_743_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 1);
v_a_727_ = v_a_745_;
goto v___jp_726_;
}
else
{
lean_object* v_a_746_; 
v_a_746_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_746_);
v___y_737_ = v___x_744_;
v_a_738_ = v_a_746_;
goto v___jp_736_;
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
v_a_747_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_742_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_742_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
lean_inc(v_a_747_);
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
v___y_737_ = v___x_752_;
v_a_738_ = v_a_747_;
goto v___jp_736_;
}
}
}
v___jp_712_:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
lean_inc_ref(v___y_715_);
v___x_716_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_716_, 0, v___y_715_);
v___x_717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_717_, 0, v___y_713_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v___y_714_);
v___x_721_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_703_, v_toElabInfo_704_);
v___x_724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
v___jp_726_:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_Meta_ppExpr(v_expr_705_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref_known(v___x_728_, 1);
v___x_730_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__3));
v___x_731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v_a_729_);
v___x_732_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
v___x_733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
if (v_isBinder_706_ == 0)
{
lean_object* v___x_734_; 
v___x_734_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__6));
v___y_713_ = v___x_733_;
v___y_714_ = v_a_727_;
v___y_715_ = v___x_734_;
goto v___jp_712_;
}
else
{
lean_object* v___x_735_; 
v___x_735_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__7));
v___y_713_ = v___x_733_;
v___y_714_ = v_a_727_;
v___y_715_ = v___x_735_;
goto v___jp_712_;
}
}
else
{
lean_dec(v_a_727_);
lean_dec_ref(v_toElabInfo_704_);
lean_dec_ref(v_ctx_703_);
return v___x_728_;
}
}
v___jp_736_:
{
uint8_t v___x_739_; 
v___x_739_ = l_Lean_Exception_isInterrupt(v_a_738_);
if (v___x_739_ == 0)
{
uint8_t v___x_740_; 
v___x_740_ = l_Lean_Exception_isRuntime(v_a_738_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
lean_dec_ref(v___y_737_);
v___x_741_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__9));
v_a_727_ = v___x_741_;
goto v___jp_726_;
}
else
{
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec_ref(v_expr_705_);
lean_dec_ref(v_toElabInfo_704_);
lean_dec_ref(v_ctx_703_);
return v___y_737_;
}
}
else
{
lean_dec_ref(v_a_738_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec_ref(v_expr_705_);
lean_dec_ref(v_toElabInfo_704_);
lean_dec_ref(v_ctx_703_);
return v___y_737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0___boxed(lean_object* v_ctx_755_, lean_object* v_toElabInfo_756_, lean_object* v_expr_757_, lean_object* v_isBinder_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
uint8_t v_isBinder_boxed_764_; lean_object* v_res_765_; 
v_isBinder_boxed_764_ = lean_unbox(v_isBinder_758_);
v_res_765_ = l_Lean_Elab_TermInfo_format___lam__0(v_ctx_755_, v_toElabInfo_756_, v_expr_757_, v_isBinder_boxed_764_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format(lean_object* v_ctx_766_, lean_object* v_info_767_){
_start:
{
lean_object* v_toElabInfo_769_; lean_object* v_expr_770_; uint8_t v_isBinder_771_; lean_object* v___x_772_; lean_object* v___f_773_; lean_object* v___x_774_; 
v_toElabInfo_769_ = lean_ctor_get(v_info_767_, 0);
v_expr_770_ = lean_ctor_get(v_info_767_, 3);
v_isBinder_771_ = lean_ctor_get_uint8(v_info_767_, sizeof(void*)*4);
v___x_772_ = lean_box(v_isBinder_771_);
lean_inc_ref(v_expr_770_);
lean_inc_ref(v_toElabInfo_769_);
lean_inc_ref(v_ctx_766_);
v___f_773_ = lean_alloc_closure((void*)(l_Lean_Elab_TermInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_773_, 0, v_ctx_766_);
lean_closure_set(v___f_773_, 1, v_toElabInfo_769_);
lean_closure_set(v___f_773_, 2, v_expr_770_);
lean_closure_set(v___f_773_, 3, v___x_772_);
v___x_774_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_767_, v_ctx_766_, v___f_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___boxed(lean_object* v_ctx_775_, lean_object* v_info_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_Elab_TermInfo_format(v_ctx_775_, v_info_776_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialTermInfo_format(lean_object* v_ctx_782_, lean_object* v_info_783_){
_start:
{
lean_object* v_toElabInfo_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_toElabInfo_784_ = lean_ctor_get(v_info_783_, 0);
lean_inc_ref(v_toElabInfo_784_);
lean_dec_ref(v_info_783_);
v___x_785_ = ((lean_object*)(l_Lean_Elab_PartialTermInfo_format___closed__1));
v___x_786_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_782_, v_toElabInfo_784_);
v___x_787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(lean_object* v_x_794_){
_start:
{
if (lean_obj_tag(v_x_794_) == 0)
{
lean_object* v___x_795_; 
v___x_795_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_795_;
}
else
{
lean_object* v_val_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_806_; 
v_val_796_ = lean_ctor_get(v_x_794_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v_x_794_);
if (v_isSharedCheck_806_ == 0)
{
v___x_798_ = v_x_794_;
v_isShared_799_ = v_isSharedCheck_806_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_val_796_);
lean_dec(v_x_794_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_806_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_800_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_801_ = lean_expr_dbg_to_string(v_val_796_);
lean_dec(v_val_796_);
if (v_isShared_799_ == 0)
{
lean_ctor_set_tag(v___x_798_, 3);
lean_ctor_set(v___x_798_, 0, v___x_801_);
v___x_803_ = v___x_798_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_805_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_804_; 
v___x_804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_800_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
return v___x_804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0(lean_object* v_ctx_813_, lean_object* v_lctx_814_, lean_object* v_stx_815_, lean_object* v_expectedType_x3f_816_, lean_object* v_info_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___x_823_; lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_842_; 
v___x_823_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_813_, v_lctx_814_, v_stx_815_);
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_842_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_842_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_842_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_828_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__1));
v___x_829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v_a_824_);
v___x_830_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_831_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_816_);
v___x_833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_831_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = l_Lean_Elab_CompletionInfo_stx(v_info_817_);
v___x_837_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_813_, v___x_836_);
lean_dec(v___x_836_);
v___x_838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_835_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_838_);
v___x_840_ = v___x_826_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___boxed(lean_object* v_ctx_843_, lean_object* v_lctx_844_, lean_object* v_stx_845_, lean_object* v_expectedType_x3f_846_, lean_object* v_info_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_Elab_CompletionInfo_format___lam__0(v_ctx_843_, v_lctx_844_, v_stx_845_, v_expectedType_x3f_846_, v_info_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec_ref(v_info_847_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format(lean_object* v_ctx_860_, lean_object* v_info_861_){
_start:
{
switch(lean_obj_tag(v_info_861_))
{
case 0:
{
lean_object* v_termInfo_863_; lean_object* v_expectedType_x3f_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_885_; 
v_termInfo_863_ = lean_ctor_get(v_info_861_, 0);
v_expectedType_x3f_864_ = lean_ctor_get(v_info_861_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v_info_861_);
if (v_isSharedCheck_885_ == 0)
{
v___x_866_ = v_info_861_;
v_isShared_867_ = v_isSharedCheck_885_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_expectedType_x3f_864_);
lean_inc(v_termInfo_863_);
lean_dec(v_info_861_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_885_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_Elab_TermInfo_format(v_ctx_860_, v_termInfo_863_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_884_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_884_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_884_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_884_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__1));
if (v_isShared_867_ == 0)
{
lean_ctor_set_tag(v___x_866_, 5);
lean_ctor_set(v___x_866_, 1, v_a_869_);
lean_ctor_set(v___x_866_, 0, v___x_873_);
v___x_875_ = v___x_866_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_a_869_);
v___x_875_ = v_reuseFailAlloc_883_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_876_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_875_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_864_);
v___x_879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_879_);
v___x_881_ = v___x_871_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
else
{
lean_del_object(v___x_866_);
lean_dec(v_expectedType_x3f_864_);
return v___x_868_;
}
}
}
case 1:
{
lean_object* v_stx_886_; lean_object* v_lctx_887_; lean_object* v_expectedType_x3f_888_; lean_object* v___f_889_; lean_object* v___x_890_; 
v_stx_886_ = lean_ctor_get(v_info_861_, 0);
lean_inc(v_stx_886_);
v_lctx_887_ = lean_ctor_get(v_info_861_, 2);
lean_inc_ref_n(v_lctx_887_, 2);
v_expectedType_x3f_888_ = lean_ctor_get(v_info_861_, 3);
lean_inc(v_expectedType_x3f_888_);
lean_inc_ref(v_ctx_860_);
v___f_889_ = lean_alloc_closure((void*)(l_Lean_Elab_CompletionInfo_format___lam__0___boxed), 10, 5);
lean_closure_set(v___f_889_, 0, v_ctx_860_);
lean_closure_set(v___f_889_, 1, v_lctx_887_);
lean_closure_set(v___f_889_, 2, v_stx_886_);
lean_closure_set(v___f_889_, 3, v_expectedType_x3f_888_);
lean_closure_set(v___f_889_, 4, v_info_861_);
v___x_890_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_860_, v_lctx_887_, v___f_889_);
return v___x_890_;
}
default: 
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_891_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__3));
v___x_892_ = l_Lean_Elab_CompletionInfo_stx(v_info_861_);
lean_dec_ref(v_info_861_);
v___x_893_ = lean_box(0);
v___x_894_ = 0;
lean_inc(v___x_892_);
v___x_895_ = l_Lean_Syntax_formatStx(v___x_892_, v___x_893_, v___x_894_);
v___x_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_891_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_860_, v___x_892_);
lean_dec(v___x_892_);
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___boxed(lean_object* v_ctx_902_, lean_object* v_info_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_Elab_CompletionInfo_format(v_ctx_902_, v_info_903_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format(lean_object* v_ctx_909_, lean_object* v_info_910_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_912_ = ((lean_object*)(l_Lean_Elab_CommandInfo_format___closed__1));
v___x_913_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_909_, v_info_910_);
v___x_914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_912_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format___boxed(lean_object* v_ctx_916_, lean_object* v_info_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Elab_CommandInfo_format(v_ctx_916_, v_info_917_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format(lean_object* v_ctx_923_, lean_object* v_info_924_){
_start:
{
lean_object* v_stx_926_; lean_object* v_optionName_927_; lean_object* v___x_928_; uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_stx_926_ = lean_ctor_get(v_info_924_, 0);
lean_inc(v_stx_926_);
v_optionName_927_ = lean_ctor_get(v_info_924_, 1);
lean_inc(v_optionName_927_);
lean_dec_ref(v_info_924_);
v___x_928_ = ((lean_object*)(l_Lean_Elab_OptionInfo_format___closed__1));
v___x_929_ = 1;
v___x_930_ = l_Lean_Name_toString(v_optionName_927_, v___x_929_);
v___x_931_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
v___x_932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_928_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_932_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_923_, v_stx_926_);
lean_dec(v_stx_926_);
v___x_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format___boxed(lean_object* v_ctx_938_, lean_object* v_info_939_, lean_object* v_a_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_Elab_OptionInfo_format(v_ctx_938_, v_info_939_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format(lean_object* v_ctx_945_, lean_object* v_info_946_){
_start:
{
lean_object* v_stx_948_; lean_object* v_errorName_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_965_; 
v_stx_948_ = lean_ctor_get(v_info_946_, 0);
v_errorName_949_ = lean_ctor_get(v_info_946_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_info_946_);
if (v_isSharedCheck_965_ == 0)
{
v___x_951_ = v_info_946_;
v_isShared_952_ = v_isSharedCheck_965_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_errorName_949_);
lean_inc(v_stx_948_);
lean_dec(v_info_946_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_965_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_953_; uint8_t v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_953_ = ((lean_object*)(l_Lean_Elab_ErrorNameInfo_format___closed__1));
v___x_954_ = 1;
v___x_955_ = l_Lean_Name_toString(v_errorName_949_, v___x_954_);
v___x_956_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
if (v_isShared_952_ == 0)
{
lean_ctor_set_tag(v___x_951_, 5);
lean_ctor_set(v___x_951_, 1, v___x_956_);
lean_ctor_set(v___x_951_, 0, v___x_953_);
v___x_958_ = v___x_951_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v___x_956_);
v___x_958_ = v_reuseFailAlloc_964_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_959_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_958_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_945_, v_stx_948_);
lean_dec(v_stx_948_);
v___x_962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
return v___x_963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format___boxed(lean_object* v_ctx_966_, lean_object* v_info_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_966_, v_info_967_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0(lean_object* v_val_976_, lean_object* v_fieldName_977_, lean_object* v_ctx_978_, lean_object* v_stx_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v___x_985_; 
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
lean_inc_ref(v_val_976_);
v___x_985_ = lean_infer_type(v_val_976_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_987_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_985_, 1);
v___x_987_ = l_Lean_Meta_ppExpr(v_a_986_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1018_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_1018_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1018_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_Meta_ppExpr(v_val_976_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1017_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1017_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1017_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_997_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__1));
v___x_998_ = 1;
v___x_999_ = l_Lean_Name_toString(v_fieldName_977_, v___x_998_);
if (v_isShared_991_ == 0)
{
lean_ctor_set_tag(v___x_990_, 3);
lean_ctor_set(v___x_990_, 0, v___x_999_);
v___x_1001_ = v___x_990_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_997_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v_a_988_);
v___x_1006_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__3));
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v_a_993_);
v___x_1009_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_978_, v_stx_979_);
v___x_1012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1012_);
v___x_1014_ = v___x_995_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
else
{
lean_del_object(v___x_990_);
lean_dec(v_a_988_);
lean_dec_ref(v_ctx_978_);
lean_dec(v_fieldName_977_);
return v___x_992_;
}
}
}
else
{
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec_ref(v_ctx_978_);
lean_dec(v_fieldName_977_);
lean_dec_ref(v_val_976_);
return v___x_987_;
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec_ref(v_ctx_978_);
lean_dec(v_fieldName_977_);
lean_dec_ref(v_val_976_);
v_a_1019_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_985_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_985_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0___boxed(lean_object* v_val_1027_, lean_object* v_fieldName_1028_, lean_object* v_ctx_1029_, lean_object* v_stx_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_Elab_FieldInfo_format___lam__0(v_val_1027_, v_fieldName_1028_, v_ctx_1029_, v_stx_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v_stx_1030_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format(lean_object* v_ctx_1037_, lean_object* v_info_1038_){
_start:
{
lean_object* v_fieldName_1040_; lean_object* v_lctx_1041_; lean_object* v_val_1042_; lean_object* v_stx_1043_; lean_object* v___f_1044_; lean_object* v___x_1045_; 
v_fieldName_1040_ = lean_ctor_get(v_info_1038_, 1);
lean_inc(v_fieldName_1040_);
v_lctx_1041_ = lean_ctor_get(v_info_1038_, 2);
lean_inc_ref(v_lctx_1041_);
v_val_1042_ = lean_ctor_get(v_info_1038_, 3);
lean_inc_ref(v_val_1042_);
v_stx_1043_ = lean_ctor_get(v_info_1038_, 4);
lean_inc(v_stx_1043_);
lean_dec_ref(v_info_1038_);
lean_inc_ref(v_ctx_1037_);
v___f_1044_ = lean_alloc_closure((void*)(l_Lean_Elab_FieldInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1044_, 0, v_val_1042_);
lean_closure_set(v___f_1044_, 1, v_fieldName_1040_);
lean_closure_set(v___f_1044_, 2, v_ctx_1037_);
lean_closure_set(v___f_1044_, 3, v_stx_1043_);
v___x_1045_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1037_, v_lctx_1041_, v___f_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___boxed(lean_object* v_ctx_1046_, lean_object* v_info_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_Elab_FieldInfo_format(v_ctx_1046_, v_info_1047_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(lean_object* v_pre_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_){
_start:
{
if (lean_obj_tag(v_x_1052_) == 0)
{
lean_dec(v_pre_1050_);
return v_x_1051_;
}
else
{
lean_object* v_head_1053_; lean_object* v_tail_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1063_; 
v_head_1053_ = lean_ctor_get(v_x_1052_, 0);
v_tail_1054_ = lean_ctor_get(v_x_1052_, 1);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_x_1052_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1056_ = v_x_1052_;
v_isShared_1057_ = v_isSharedCheck_1063_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_tail_1054_);
lean_inc(v_head_1053_);
lean_dec(v_x_1052_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1063_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
lean_inc(v_pre_1050_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set_tag(v___x_1056_, 5);
lean_ctor_set(v___x_1056_, 1, v_pre_1050_);
lean_ctor_set(v___x_1056_, 0, v_x_1051_);
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_x_1051_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_pre_1050_);
v___x_1059_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v_head_1053_);
v_x_1051_ = v___x_1060_;
v_x_1052_ = v_tail_1054_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(lean_object* v_pre_1064_, lean_object* v_x_1065_){
_start:
{
if (lean_obj_tag(v_x_1065_) == 0)
{
lean_object* v___x_1066_; 
lean_dec(v_pre_1064_);
v___x_1066_ = lean_box(0);
return v___x_1066_;
}
else
{
lean_object* v_head_1067_; lean_object* v_tail_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1076_; 
v_head_1067_ = lean_ctor_get(v_x_1065_, 0);
v_tail_1068_ = lean_ctor_get(v_x_1065_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_x_1065_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1070_ = v_x_1065_;
v_isShared_1071_ = v_isSharedCheck_1076_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_tail_1068_);
lean_inc(v_head_1067_);
lean_dec(v_x_1065_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1076_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
lean_inc(v_pre_1064_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 5);
lean_ctor_set(v___x_1070_, 1, v_head_1067_);
lean_ctor_set(v___x_1070_, 0, v_pre_1064_);
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_pre_1064_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_head_1067_);
v___x_1073_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(v_pre_1064_, v___x_1073_, v_tail_1068_);
return v___x_1074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(lean_object* v_x_1077_, lean_object* v_x_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
if (lean_obj_tag(v_x_1077_) == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = l_List_reverse___redArg(v_x_1078_);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
else
{
lean_object* v_head_1086_; lean_object* v_tail_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1105_; 
v_head_1086_ = lean_ctor_get(v_x_1077_, 0);
v_tail_1087_ = lean_ctor_get(v_x_1077_, 1);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_x_1077_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1089_ = v_x_1077_;
v_isShared_1090_ = v_isSharedCheck_1105_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_tail_1087_);
lean_inc(v_head_1086_);
lean_dec(v_x_1077_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1105_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_Meta_ppGoal(v_head_1086_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v_head_1086_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1091_, 1);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 1, v_x_1078_);
lean_ctor_set(v___x_1089_, 0, v_a_1092_);
v___x_1094_ = v___x_1089_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1092_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_x_1078_);
v___x_1094_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
v_x_1077_ = v_tail_1087_;
v_x_1078_ = v___x_1094_;
goto _start;
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_del_object(v___x_1089_);
lean_dec(v_tail_1087_);
lean_dec(v_x_1078_);
v_a_1097_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1091_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1091_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(lean_object* v_x_1106_, lean_object* v_x_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_x_1106_, v_x_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0(lean_object* v_goals_1117_, lean_object* v___x_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_goals_1117_, v___x_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1134_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1134_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1134_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1129_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1130_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1129_, v_a_1125_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1130_);
v___x_1132_ = v___x_1127_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
v_a_1135_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1124_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1124_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(lean_object* v_goals_1143_, lean_object* v___x_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0(v_goals_1143_, v___x_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
return v_res_1150_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
return v___x_1152_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1153_ = lean_unsigned_to_nat(32u);
v___x_1154_ = lean_mk_empty_array_with_capacity(v___x_1153_);
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
return v___x_1155_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2(void){
_start:
{
size_t v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1156_ = ((size_t)5ULL);
v___x_1157_ = lean_unsigned_to_nat(0u);
v___x_1158_ = lean_unsigned_to_nat(32u);
v___x_1159_ = lean_mk_empty_array_with_capacity(v___x_1158_);
v___x_1160_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__1, &l_Lean_Elab_ContextInfo_ppGoals___closed__1_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1);
v___x_1161_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v___x_1159_);
lean_ctor_set(v___x_1161_, 2, v___x_1157_);
lean_ctor_set(v___x_1161_, 3, v___x_1157_);
lean_ctor_set_usize(v___x_1161_, 4, v___x_1156_);
return v___x_1161_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1162_ = lean_box(1);
v___x_1163_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_1164_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__0, &l_Lean_Elab_ContextInfo_ppGoals___closed__0_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0);
v___x_1165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v___x_1163_);
lean_ctor_set(v___x_1165_, 2, v___x_1162_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object* v_ctx_1169_, lean_object* v_goals_1170_){
_start:
{
uint8_t v___x_1172_; 
v___x_1172_ = l_List_isEmpty___redArg(v_goals_1170_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___f_1175_; lean_object* v___x_1176_; 
v___x_1173_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_1174_ = lean_box(0);
v___f_1175_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1175_, 0, v_goals_1170_);
lean_closure_set(v___f_1175_, 1, v___x_1174_);
v___x_1176_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1169_, v___x_1173_, v___f_1175_);
return v___x_1176_;
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec(v_goals_1170_);
lean_dec_ref(v_ctx_1169_);
v___x_1177_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___closed__5));
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object* v_ctx_1179_, lean_object* v_goals_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctx_1179_, v_goals_1180_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format(lean_object* v_ctx_1192_, lean_object* v_info_1193_){
_start:
{
lean_object* v_toCommandContextInfo_1195_; lean_object* v_parentDecl_x3f_1196_; lean_object* v_autoImplicits_1197_; lean_object* v_env_1198_; lean_object* v_cmdEnv_x3f_1199_; lean_object* v_fileMap_1200_; lean_object* v_options_1201_; lean_object* v_currNamespace_1202_; lean_object* v_openDecls_1203_; lean_object* v_ngen_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1246_; 
v_toCommandContextInfo_1195_ = lean_ctor_get(v_ctx_1192_, 0);
lean_inc_ref(v_toCommandContextInfo_1195_);
v_parentDecl_x3f_1196_ = lean_ctor_get(v_ctx_1192_, 1);
v_autoImplicits_1197_ = lean_ctor_get(v_ctx_1192_, 2);
v_env_1198_ = lean_ctor_get(v_toCommandContextInfo_1195_, 0);
v_cmdEnv_x3f_1199_ = lean_ctor_get(v_toCommandContextInfo_1195_, 1);
v_fileMap_1200_ = lean_ctor_get(v_toCommandContextInfo_1195_, 2);
v_options_1201_ = lean_ctor_get(v_toCommandContextInfo_1195_, 4);
v_currNamespace_1202_ = lean_ctor_get(v_toCommandContextInfo_1195_, 5);
v_openDecls_1203_ = lean_ctor_get(v_toCommandContextInfo_1195_, 6);
v_ngen_1204_ = lean_ctor_get(v_toCommandContextInfo_1195_, 7);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_toCommandContextInfo_1195_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v_toCommandContextInfo_1195_, 3);
lean_dec(v_unused_1247_);
v___x_1206_ = v_toCommandContextInfo_1195_;
v_isShared_1207_ = v_isSharedCheck_1246_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_ngen_1204_);
lean_inc(v_openDecls_1203_);
lean_inc(v_currNamespace_1202_);
lean_inc(v_options_1201_);
lean_inc(v_fileMap_1200_);
lean_inc(v_cmdEnv_x3f_1199_);
lean_inc(v_env_1198_);
lean_dec(v_toCommandContextInfo_1195_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1246_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v_toElabInfo_1208_; lean_object* v_mctxBefore_1209_; lean_object* v_goalsBefore_1210_; lean_object* v_mctxAfter_1211_; lean_object* v_goalsAfter_1212_; lean_object* v___x_1214_; 
v_toElabInfo_1208_ = lean_ctor_get(v_info_1193_, 0);
lean_inc_ref(v_toElabInfo_1208_);
v_mctxBefore_1209_ = lean_ctor_get(v_info_1193_, 1);
lean_inc_ref(v_mctxBefore_1209_);
v_goalsBefore_1210_ = lean_ctor_get(v_info_1193_, 2);
lean_inc(v_goalsBefore_1210_);
v_mctxAfter_1211_ = lean_ctor_get(v_info_1193_, 3);
lean_inc_ref(v_mctxAfter_1211_);
v_goalsAfter_1212_ = lean_ctor_get(v_info_1193_, 4);
lean_inc(v_goalsAfter_1212_);
lean_dec_ref(v_info_1193_);
lean_inc_ref(v_ngen_1204_);
lean_inc(v_openDecls_1203_);
lean_inc(v_currNamespace_1202_);
lean_inc_ref(v_options_1201_);
lean_inc_ref(v_fileMap_1200_);
lean_inc(v_cmdEnv_x3f_1199_);
lean_inc_ref(v_env_1198_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 3, v_mctxBefore_1209_);
v___x_1214_ = v___x_1206_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_env_1198_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_cmdEnv_x3f_1199_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_fileMap_1200_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v_mctxBefore_1209_);
lean_ctor_set(v_reuseFailAlloc_1245_, 4, v_options_1201_);
lean_ctor_set(v_reuseFailAlloc_1245_, 5, v_currNamespace_1202_);
lean_ctor_set(v_reuseFailAlloc_1245_, 6, v_openDecls_1203_);
lean_ctor_set(v_reuseFailAlloc_1245_, 7, v_ngen_1204_);
v___x_1214_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v_ctxB_1215_; lean_object* v___x_1216_; lean_object* v_ctxA_1217_; lean_object* v___x_1218_; 
lean_inc_ref_n(v_autoImplicits_1197_, 2);
lean_inc_n(v_parentDecl_x3f_1196_, 2);
v_ctxB_1215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxB_1215_, 0, v___x_1214_);
lean_ctor_set(v_ctxB_1215_, 1, v_parentDecl_x3f_1196_);
lean_ctor_set(v_ctxB_1215_, 2, v_autoImplicits_1197_);
v___x_1216_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1216_, 0, v_env_1198_);
lean_ctor_set(v___x_1216_, 1, v_cmdEnv_x3f_1199_);
lean_ctor_set(v___x_1216_, 2, v_fileMap_1200_);
lean_ctor_set(v___x_1216_, 3, v_mctxAfter_1211_);
lean_ctor_set(v___x_1216_, 4, v_options_1201_);
lean_ctor_set(v___x_1216_, 5, v_currNamespace_1202_);
lean_ctor_set(v___x_1216_, 6, v_openDecls_1203_);
lean_ctor_set(v___x_1216_, 7, v_ngen_1204_);
v_ctxA_1217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxA_1217_, 0, v___x_1216_);
lean_ctor_set(v_ctxA_1217_, 1, v_parentDecl_x3f_1196_);
lean_ctor_set(v_ctxA_1217_, 2, v_autoImplicits_1197_);
v___x_1218_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxB_1215_, v_goalsBefore_1210_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1220_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1218_, 1);
v___x_1220_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxA_1217_, v_goalsAfter_1212_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1244_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1244_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1244_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v_stx_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
v_stx_1225_ = lean_ctor_get(v_toElabInfo_1208_, 1);
lean_inc(v_stx_1225_);
v___x_1226_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__1));
v___x_1227_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1192_, v_toElabInfo_1208_);
v___x_1228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1226_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1228_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___x_1231_ = lean_box(0);
v___x_1232_ = 0;
v___x_1233_ = l_Lean_Syntax_formatStx(v_stx_1225_, v___x_1231_, v___x_1232_);
v___x_1234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1230_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__3));
v___x_1236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
v___x_1237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
lean_ctor_set(v___x_1237_, 1, v_a_1219_);
v___x_1238_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__5));
v___x_1239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v_a_1221_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1240_);
v___x_1242_ = v___x_1223_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
else
{
lean_dec(v_a_1219_);
lean_dec_ref(v_toElabInfo_1208_);
lean_dec_ref(v_ctx_1192_);
return v___x_1220_;
}
}
else
{
lean_dec_ref_known(v_ctxA_1217_, 3);
lean_dec(v_goalsAfter_1212_);
lean_dec_ref(v_toElabInfo_1208_);
lean_dec_ref(v_ctx_1192_);
return v___x_1218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format___boxed(lean_object* v_ctx_1248_, lean_object* v_info_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Elab_TacticInfo_format(v_ctx_1248_, v_info_1249_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object* v_ctx_1258_, lean_object* v_info_1259_){
_start:
{
lean_object* v_lctx_1261_; lean_object* v_stx_1262_; lean_object* v_output_1263_; lean_object* v___x_1264_; lean_object* v_a_1265_; lean_object* v___x_1266_; lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1279_; 
v_lctx_1261_ = lean_ctor_get(v_info_1259_, 0);
lean_inc_ref_n(v_lctx_1261_, 2);
v_stx_1262_ = lean_ctor_get(v_info_1259_, 1);
lean_inc(v_stx_1262_);
v_output_1263_ = lean_ctor_get(v_info_1259_, 2);
lean_inc(v_output_1263_);
lean_dec_ref(v_info_1259_);
v___x_1264_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1258_, v_lctx_1261_, v_stx_1262_);
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref(v___x_1264_);
v___x_1266_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1258_, v_lctx_1261_, v_output_1263_);
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1279_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1279_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1271_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__1));
v___x_1272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v_a_1265_);
v___x_1273_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__3));
v___x_1274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1272_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
lean_ctor_set(v___x_1275_, 1, v_a_1267_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1275_);
v___x_1277_ = v___x_1269_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object* v_ctx_1280_, lean_object* v_info_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1280_, v_info_1281_);
lean_dec_ref(v_ctx_1280_);
return v_res_1283_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__0(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
return v___x_1285_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__1(void){
_start:
{
uint8_t v___x_1286_; size_t v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1286_ = 1;
v___x_1287_ = ((size_t)0ULL);
v___x_1288_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__0, &l_Lean_Elab_UserWidgetInfo_format___closed__0_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__0);
v___x_1289_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
lean_ctor_set_usize(v___x_1289_, 2, v___x_1287_);
lean_ctor_set_uint8(v___x_1289_, sizeof(void*)*3, v___x_1286_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_UserWidgetInfo_format(lean_object* v_info_1293_){
_start:
{
lean_object* v_toWidgetInstance_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1323_; 
v_toWidgetInstance_1294_ = lean_ctor_get(v_info_1293_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_info_1293_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; 
v_unused_1324_ = lean_ctor_get(v_info_1293_, 1);
lean_dec(v_unused_1324_);
v___x_1296_ = v_info_1293_;
v_isShared_1297_ = v_isSharedCheck_1323_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_toWidgetInstance_1294_);
lean_dec(v_info_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1323_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v_id_1298_; lean_object* v_props_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v_fst_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1321_; 
v_id_1298_ = lean_ctor_get(v_toWidgetInstance_1294_, 0);
lean_inc(v_id_1298_);
v_props_1299_ = lean_ctor_get(v_toWidgetInstance_1294_, 1);
lean_inc_ref(v_props_1299_);
lean_dec_ref(v_toWidgetInstance_1294_);
v___x_1300_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__1, &l_Lean_Elab_UserWidgetInfo_format___closed__1_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__1);
v___x_1301_ = lean_apply_1(v_props_1299_, v___x_1300_);
v_fst_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; 
v_unused_1322_ = lean_ctor_get(v___x_1301_, 1);
lean_dec(v_unused_1322_);
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1321_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_fst_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1321_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1306_; uint8_t v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1306_ = ((lean_object*)(l_Lean_Elab_UserWidgetInfo_format___closed__3));
v___x_1307_ = 1;
v___x_1308_ = l_Lean_Name_toString(v_id_1298_, v___x_1307_);
v___x_1309_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set_tag(v___x_1304_, 5);
lean_ctor_set(v___x_1304_, 1, v___x_1309_);
lean_ctor_set(v___x_1304_, 0, v___x_1306_);
v___x_1311_ = v___x_1304_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
if (v_isShared_1297_ == 0)
{
lean_ctor_set_tag(v___x_1296_, 5);
lean_ctor_set(v___x_1296_, 1, v___x_1312_);
lean_ctor_set(v___x_1296_, 0, v___x_1311_);
v___x_1314_ = v___x_1296_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1315_ = lean_unsigned_to_nat(80u);
v___x_1316_ = l_Lean_Json_pretty(v_fst_1302_, v___x_1315_);
v___x_1317_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
v___x_1318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1314_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
return v___x_1318_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FVarAliasInfo_format(lean_object* v_info_1331_){
_start:
{
lean_object* v_userName_1332_; lean_object* v_id_1333_; lean_object* v_baseId_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v_userName_1332_ = lean_ctor_get(v_info_1331_, 0);
lean_inc(v_userName_1332_);
v_id_1333_ = lean_ctor_get(v_info_1331_, 1);
lean_inc(v_id_1333_);
v_baseId_1334_ = lean_ctor_get(v_info_1331_, 2);
lean_inc(v_baseId_1334_);
lean_dec_ref(v_info_1331_);
v___x_1335_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__1));
v___x_1336_ = l_Lean_Name_eraseMacroScopes(v_userName_1332_);
lean_dec(v_userName_1332_);
v___x_1337_ = 1;
v___x_1338_ = l_Lean_Name_toString(v___x_1336_, v___x_1337_);
v___x_1339_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
v___x_1340_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1335_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_1342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1340_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = l_Lean_Name_toString(v_id_1333_, v___x_1337_);
v___x_1344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
v___x_1345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1342_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
v___x_1346_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__3));
v___x_1347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1345_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = l_Lean_Name_toString(v_baseId_1334_, v___x_1337_);
v___x_1349_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
v___x_1350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1347_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format(lean_object* v_ctx_1354_, lean_object* v_info_1355_){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = ((lean_object*)(l_Lean_Elab_FieldRedeclInfo_format___closed__1));
v___x_1357_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1354_, v_info_1355_);
v___x_1358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1356_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format___boxed(lean_object* v_ctx_1359_, lean_object* v_info_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1359_, v_info_1360_);
lean_dec(v_info_1360_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f(lean_object* v_ppCtx_1364_, lean_object* v_info_1365_){
_start:
{
lean_object* v_mkDocString_x3f_1367_; 
v_mkDocString_x3f_1367_ = lean_ctor_get(v_info_1365_, 2);
lean_inc(v_mkDocString_x3f_1367_);
lean_dec_ref(v_info_1365_);
if (lean_obj_tag(v_mkDocString_x3f_1367_) == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec_ref(v_ppCtx_1364_);
v___x_1368_ = lean_box(0);
v___x_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
return v___x_1369_;
}
else
{
lean_object* v_val_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1402_; 
v_val_1370_ = lean_ctor_get(v_mkDocString_x3f_1367_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_mkDocString_x3f_1367_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1372_ = v_mkDocString_x3f_1367_;
v_isShared_1373_ = v_isSharedCheck_1402_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_val_1370_);
lean_dec(v_mkDocString_x3f_1367_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1402_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_apply_2(v_val_1370_, v_ppCtx_1364_, lean_box(0));
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1385_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1377_ = v___x_1374_;
v_isShared_1378_ = v_isSharedCheck_1385_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1374_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1385_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v_a_1375_);
v___x_1380_ = v___x_1372_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1382_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1380_);
v___x_1382_ = v___x_1377_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1401_; 
v_a_1386_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1388_ = v___x_1374_;
v_isShared_1389_ = v_isSharedCheck_1401_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1374_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1401_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1390_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0));
v___x_1391_ = lean_io_error_to_string(v_a_1386_);
v___x_1392_ = lean_string_append(v___x_1390_, v___x_1391_);
lean_dec_ref(v___x_1391_);
v___x_1393_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1394_ = lean_string_append(v___x_1392_, v___x_1393_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1394_);
v___x_1396_ = v___x_1372_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1398_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set_tag(v___x_1388_, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1396_);
v___x_1398_ = v___x_1388_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___boxed(lean_object* v_ppCtx_1403_, lean_object* v_info_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_ppCtx_1403_, v_info_1404_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(lean_object* v_x_1407_, lean_object* v_x_1408_){
_start:
{
if (lean_obj_tag(v_x_1407_) == 0)
{
lean_object* v___x_1409_; 
v___x_1409_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_1409_;
}
else
{
lean_object* v_val_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1421_; 
v_val_1410_ = lean_ctor_get(v_x_1407_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_x_1407_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1412_ = v_x_1407_;
v_isShared_1413_ = v_isSharedCheck_1421_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_val_1410_);
lean_dec(v_x_1407_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1421_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1414_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_1415_ = l_String_quote(v_val_1410_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set_tag(v___x_1412_, 3);
lean_ctor_set(v___x_1412_, 0, v___x_1415_);
v___x_1417_ = v___x_1412_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1414_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = l_Repr_addAppParen(v___x_1418_, v_x_1408_);
return v___x_1419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(lean_object* v_x_1422_, lean_object* v_x_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_x_1422_, v_x_1423_);
lean_dec(v_x_1423_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object* v_ctx_1439_, lean_object* v_info_1440_){
_start:
{
lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v_toTermInfo_1448_; lean_object* v_location_x3f_1449_; uint8_t v_explicit_1450_; lean_object* v___y_1452_; 
v_toTermInfo_1448_ = lean_ctor_get(v_info_1440_, 0);
lean_inc_ref(v_toTermInfo_1448_);
v_location_x3f_1449_ = lean_ctor_get(v_info_1440_, 1);
lean_inc(v_location_x3f_1449_);
v_explicit_1450_ = lean_ctor_get_uint8(v_info_1440_, sizeof(void*)*3);
if (lean_obj_tag(v_location_x3f_1449_) == 1)
{
lean_object* v_val_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1534_; 
v_val_1473_ = lean_ctor_get(v_location_x3f_1449_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_location_x3f_1449_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1475_ = v_location_x3f_1449_;
v_isShared_1476_ = v_isSharedCheck_1534_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_val_1473_);
lean_dec(v_location_x3f_1449_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1534_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v_range_1477_; lean_object* v_pos_1478_; lean_object* v_endPos_1479_; lean_object* v_module_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1532_; 
v_range_1477_ = lean_ctor_get(v_val_1473_, 1);
v_pos_1478_ = lean_ctor_get(v_range_1477_, 0);
lean_inc_ref(v_pos_1478_);
v_endPos_1479_ = lean_ctor_get(v_range_1477_, 2);
lean_inc_ref(v_endPos_1479_);
v_module_1480_ = lean_ctor_get(v_val_1473_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_val_1473_);
if (v_isSharedCheck_1532_ == 0)
{
lean_object* v_unused_1533_; 
v_unused_1533_ = lean_ctor_get(v_val_1473_, 1);
lean_dec(v_unused_1533_);
v___x_1482_ = v_val_1473_;
v_isShared_1483_ = v_isSharedCheck_1532_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_module_1480_);
lean_dec(v_val_1473_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1532_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v_line_1484_; lean_object* v_column_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1531_; 
v_line_1484_ = lean_ctor_get(v_pos_1478_, 0);
v_column_1485_ = lean_ctor_get(v_pos_1478_, 1);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_pos_1478_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1487_ = v_pos_1478_;
v_isShared_1488_ = v_isSharedCheck_1531_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_column_1485_);
lean_inc(v_line_1484_);
lean_dec(v_pos_1478_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1531_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v_line_1489_; lean_object* v_column_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1530_; 
v_line_1489_ = lean_ctor_get(v_endPos_1479_, 0);
v_column_1490_ = lean_ctor_get(v_endPos_1479_, 1);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_endPos_1479_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1492_ = v_endPos_1479_;
v_isShared_1493_ = v_isSharedCheck_1530_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_column_1490_);
lean_inc(v_line_1489_);
lean_dec(v_endPos_1479_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1530_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
uint8_t v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1494_ = 1;
v___x_1495_ = l_Lean_Name_toString(v_module_1480_, v___x_1494_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set_tag(v___x_1475_, 3);
lean_ctor_set(v___x_1475_, 0, v___x_1495_);
v___x_1497_ = v___x_1475_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1498_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
if (v_isShared_1493_ == 0)
{
lean_ctor_set_tag(v___x_1492_, 5);
lean_ctor_set(v___x_1492_, 1, v___x_1498_);
lean_ctor_set(v___x_1492_, 0, v___x_1497_);
v___x_1500_ = v___x_1492_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1501_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_1502_ = l_Nat_reprFast(v_line_1484_);
v___x_1503_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set_tag(v___x_1487_, 5);
lean_ctor_set(v___x_1487_, 1, v___x_1503_);
lean_ctor_set(v___x_1487_, 0, v___x_1501_);
v___x_1505_ = v___x_1487_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1506_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
if (v_isShared_1483_ == 0)
{
lean_ctor_set_tag(v___x_1482_, 5);
lean_ctor_set(v___x_1482_, 1, v___x_1506_);
lean_ctor_set(v___x_1482_, 0, v___x_1505_);
v___x_1508_ = v___x_1482_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1509_ = l_Nat_reprFast(v_column_1485_);
v___x_1510_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
v___x_1511_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1508_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v___x_1513_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1511_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1500_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_1516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1514_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = l_Nat_reprFast(v_line_1489_);
v___x_1518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
v___x_1519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1501_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
lean_ctor_set(v___x_1520_, 1, v___x_1506_);
v___x_1521_ = l_Nat_reprFast(v_column_1490_);
v___x_1522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
v___x_1523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1520_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
lean_ctor_set(v___x_1524_, 1, v___x_1512_);
v___x_1525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1516_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___y_1452_ = v___x_1525_;
goto v___jp_1451_;
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
lean_object* v___x_1535_; 
lean_dec(v_location_x3f_1449_);
v___x_1535_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
v___y_1452_ = v___x_1535_;
goto v___jp_1451_;
}
v___jp_1442_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
lean_inc_ref(v___y_1444_);
v___x_1445_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___y_1444_);
v___x_1446_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___y_1443_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
return v___x_1447_;
}
v___jp_1451_:
{
lean_object* v_lctx_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v_a_1456_; lean_object* v___x_1457_; 
v_lctx_1453_ = lean_ctor_get(v_toTermInfo_1448_, 1);
lean_inc_ref(v_lctx_1453_);
v___x_1454_ = l_Lean_Elab_ContextInfo_toPPContext(v_ctx_1439_, v_lctx_1453_);
v___x_1455_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v___x_1454_, v_info_1440_);
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref(v___x_1455_);
v___x_1457_ = l_Lean_Elab_TermInfo_format(v_ctx_1439_, v_toTermInfo_1448_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___x_1459_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__1));
v___x_1460_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
lean_ctor_set(v___x_1460_, 1, v_a_1458_);
v___x_1461_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__3));
v___x_1462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1460_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
v___x_1463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
lean_ctor_set(v___x_1463_, 1, v___y_1452_);
v___x_1464_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__5));
v___x_1465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1463_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_a_1456_, v___x_1466_);
v___x_1468_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1465_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__7));
v___x_1470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1468_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
if (v_explicit_1450_ == 0)
{
lean_object* v___x_1471_; 
v___x_1471_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__8));
v___y_1443_ = v___x_1470_;
v___y_1444_ = v___x_1471_;
goto v___jp_1442_;
}
else
{
lean_object* v___x_1472_; 
v___x_1472_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__9));
v___y_1443_ = v___x_1470_;
v___y_1444_ = v___x_1472_;
goto v___jp_1442_;
}
}
else
{
lean_dec(v_a_1456_);
lean_dec(v___y_1452_);
return v___x_1457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object* v_ctx_1536_, lean_object* v_info_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1536_, v_info_1537_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object* v_ctx_1543_, lean_object* v_info_1544_){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = ((lean_object*)(l_Lean_Elab_ChoiceInfo_format___closed__1));
v___x_1546_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1543_, v_info_1544_);
v___x_1547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceResolutionInfo_format(lean_object* v_ctx_1560_, lean_object* v_info_1561_){
_start:
{
lean_object* v_stx_1562_; lean_object* v_chosenAltIdx_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1591_; 
v_stx_1562_ = lean_ctor_get(v_info_1561_, 0);
v_chosenAltIdx_1563_ = lean_ctor_get(v_info_1561_, 1);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_info_1561_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1565_ = v_info_1561_;
v_isShared_1566_ = v_isSharedCheck_1591_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_chosenAltIdx_1563_);
lean_inc(v_stx_1562_);
lean_dec(v_info_1561_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1591_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1567_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__1));
lean_inc(v_chosenAltIdx_1563_);
v___x_1568_ = l_Nat_reprFast(v_chosenAltIdx_1563_);
v___x_1569_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set_tag(v___x_1565_, 5);
lean_ctor_set(v___x_1565_, 1, v___x_1569_);
lean_ctor_set(v___x_1565_, 0, v___x_1567_);
v___x_1571_ = v___x_1565_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1572_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__3));
v___x_1573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = l_Lean_Syntax_getNumArgs(v_stx_1562_);
v___x_1575_ = l_Nat_reprFast(v___x_1574_);
v___x_1576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
v___x_1577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1573_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__5));
v___x_1579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = l_Lean_Syntax_getArg(v_stx_1562_, v_chosenAltIdx_1563_);
lean_dec(v_chosenAltIdx_1563_);
v___x_1581_ = l_Lean_Syntax_getKind(v___x_1580_);
v___x_1582_ = 1;
v___x_1583_ = l_Lean_Name_toString(v___x_1581_, v___x_1582_);
v___x_1584_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
v___x_1585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1579_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__7));
v___x_1587_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1560_, v_stx_1562_);
lean_dec(v_stx_1562_);
v___x_1589_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
return v___x_1589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object* v_ctx_1595_, lean_object* v_info_1596_){
_start:
{
lean_object* v_stx_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v_stx_1597_ = lean_ctor_get(v_info_1596_, 1);
v___x_1598_ = ((lean_object*)(l_Lean_Elab_DocInfo_format___closed__1));
lean_inc(v_stx_1597_);
v___x_1599_ = l_Lean_Syntax_getKind(v_stx_1597_);
v___x_1600_ = 1;
v___x_1601_ = l_Lean_Name_toString(v___x_1599_, v___x_1600_);
v___x_1602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
v___x_1603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1598_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1603_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1595_, v_info_1596_);
v___x_1607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1605_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object* v_ctx_1611_, lean_object* v_info_1612_){
_start:
{
lean_object* v_toElabInfo_1613_; lean_object* v_name_1614_; uint8_t v_kind_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_toElabInfo_1613_ = lean_ctor_get(v_info_1612_, 0);
lean_inc_ref(v_toElabInfo_1613_);
v_name_1614_ = lean_ctor_get(v_info_1612_, 1);
lean_inc(v_name_1614_);
v_kind_1615_ = lean_ctor_get_uint8(v_info_1612_, sizeof(void*)*2);
lean_dec_ref(v_info_1612_);
v___x_1616_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__1));
v___x_1617_ = 1;
v___x_1618_ = l_Lean_Name_toString(v_name_1614_, v___x_1617_);
v___x_1619_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
v___x_1620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1616_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__5));
v___x_1622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1620_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = l_Lean_Elab_instReprDocElabKind_repr(v_kind_1615_, v___x_1623_);
v___x_1625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1622_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__7));
v___x_1627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1611_, v_toElabInfo_1613_);
v___x_1629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object* v_ctx_1630_, lean_object* v_x_1631_){
_start:
{
switch(lean_obj_tag(v_x_1631_))
{
case 0:
{
lean_object* v_i_1633_; lean_object* v___x_1634_; 
v_i_1633_ = lean_ctor_get(v_x_1631_, 0);
lean_inc_ref(v_i_1633_);
lean_dec_ref_known(v_x_1631_, 1);
v___x_1634_ = l_Lean_Elab_TacticInfo_format(v_ctx_1630_, v_i_1633_);
return v___x_1634_;
}
case 1:
{
lean_object* v_i_1635_; lean_object* v___x_1636_; 
v_i_1635_ = lean_ctor_get(v_x_1631_, 0);
lean_inc_ref(v_i_1635_);
lean_dec_ref_known(v_x_1631_, 1);
v___x_1636_ = l_Lean_Elab_TermInfo_format(v_ctx_1630_, v_i_1635_);
return v___x_1636_;
}
case 2:
{
lean_object* v_i_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1645_; 
v_i_1637_ = lean_ctor_get(v_x_1631_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_x_1631_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1639_ = v_x_1631_;
v_isShared_1640_ = v_isSharedCheck_1645_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_i_1637_);
lean_dec(v_x_1631_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1645_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1641_ = l_Lean_Elab_PartialTermInfo_format(v_ctx_1630_, v_i_1637_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set_tag(v___x_1639_, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1641_);
v___x_1643_ = v___x_1639_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
case 3:
{
lean_object* v_i_1646_; lean_object* v___x_1647_; 
v_i_1646_ = lean_ctor_get(v_x_1631_, 0);
lean_inc_ref(v_i_1646_);
lean_dec_ref_known(v_x_1631_, 1);
v___x_1647_ = l_Lean_Elab_CommandInfo_format(v_ctx_1630_, v_i_1646_);
return v___x_1647_;
}
case 4:
{
lean_object* v_i_1648_; lean_object* v___x_1649_; 
v_i_1648_ = lean_ctor_get(v_x_1631_, 0);
lean_inc_ref(v_i_1648_);
lean_dec_ref_known(v_x_1631_, 1);
v___x_1649_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1630_, v_i_1648_);
lean_dec_ref(v_ctx_1630_);
return v___x_1649_;
}
case 5:
{
lean_object* v_i_1650_; lean_object* v___x_1651_; 
v_i_1650_ = lean_ctor_get(v_x_1631_, 0);
lean_inc_ref(v_i_1650_);
lean_dec_ref_known(v_x_1631_, 1);
v___x_1651_ = l_Lean_Elab_OptionInfo_format(v_ctx_1630_, v_i_1650_);
return v___x_1651_;
}
case 6:
{
lean_object* v_i_1652_; lean_object* v___x_1653_; 
v_i_1652_ = lean_ctor_get(v_x_1631_, 0);
lean_inc_ref(v_i_1652_);
lean_dec_ref_known(v_x_1631_, 1);
v___x_1653_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_1630_, v_i_1652_);
return v___x_1653_;
}
case 7:
{
lean_object* v_i_1654_; lean_object* v___x_1655_; 
v_i_1654_ = lean_ctor_get(v_x_1631_, 0);
lean_inc_ref(v_i_1654_);
lean_dec_ref_known(v_x_1631_, 1);
v___x_1655_ = l_Lean_Elab_FieldInfo_format(v_ctx_1630_, v_i_1654_);
return v___x_1655_;
}
case 8:
{
lean_object* v_i_1656_; lean_object* v___x_1657_; 
v_i_1656_ = lean_ctor_get(v_x_1631_, 0);
lean_inc_ref(v_i_1656_);
lean_dec_ref_known(v_x_1631_, 1);
v___x_1657_ = l_Lean_Elab_CompletionInfo_format(v_ctx_1630_, v_i_1656_);
return v___x_1657_;
}
case 9:
{
lean_object* v_i_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1666_; 
lean_dec_ref(v_ctx_1630_);
v_i_1658_ = lean_ctor_get(v_x_1631_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_x_1631_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1660_ = v_x_1631_;
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_i_1658_);
lean_dec(v_x_1631_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1662_ = l_Lean_Elab_UserWidgetInfo_format(v_i_1658_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set_tag(v___x_1660_, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1662_);
v___x_1664_ = v___x_1660_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
case 10:
{
lean_object* v_i_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1675_; 
lean_dec_ref(v_ctx_1630_);
v_i_1667_ = lean_ctor_get(v_x_1631_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_x_1631_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1669_ = v_x_1631_;
v_isShared_1670_ = v_isSharedCheck_1675_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_i_1667_);
lean_dec(v_x_1631_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1675_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1671_ = l_Lean_Elab_CustomInfo_format(v_i_1667_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set_tag(v___x_1669_, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1671_);
v___x_1673_ = v___x_1669_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
case 11:
{
lean_object* v_i_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1684_; 
lean_dec_ref(v_ctx_1630_);
v_i_1676_ = lean_ctor_get(v_x_1631_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_x_1631_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1678_ = v_x_1631_;
v_isShared_1679_ = v_isSharedCheck_1684_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_i_1676_);
lean_dec(v_x_1631_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1684_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1680_ = l_Lean_Elab_FVarAliasInfo_format(v_i_1676_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set_tag(v___x_1678_, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1680_);
v___x_1682_ = v___x_1678_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
case 12:
{
lean_object* v_i_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1693_; 
v_i_1685_ = lean_ctor_get(v_x_1631_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_x_1631_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1687_ = v_x_1631_;
v_isShared_1688_ = v_isSharedCheck_1693_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_i_1685_);
lean_dec(v_x_1631_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1693_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1689_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1630_, v_i_1685_);
lean_dec(v_i_1685_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set_tag(v___x_1687_, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1689_);
v___x_1691_ = v___x_1687_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
case 13:
{
lean_object* v_i_1694_; lean_object* v___x_1695_; 
v_i_1694_ = lean_ctor_get(v_x_1631_, 0);
lean_inc_ref(v_i_1694_);
lean_dec_ref_known(v_x_1631_, 1);
v___x_1695_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1630_, v_i_1694_);
return v___x_1695_;
}
case 14:
{
lean_object* v_i_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1704_; 
v_i_1696_ = lean_ctor_get(v_x_1631_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_x_1631_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1698_ = v_x_1631_;
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_i_1696_);
lean_dec(v_x_1631_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1700_ = l_Lean_Elab_ChoiceInfo_format(v_ctx_1630_, v_i_1696_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set_tag(v___x_1698_, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1700_);
v___x_1702_ = v___x_1698_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
case 15:
{
lean_object* v_i_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1713_; 
v_i_1705_ = lean_ctor_get(v_x_1631_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_x_1631_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1707_ = v_x_1631_;
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_i_1705_);
lean_dec(v_x_1631_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1709_ = l_Lean_Elab_ChoiceResolutionInfo_format(v_ctx_1630_, v_i_1705_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set_tag(v___x_1707_, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1709_);
v___x_1711_ = v___x_1707_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
case 16:
{
lean_object* v_i_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1722_; 
v_i_1714_ = lean_ctor_get(v_x_1631_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_x_1631_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1716_ = v_x_1631_;
v_isShared_1717_ = v_isSharedCheck_1722_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_i_1714_);
lean_dec(v_x_1631_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1722_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1718_ = l_Lean_Elab_DocInfo_format(v_ctx_1630_, v_i_1714_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set_tag(v___x_1716_, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1718_);
v___x_1720_ = v___x_1716_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
default: 
{
lean_object* v_i_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1731_; 
v_i_1723_ = lean_ctor_get(v_x_1631_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_x_1631_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1725_ = v_x_1631_;
v_isShared_1726_ = v_isSharedCheck_1731_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_i_1723_);
lean_dec(v_x_1631_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1731_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1727_ = l_Lean_Elab_DocElabInfo_format(v_ctx_1630_, v_i_1723_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set_tag(v___x_1725_, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1727_);
v___x_1729_ = v___x_1725_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object* v_ctx_1732_, lean_object* v_x_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Elab_Info_format(v_ctx_1732_, v_x_1733_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object* v_x_1736_, lean_object* v_x_1737_){
_start:
{
if (lean_obj_tag(v_x_1737_) == 0)
{
return v_x_1736_;
}
else
{
lean_object* v_head_1738_; lean_object* v_tail_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_head_1738_ = lean_ctor_get(v_x_1737_, 0);
v_tail_1739_ = lean_ctor_get(v_x_1737_, 1);
v___x_1740_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2));
v___x_1741_ = lean_string_append(v_x_1736_, v___x_1740_);
v___x_1742_ = lean_expr_dbg_to_string(v_head_1738_);
v___x_1743_ = lean_string_append(v___x_1741_, v___x_1742_);
lean_dec_ref(v___x_1742_);
v_x_1736_ = v___x_1743_;
v_x_1737_ = v_tail_1739_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object* v_x_1745_, lean_object* v_x_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v_x_1745_, v_x_1746_);
lean_dec(v_x_1746_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object* v_x_1750_){
_start:
{
if (lean_obj_tag(v_x_1750_) == 0)
{
lean_object* v___x_1751_; 
v___x_1751_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0));
return v___x_1751_;
}
else
{
lean_object* v_tail_1752_; 
v_tail_1752_ = lean_ctor_get(v_x_1750_, 1);
if (lean_obj_tag(v_tail_1752_) == 0)
{
lean_object* v_head_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v_head_1753_ = lean_ctor_get(v_x_1750_, 0);
v___x_1754_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1755_ = lean_expr_dbg_to_string(v_head_1753_);
v___x_1756_ = lean_string_append(v___x_1754_, v___x_1755_);
lean_dec_ref(v___x_1755_);
v___x_1757_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1758_ = lean_string_append(v___x_1756_, v___x_1757_);
return v___x_1758_;
}
else
{
lean_object* v_head_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; uint32_t v___x_1764_; lean_object* v___x_1765_; 
v_head_1759_ = lean_ctor_get(v_x_1750_, 0);
v___x_1760_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1761_ = lean_expr_dbg_to_string(v_head_1759_);
v___x_1762_ = lean_string_append(v___x_1760_, v___x_1761_);
lean_dec_ref(v___x_1761_);
v___x_1763_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v___x_1762_, v_tail_1752_);
v___x_1764_ = 93;
v___x_1765_ = lean_string_push(v___x_1763_, v___x_1764_);
return v___x_1765_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object* v_x_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v_x_1766_);
lean_dec(v_x_1766_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object* v_ctx_1774_){
_start:
{
switch(lean_obj_tag(v_ctx_1774_))
{
case 0:
{
lean_object* v___x_1775_; 
lean_dec_ref_known(v_ctx_1774_, 1);
v___x_1775_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__1));
return v___x_1775_;
}
case 1:
{
lean_object* v_parentDecl_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1789_; 
v_parentDecl_1776_ = lean_ctor_get(v_ctx_1774_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_ctx_1774_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1778_ = v_ctx_1774_;
v_isShared_1779_ = v_isSharedCheck_1789_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_parentDecl_1776_);
lean_dec(v_ctx_1774_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1789_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1780_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__2));
v___x_1781_ = 1;
v___x_1782_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_parentDecl_1776_, v___x_1781_);
v___x_1783_ = lean_string_append(v___x_1780_, v___x_1782_);
lean_dec_ref(v___x_1782_);
v___x_1784_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1785_ = lean_string_append(v___x_1783_, v___x_1784_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set_tag(v___x_1778_, 3);
lean_ctor_set(v___x_1778_, 0, v___x_1785_);
v___x_1787_ = v___x_1778_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
default: 
{
lean_object* v_autoImplicits_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1805_; 
v_autoImplicits_1790_ = lean_ctor_get(v_ctx_1774_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_ctx_1774_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1792_ = v_ctx_1774_;
v_isShared_1793_ = v_isSharedCheck_1805_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_autoImplicits_1790_);
lean_dec(v_ctx_1774_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1805_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1794_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__3));
v___x_1795_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__4));
v___x_1796_ = lean_array_to_list(v_autoImplicits_1790_);
v___x_1797_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v___x_1796_);
lean_dec(v___x_1796_);
v___x_1798_ = lean_string_append(v___x_1795_, v___x_1797_);
lean_dec_ref(v___x_1797_);
v___x_1799_ = lean_string_append(v___x_1794_, v___x_1798_);
lean_dec_ref(v___x_1798_);
v___x_1800_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1801_ = lean_string_append(v___x_1799_, v___x_1800_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set_tag(v___x_1792_, 3);
lean_ctor_set(v___x_1792_, 0, v___x_1801_);
v___x_1803_ = v___x_1792_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(3, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format(lean_object* v_tree_1815_, lean_object* v_ctx_x3f_1816_){
_start:
{
switch(lean_obj_tag(v_tree_1815_))
{
case 0:
{
lean_object* v_i_1818_; lean_object* v_t_1819_; lean_object* v___x_1820_; 
v_i_1818_ = lean_ctor_get(v_tree_1815_, 0);
lean_inc_ref(v_i_1818_);
v_t_1819_ = lean_ctor_get(v_tree_1815_, 1);
lean_inc_ref(v_t_1819_);
lean_dec_ref_known(v_tree_1815_, 2);
v___x_1820_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1818_, v_ctx_x3f_1816_);
v_tree_1815_ = v_t_1819_;
v_ctx_x3f_1816_ = v___x_1820_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_ctx_x3f_1816_) == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_dec_ref_known(v_tree_1815_, 2);
v___x_1822_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__1));
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
return v___x_1823_;
}
else
{
lean_object* v_i_1824_; lean_object* v_children_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1875_; 
v_i_1824_ = lean_ctor_get(v_tree_1815_, 0);
v_children_1825_ = lean_ctor_get(v_tree_1815_, 1);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_tree_1815_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1827_ = v_tree_1815_;
v_isShared_1828_ = v_isSharedCheck_1875_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_children_1825_);
lean_inc(v_i_1824_);
lean_dec(v_tree_1815_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1875_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_val_1829_; lean_object* v___x_1830_; 
v_val_1829_ = lean_ctor_get(v_ctx_x3f_1816_, 0);
lean_inc_ref(v_i_1824_);
lean_inc(v_val_1829_);
v___x_1830_ = l_Lean_Elab_Info_format(v_val_1829_, v_i_1824_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1874_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1833_ = v___x_1830_;
v_isShared_1834_ = v_isSharedCheck_1874_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1830_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1874_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_size_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v_size_1835_ = lean_ctor_get(v_children_1825_, 2);
v___x_1836_ = lean_unsigned_to_nat(0u);
v___x_1837_ = lean_nat_dec_eq(v_size_1835_, v___x_1836_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_del_object(v___x_1833_);
v___x_1838_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_1816_, v_i_1824_);
lean_dec_ref(v_i_1824_);
v___x_1839_ = l_Lean_PersistentArray_toList___redArg(v_children_1825_);
lean_dec_ref(v_children_1825_);
v___x_1840_ = lean_box(0);
v___x_1841_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1838_, v___x_1839_, v___x_1840_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1857_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1857_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1857_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1846_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1828_ == 0)
{
lean_ctor_set_tag(v___x_1827_, 5);
lean_ctor_set(v___x_1827_, 1, v_a_1831_);
lean_ctor_set(v___x_1827_, 0, v___x_1846_);
v___x_1848_ = v___x_1827_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1846_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_a_1831_);
v___x_1848_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1849_ = lean_box(1);
v___x_1850_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1849_, v_a_1842_);
v___x_1851_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1848_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = l_Std_Format_nestD(v___x_1851_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1852_);
v___x_1854_ = v___x_1844_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec(v_a_1831_);
lean_del_object(v___x_1827_);
v_a_1858_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1841_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1841_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1868_; 
lean_dec_ref(v_children_1825_);
lean_dec_ref(v_i_1824_);
lean_dec_ref_known(v_ctx_x3f_1816_, 1);
v___x_1866_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1828_ == 0)
{
lean_ctor_set_tag(v___x_1827_, 5);
lean_ctor_set(v___x_1827_, 1, v_a_1831_);
lean_ctor_set(v___x_1827_, 0, v___x_1866_);
v___x_1868_ = v___x_1827_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1866_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v_a_1831_);
v___x_1868_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
v___x_1869_ = l_Std_Format_nestD(v___x_1868_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1869_);
v___x_1871_ = v___x_1833_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
else
{
lean_del_object(v___x_1827_);
lean_dec_ref(v_children_1825_);
lean_dec_ref(v_i_1824_);
lean_dec_ref_known(v_ctx_x3f_1816_, 1);
return v___x_1830_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v_ctx_x3f_1816_);
v_mvarId_1876_ = lean_ctor_get(v_tree_1815_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_tree_1815_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1878_ = v_tree_1815_;
v_isShared_1879_ = v_isSharedCheck_1889_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_mvarId_1876_);
lean_dec(v_tree_1815_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1889_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; uint8_t v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1880_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__5));
v___x_1881_ = 1;
v___x_1882_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_1876_, v___x_1881_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set_tag(v___x_1878_, 3);
lean_ctor_set(v___x_1878_, 0, v___x_1882_);
v___x_1884_ = v___x_1878_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1880_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = l_Std_Format_nestD(v___x_1885_);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
return v___x_1887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object* v___x_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_){
_start:
{
if (lean_obj_tag(v_x_1891_) == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_dec(v___x_1890_);
v___x_1894_ = l_List_reverse___redArg(v_x_1892_);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
return v___x_1895_;
}
else
{
lean_object* v_head_1896_; lean_object* v_tail_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1915_; 
v_head_1896_ = lean_ctor_get(v_x_1891_, 0);
v_tail_1897_ = lean_ctor_get(v_x_1891_, 1);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_x_1891_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1899_ = v_x_1891_;
v_isShared_1900_ = v_isSharedCheck_1915_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_tail_1897_);
lean_inc(v_head_1896_);
lean_dec(v_x_1891_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1915_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; 
lean_inc(v___x_1890_);
v___x_1901_ = l_Lean_Elab_InfoTree_format(v_head_1896_, v___x_1890_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1901_, 1);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 1, v_x_1892_);
lean_ctor_set(v___x_1899_, 0, v_a_1902_);
v___x_1904_ = v___x_1899_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1902_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_x_1892_);
v___x_1904_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
v_x_1891_ = v_tail_1897_;
v_x_1892_ = v___x_1904_;
goto _start;
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
lean_del_object(v___x_1899_);
lean_dec(v_tail_1897_);
lean_dec(v_x_1892_);
lean_dec(v___x_1890_);
v_a_1907_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1901_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1901_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
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
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object* v___x_1916_, lean_object* v_x_1917_, lean_object* v_x_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1916_, v_x_1917_, v_x_1918_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object* v_tree_1921_, lean_object* v_ctx_x3f_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_Elab_InfoTree_format(v_tree_1921_, v_ctx_x3f_1922_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object* v_f_1925_, lean_object* v_s_1926_){
_start:
{
uint8_t v_enabled_1927_; lean_object* v_assignment_1928_; lean_object* v_lazyAssignment_1929_; lean_object* v_trees_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1938_; 
v_enabled_1927_ = lean_ctor_get_uint8(v_s_1926_, sizeof(void*)*3);
v_assignment_1928_ = lean_ctor_get(v_s_1926_, 0);
v_lazyAssignment_1929_ = lean_ctor_get(v_s_1926_, 1);
v_trees_1930_ = lean_ctor_get(v_s_1926_, 2);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_s_1926_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1932_ = v_s_1926_;
v_isShared_1933_ = v_isSharedCheck_1938_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_trees_1930_);
lean_inc(v_lazyAssignment_1929_);
lean_inc(v_assignment_1928_);
lean_dec(v_s_1926_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1938_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1934_ = lean_apply_1(v_f_1925_, v_trees_1930_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 2, v___x_1934_);
v___x_1936_ = v___x_1932_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_assignment_1928_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_lazyAssignment_1929_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v___x_1934_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*3, v_enabled_1927_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object* v_inst_1939_, lean_object* v_f_1940_){
_start:
{
lean_object* v_modifyInfoState_1941_; lean_object* v___f_1942_; lean_object* v___x_1943_; 
v_modifyInfoState_1941_ = lean_ctor_get(v_inst_1939_, 1);
lean_inc(v_modifyInfoState_1941_);
lean_dec_ref(v_inst_1939_);
v___f_1942_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1942_, 0, v_f_1940_);
v___x_1943_ = lean_apply_1(v_modifyInfoState_1941_, v___f_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object* v_m_1944_, lean_object* v_inst_1945_, lean_object* v_f_1946_){
_start:
{
lean_object* v_modifyInfoState_1947_; lean_object* v___f_1948_; lean_object* v___x_1949_; 
v_modifyInfoState_1947_ = lean_ctor_get(v_inst_1945_, 1);
lean_inc(v_modifyInfoState_1947_);
lean_dec_ref(v_inst_1945_);
v___f_1948_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1948_, 0, v_f_1946_);
v___x_1949_ = lean_apply_1(v_modifyInfoState_1947_, v___f_1948_);
return v___x_1949_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1950_ = lean_unsigned_to_nat(32u);
v___x_1951_ = lean_mk_empty_array_with_capacity(v___x_1950_);
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
return v___x_1952_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1953_ = ((size_t)5ULL);
v___x_1954_ = lean_unsigned_to_nat(0u);
v___x_1955_ = lean_unsigned_to_nat(32u);
v___x_1956_ = lean_mk_empty_array_with_capacity(v___x_1955_);
v___x_1957_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0);
v___x_1958_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
lean_ctor_set(v___x_1958_, 1, v___x_1956_);
lean_ctor_set(v___x_1958_, 2, v___x_1954_);
lean_ctor_set(v___x_1958_, 3, v___x_1954_);
lean_ctor_set_usize(v___x_1958_, 4, v___x_1953_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object* v_s_1959_){
_start:
{
uint8_t v_enabled_1960_; lean_object* v_assignment_1961_; lean_object* v_lazyAssignment_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1970_; 
v_enabled_1960_ = lean_ctor_get_uint8(v_s_1959_, sizeof(void*)*3);
v_assignment_1961_ = lean_ctor_get(v_s_1959_, 0);
v_lazyAssignment_1962_ = lean_ctor_get(v_s_1959_, 1);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_s_1959_);
if (v_isSharedCheck_1970_ == 0)
{
lean_object* v_unused_1971_; 
v_unused_1971_ = lean_ctor_get(v_s_1959_, 2);
lean_dec(v_unused_1971_);
v___x_1964_ = v_s_1959_;
v_isShared_1965_ = v_isSharedCheck_1970_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_lazyAssignment_1962_);
lean_inc(v_assignment_1961_);
lean_dec(v_s_1959_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1970_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1966_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 2, v___x_1966_);
v___x_1968_ = v___x_1964_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_assignment_1961_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_lazyAssignment_1962_);
lean_ctor_set(v_reuseFailAlloc_1969_, 2, v___x_1966_);
lean_ctor_set_uint8(v_reuseFailAlloc_1969_, sizeof(void*)*3, v_enabled_1960_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object* v_toPure_1972_, lean_object* v_trees_1973_, lean_object* v_____r_1974_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_apply_2(v_toPure_1972_, lean_box(0), v_trees_1973_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object* v_toPure_1976_, lean_object* v_modifyInfoState_1977_, lean_object* v___f_1978_, lean_object* v_toBind_1979_, lean_object* v_____do__lift_1980_){
_start:
{
lean_object* v_trees_1981_; lean_object* v___f_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v_trees_1981_ = lean_ctor_get(v_____do__lift_1980_, 2);
lean_inc_ref(v_trees_1981_);
lean_dec_ref(v_____do__lift_1980_);
v___f_1982_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1982_, 0, v_toPure_1976_);
lean_closure_set(v___f_1982_, 1, v_trees_1981_);
v___x_1983_ = lean_apply_1(v_modifyInfoState_1977_, v___f_1978_);
v___x_1984_ = lean_apply_4(v_toBind_1979_, lean_box(0), lean_box(0), v___x_1983_, v___f_1982_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object* v_inst_1986_, lean_object* v_inst_1987_){
_start:
{
lean_object* v_toApplicative_1988_; lean_object* v_toBind_1989_; lean_object* v_getInfoState_1990_; lean_object* v_modifyInfoState_1991_; lean_object* v_toPure_1992_; lean_object* v___f_1993_; lean_object* v___f_1994_; lean_object* v___x_1995_; 
v_toApplicative_1988_ = lean_ctor_get(v_inst_1986_, 0);
lean_inc_ref(v_toApplicative_1988_);
v_toBind_1989_ = lean_ctor_get(v_inst_1986_, 1);
lean_inc_n(v_toBind_1989_, 2);
lean_dec_ref(v_inst_1986_);
v_getInfoState_1990_ = lean_ctor_get(v_inst_1987_, 0);
lean_inc(v_getInfoState_1990_);
v_modifyInfoState_1991_ = lean_ctor_get(v_inst_1987_, 1);
lean_inc(v_modifyInfoState_1991_);
lean_dec_ref(v_inst_1987_);
v_toPure_1992_ = lean_ctor_get(v_toApplicative_1988_, 1);
lean_inc(v_toPure_1992_);
lean_dec_ref(v_toApplicative_1988_);
v___f_1993_ = ((lean_object*)(l_Lean_Elab_getResetInfoTrees___redArg___closed__0));
v___f_1994_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1994_, 0, v_toPure_1992_);
lean_closure_set(v___f_1994_, 1, v_modifyInfoState_1991_);
lean_closure_set(v___f_1994_, 2, v___f_1993_);
lean_closure_set(v___f_1994_, 3, v_toBind_1989_);
v___x_1995_ = lean_apply_4(v_toBind_1989_, lean_box(0), lean_box(0), v_getInfoState_1990_, v___f_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object* v_m_1996_, lean_object* v_inst_1997_, lean_object* v_inst_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_1997_, v_inst_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object* v_t_2000_, lean_object* v_s_2001_){
_start:
{
uint8_t v_enabled_2002_; lean_object* v_assignment_2003_; lean_object* v_lazyAssignment_2004_; lean_object* v_trees_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2013_; 
v_enabled_2002_ = lean_ctor_get_uint8(v_s_2001_, sizeof(void*)*3);
v_assignment_2003_ = lean_ctor_get(v_s_2001_, 0);
v_lazyAssignment_2004_ = lean_ctor_get(v_s_2001_, 1);
v_trees_2005_ = lean_ctor_get(v_s_2001_, 2);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_s_2001_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2007_ = v_s_2001_;
v_isShared_2008_ = v_isSharedCheck_2013_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_trees_2005_);
lean_inc(v_lazyAssignment_2004_);
lean_inc(v_assignment_2003_);
lean_dec(v_s_2001_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2013_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; lean_object* v___x_2011_; 
v___x_2009_ = l_Lean_PersistentArray_push___redArg(v_trees_2005_, v_t_2000_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 2, v___x_2009_);
v___x_2011_ = v___x_2007_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_assignment_2003_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_lazyAssignment_2004_);
lean_ctor_set(v_reuseFailAlloc_2012_, 2, v___x_2009_);
lean_ctor_set_uint8(v_reuseFailAlloc_2012_, sizeof(void*)*3, v_enabled_2002_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object* v_toPure_2014_, lean_object* v_modifyInfoState_2015_, lean_object* v___f_2016_, lean_object* v_____do__lift_2017_){
_start:
{
uint8_t v_enabled_2018_; 
v_enabled_2018_ = lean_ctor_get_uint8(v_____do__lift_2017_, sizeof(void*)*3);
if (v_enabled_2018_ == 0)
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
lean_dec_ref(v___f_2016_);
lean_dec(v_modifyInfoState_2015_);
v___x_2019_ = lean_box(0);
v___x_2020_ = lean_apply_2(v_toPure_2014_, lean_box(0), v___x_2019_);
return v___x_2020_;
}
else
{
lean_object* v___x_2021_; 
lean_dec(v_toPure_2014_);
v___x_2021_ = lean_apply_1(v_modifyInfoState_2015_, v___f_2016_);
return v___x_2021_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object* v_toPure_2022_, lean_object* v_modifyInfoState_2023_, lean_object* v___f_2024_, lean_object* v_____do__lift_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_Elab_pushInfoTree___redArg___lam__1(v_toPure_2022_, v_modifyInfoState_2023_, v___f_2024_, v_____do__lift_2025_);
lean_dec_ref(v_____do__lift_2025_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object* v_inst_2027_, lean_object* v_inst_2028_, lean_object* v_t_2029_){
_start:
{
lean_object* v_toApplicative_2030_; lean_object* v_toBind_2031_; lean_object* v_getInfoState_2032_; lean_object* v_modifyInfoState_2033_; lean_object* v_toPure_2034_; lean_object* v___f_2035_; lean_object* v___f_2036_; lean_object* v___x_2037_; 
v_toApplicative_2030_ = lean_ctor_get(v_inst_2027_, 0);
lean_inc_ref(v_toApplicative_2030_);
v_toBind_2031_ = lean_ctor_get(v_inst_2027_, 1);
lean_inc(v_toBind_2031_);
lean_dec_ref(v_inst_2027_);
v_getInfoState_2032_ = lean_ctor_get(v_inst_2028_, 0);
lean_inc(v_getInfoState_2032_);
v_modifyInfoState_2033_ = lean_ctor_get(v_inst_2028_, 1);
lean_inc(v_modifyInfoState_2033_);
lean_dec_ref(v_inst_2028_);
v_toPure_2034_ = lean_ctor_get(v_toApplicative_2030_, 1);
lean_inc(v_toPure_2034_);
lean_dec_ref(v_toApplicative_2030_);
v___f_2035_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2035_, 0, v_t_2029_);
v___f_2036_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2036_, 0, v_toPure_2034_);
lean_closure_set(v___f_2036_, 1, v_modifyInfoState_2033_);
lean_closure_set(v___f_2036_, 2, v___f_2035_);
v___x_2037_ = lean_apply_4(v_toBind_2031_, lean_box(0), lean_box(0), v_getInfoState_2032_, v___f_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object* v_m_2038_, lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_t_2041_){
_start:
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2039_, v_inst_2040_, v_t_2041_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object* v_toPure_2043_, lean_object* v_t_2044_, lean_object* v_inst_2045_, lean_object* v_inst_2046_, lean_object* v_____do__lift_2047_){
_start:
{
uint8_t v_enabled_2048_; 
v_enabled_2048_ = lean_ctor_get_uint8(v_____do__lift_2047_, sizeof(void*)*3);
if (v_enabled_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
lean_dec_ref(v_inst_2046_);
lean_dec_ref(v_inst_2045_);
lean_dec_ref(v_t_2044_);
v___x_2049_ = lean_box(0);
v___x_2050_ = lean_apply_2(v_toPure_2043_, lean_box(0), v___x_2049_);
return v___x_2050_;
}
else
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_dec(v_toPure_2043_);
v___x_2051_ = lean_unsigned_to_nat(32u);
v___x_2052_ = lean_mk_empty_array_with_capacity(v___x_2051_);
lean_dec_ref(v___x_2052_);
v___x_2053_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2054_, 0, v_t_2044_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
v___x_2055_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2045_, v_inst_2046_, v___x_2054_);
return v___x_2055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object* v_toPure_2056_, lean_object* v_t_2057_, lean_object* v_inst_2058_, lean_object* v_inst_2059_, lean_object* v_____do__lift_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Lean_Elab_pushInfoLeaf___redArg___lam__0(v_toPure_2056_, v_t_2057_, v_inst_2058_, v_inst_2059_, v_____do__lift_2060_);
lean_dec_ref(v_____do__lift_2060_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object* v_inst_2062_, lean_object* v_inst_2063_, lean_object* v_t_2064_){
_start:
{
lean_object* v_toApplicative_2065_; lean_object* v_toBind_2066_; lean_object* v_getInfoState_2067_; lean_object* v_toPure_2068_; lean_object* v___f_2069_; lean_object* v___x_2070_; 
v_toApplicative_2065_ = lean_ctor_get(v_inst_2062_, 0);
v_toBind_2066_ = lean_ctor_get(v_inst_2062_, 1);
lean_inc(v_toBind_2066_);
v_getInfoState_2067_ = lean_ctor_get(v_inst_2063_, 0);
lean_inc(v_getInfoState_2067_);
v_toPure_2068_ = lean_ctor_get(v_toApplicative_2065_, 1);
lean_inc(v_toPure_2068_);
v___f_2069_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2069_, 0, v_toPure_2068_);
lean_closure_set(v___f_2069_, 1, v_t_2064_);
lean_closure_set(v___f_2069_, 2, v_inst_2062_);
lean_closure_set(v___f_2069_, 3, v_inst_2063_);
v___x_2070_ = lean_apply_4(v_toBind_2066_, lean_box(0), lean_box(0), v_getInfoState_2067_, v___f_2069_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object* v_m_2071_, lean_object* v_inst_2072_, lean_object* v_inst_2073_, lean_object* v_t_2074_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2072_, v_inst_2073_, v_t_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object* v_inst_2076_, lean_object* v_inst_2077_, lean_object* v_info_2078_){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2079_, 0, v_info_2078_);
v___x_2080_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2076_, v_inst_2077_, v___x_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object* v_m_2081_, lean_object* v_inst_2082_, lean_object* v_inst_2083_, lean_object* v_info_2084_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_2082_, v_inst_2083_, v_info_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object* v_stx_2086_, lean_object* v_expectedType_x3f_2087_, lean_object* v_inst_2088_, lean_object* v_inst_2089_, lean_object* v_____do__lift_2090_){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v_stx_2086_);
v___x_2093_ = l_Lean_LocalContext_empty;
v___x_2094_ = 0;
v___x_2095_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2095_, 0, v___x_2092_);
lean_ctor_set(v___x_2095_, 1, v___x_2093_);
lean_ctor_set(v___x_2095_, 2, v_expectedType_x3f_2087_);
lean_ctor_set(v___x_2095_, 3, v_____do__lift_2090_);
lean_ctor_set_uint8(v___x_2095_, sizeof(void*)*4, v___x_2094_);
lean_ctor_set_uint8(v___x_2095_, sizeof(void*)*4 + 1, v___x_2094_);
v___x_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
v___x_2097_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2088_, v_inst_2089_, v___x_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_inst_2100_, lean_object* v_inst_2101_, lean_object* v_stx_2102_, lean_object* v_n_2103_, lean_object* v_expectedType_x3f_2104_){
_start:
{
lean_object* v_toBind_2105_; lean_object* v___f_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v_toBind_2105_ = lean_ctor_get(v_inst_2098_, 1);
lean_inc(v_toBind_2105_);
lean_inc_ref(v_inst_2098_);
v___f_2106_ = lean_alloc_closure((void*)(l_Lean_Elab_addConstInfo___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2106_, 0, v_stx_2102_);
lean_closure_set(v___f_2106_, 1, v_expectedType_x3f_2104_);
lean_closure_set(v___f_2106_, 2, v_inst_2098_);
lean_closure_set(v___f_2106_, 3, v_inst_2099_);
v___x_2107_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_2098_, v_inst_2100_, v_inst_2101_, v_n_2103_);
v___x_2108_ = lean_apply_4(v_toBind_2105_, lean_box(0), lean_box(0), v___x_2107_, v___f_2106_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object* v_m_2109_, lean_object* v_inst_2110_, lean_object* v_inst_2111_, lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_stx_2114_, lean_object* v_n_2115_, lean_object* v_expectedType_x3f_2116_){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Lean_Elab_addConstInfo___redArg(v_inst_2110_, v_inst_2111_, v_inst_2112_, v_inst_2113_, v_stx_2114_, v_n_2115_, v_expectedType_x3f_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v___x_2121_; lean_object* v_infoState_2122_; uint8_t v_enabled_2123_; 
v___x_2121_ = lean_st_ref_get(v___y_2119_);
v_infoState_2122_ = lean_ctor_get(v___x_2121_, 8);
lean_inc_ref(v_infoState_2122_);
lean_dec(v___x_2121_);
v_enabled_2123_ = lean_ctor_get_uint8(v_infoState_2122_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2122_);
if (v_enabled_2123_ == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_dec_ref(v_t_2118_);
v___x_2124_ = lean_box(0);
v___x_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
return v___x_2125_;
}
else
{
lean_object* v___x_2126_; lean_object* v_infoState_2127_; lean_object* v_env_2128_; lean_object* v_nextMacroScope_2129_; lean_object* v_ngen_2130_; lean_object* v_auxDeclNGen_2131_; lean_object* v_traceState_2132_; lean_object* v_cache_2133_; lean_object* v_recordedDeps_2134_; lean_object* v_messages_2135_; lean_object* v_snapshotTasks_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2158_; 
v___x_2126_ = lean_st_ref_take(v___y_2119_);
v_infoState_2127_ = lean_ctor_get(v___x_2126_, 8);
v_env_2128_ = lean_ctor_get(v___x_2126_, 0);
v_nextMacroScope_2129_ = lean_ctor_get(v___x_2126_, 1);
v_ngen_2130_ = lean_ctor_get(v___x_2126_, 2);
v_auxDeclNGen_2131_ = lean_ctor_get(v___x_2126_, 3);
v_traceState_2132_ = lean_ctor_get(v___x_2126_, 4);
v_cache_2133_ = lean_ctor_get(v___x_2126_, 5);
v_recordedDeps_2134_ = lean_ctor_get(v___x_2126_, 6);
v_messages_2135_ = lean_ctor_get(v___x_2126_, 7);
v_snapshotTasks_2136_ = lean_ctor_get(v___x_2126_, 9);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2138_ = v___x_2126_;
v_isShared_2139_ = v_isSharedCheck_2158_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_snapshotTasks_2136_);
lean_inc(v_infoState_2127_);
lean_inc(v_messages_2135_);
lean_inc(v_recordedDeps_2134_);
lean_inc(v_cache_2133_);
lean_inc(v_traceState_2132_);
lean_inc(v_auxDeclNGen_2131_);
lean_inc(v_ngen_2130_);
lean_inc(v_nextMacroScope_2129_);
lean_inc(v_env_2128_);
lean_dec(v___x_2126_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2158_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
uint8_t v_enabled_2140_; lean_object* v_assignment_2141_; lean_object* v_lazyAssignment_2142_; lean_object* v_trees_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2157_; 
v_enabled_2140_ = lean_ctor_get_uint8(v_infoState_2127_, sizeof(void*)*3);
v_assignment_2141_ = lean_ctor_get(v_infoState_2127_, 0);
v_lazyAssignment_2142_ = lean_ctor_get(v_infoState_2127_, 1);
v_trees_2143_ = lean_ctor_get(v_infoState_2127_, 2);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_infoState_2127_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2145_ = v_infoState_2127_;
v_isShared_2146_ = v_isSharedCheck_2157_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_trees_2143_);
lean_inc(v_lazyAssignment_2142_);
lean_inc(v_assignment_2141_);
lean_dec(v_infoState_2127_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2157_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2147_ = lean_box(0);
v___x_2148_ = l_Lean_PersistentArray_push___redArg(v_trees_2143_, v_t_2118_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 2, v___x_2148_);
v___x_2150_ = v___x_2145_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_assignment_2141_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_lazyAssignment_2142_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v___x_2148_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*3, v_enabled_2140_);
v___x_2150_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2152_; 
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 8, v___x_2150_);
v___x_2152_ = v___x_2138_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_env_2128_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_nextMacroScope_2129_);
lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_ngen_2130_);
lean_ctor_set(v_reuseFailAlloc_2155_, 3, v_auxDeclNGen_2131_);
lean_ctor_set(v_reuseFailAlloc_2155_, 4, v_traceState_2132_);
lean_ctor_set(v_reuseFailAlloc_2155_, 5, v_cache_2133_);
lean_ctor_set(v_reuseFailAlloc_2155_, 6, v_recordedDeps_2134_);
lean_ctor_set(v_reuseFailAlloc_2155_, 7, v_messages_2135_);
lean_ctor_set(v_reuseFailAlloc_2155_, 8, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2155_, 9, v_snapshotTasks_2136_);
v___x_2152_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = lean_st_ref_put(v___y_2119_, v___x_2152_);
v___x_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2147_);
return v___x_2154_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2159_, v___y_2160_);
lean_dec(v___y_2160_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object* v_t_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v___x_2167_; lean_object* v_infoState_2168_; uint8_t v_enabled_2169_; 
v___x_2167_ = lean_st_ref_get(v___y_2165_);
v_infoState_2168_ = lean_ctor_get(v___x_2167_, 8);
lean_inc_ref(v_infoState_2168_);
lean_dec(v___x_2167_);
v_enabled_2169_ = lean_ctor_get_uint8(v_infoState_2168_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2168_);
if (v_enabled_2169_ == 0)
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
lean_dec_ref(v_t_2163_);
v___x_2170_ = lean_box(0);
v___x_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
return v___x_2171_;
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2172_ = lean_unsigned_to_nat(32u);
v___x_2173_ = lean_mk_empty_array_with_capacity(v___x_2172_);
lean_dec_ref(v___x_2173_);
v___x_2174_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2175_, 0, v_t_2163_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
v___x_2176_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v___x_2175_, v___y_2165_);
return v___x_2176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object* v_t_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
return v_res_2181_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
return v___x_2183_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2184_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2185_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2186_ = lean_unsigned_to_nat(0u);
v___x_2187_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
lean_ctor_set(v___x_2187_, 2, v___x_2186_);
lean_ctor_set(v___x_2187_, 3, v___x_2186_);
lean_ctor_set(v___x_2187_, 4, v___x_2185_);
lean_ctor_set(v___x_2187_, 5, v___x_2185_);
lean_ctor_set(v___x_2187_, 6, v___x_2185_);
lean_ctor_set(v___x_2187_, 7, v___x_2185_);
lean_ctor_set(v___x_2187_, 8, v___x_2185_);
lean_ctor_set(v___x_2187_, 9, v___x_2185_);
lean_ctor_set(v___x_2187_, 10, v___x_2185_);
lean_ctor_set(v___x_2187_, 11, v___x_2184_);
return v___x_2187_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2188_ = lean_box(1);
v___x_2189_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_2190_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
lean_ctor_set(v___x_2191_, 1, v___x_2189_);
lean_ctor_set(v___x_2191_, 2, v___x_2188_);
return v___x_2191_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3));
v___x_2194_ = l_Lean_stringToMessageData(v___x_2193_);
return v___x_2194_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5));
v___x_2197_ = l_Lean_stringToMessageData(v___x_2196_);
return v___x_2197_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8(void){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7));
v___x_2200_ = l_Lean_stringToMessageData(v___x_2199_);
return v___x_2200_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9));
v___x_2203_ = l_Lean_stringToMessageData(v___x_2202_);
return v___x_2203_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11));
v___x_2206_ = l_Lean_stringToMessageData(v___x_2205_);
return v___x_2206_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13));
v___x_2209_ = l_Lean_stringToMessageData(v___x_2208_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15));
v___x_2212_ = l_Lean_stringToMessageData(v___x_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_2213_, lean_object* v_declHint_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v_env_2219_; uint8_t v___x_2220_; 
v___x_2217_ = lean_box(0);
v___x_2218_ = lean_st_ref_get(v___y_2215_);
v_env_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc_ref(v_env_2219_);
lean_dec(v___x_2218_);
v___x_2220_ = l_Lean_Name_isAnonymous(v_declHint_2214_);
if (v___x_2220_ == 0)
{
uint8_t v_isExporting_2221_; 
v_isExporting_2221_ = lean_ctor_get_uint8(v_env_2219_, sizeof(void*)*13);
if (v_isExporting_2221_ == 0)
{
lean_object* v___x_2222_; 
lean_dec_ref(v_env_2219_);
lean_dec(v_declHint_2214_);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v_msg_2213_);
return v___x_2222_;
}
else
{
lean_object* v___x_2223_; uint8_t v___x_2224_; 
lean_inc_ref(v_env_2219_);
v___x_2223_ = l_Lean_Environment_setExporting(v_env_2219_, v___x_2220_);
lean_inc(v_declHint_2214_);
lean_inc_ref(v___x_2223_);
v___x_2224_ = l_Lean_Environment_contains(v___x_2223_, v_declHint_2214_, v_isExporting_2221_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; 
lean_dec_ref(v___x_2223_);
lean_dec_ref(v_env_2219_);
lean_dec(v_declHint_2214_);
v___x_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2225_, 0, v_msg_2213_);
return v___x_2225_;
}
else
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v_c_2231_; lean_object* v___x_2232_; 
v___x_2226_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2227_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_2228_ = l_Lean_Options_empty;
v___x_2229_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2223_);
lean_ctor_set(v___x_2229_, 1, v___x_2226_);
lean_ctor_set(v___x_2229_, 2, v___x_2227_);
lean_ctor_set(v___x_2229_, 3, v___x_2228_);
lean_inc(v_declHint_2214_);
v___x_2230_ = l_Lean_MessageData_ofConstName(v_declHint_2214_, v___x_2220_);
v_c_2231_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2231_, 0, v___x_2229_);
lean_ctor_set(v_c_2231_, 1, v___x_2230_);
v___x_2232_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2219_, v_declHint_2214_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_dec_ref(v_env_2219_);
lean_dec(v_declHint_2214_);
v___x_2233_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
lean_ctor_set(v___x_2234_, 1, v_c_2231_);
v___x_2235_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6);
v___x_2236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2234_);
lean_ctor_set(v___x_2236_, 1, v___x_2235_);
v___x_2237_ = l_Lean_MessageData_note(v___x_2236_);
v___x_2238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2238_, 0, v_msg_2213_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
return v___x_2239_;
}
else
{
lean_object* v_val_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2274_; 
v_val_2240_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2242_ = v___x_2232_;
v_isShared_2243_ = v_isSharedCheck_2274_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_val_2240_);
lean_dec(v___x_2232_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2274_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2244_; lean_object* v_moduleNames_2245_; lean_object* v_mod_2246_; uint8_t v___x_2247_; 
v___x_2244_ = l_Lean_Environment_header(v_env_2219_);
lean_dec_ref(v_env_2219_);
v_moduleNames_2245_ = lean_ctor_get(v___x_2244_, 4);
lean_inc_ref(v_moduleNames_2245_);
lean_dec_ref(v___x_2244_);
v_mod_2246_ = lean_array_get(v___x_2217_, v_moduleNames_2245_, v_val_2240_);
lean_dec(v_val_2240_);
lean_dec_ref(v_moduleNames_2245_);
v___x_2247_ = l_Lean_isPrivateName(v_declHint_2214_);
lean_dec(v_declHint_2214_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2248_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8);
v___x_2249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
lean_ctor_set(v___x_2249_, 1, v_c_2231_);
v___x_2250_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10);
v___x_2251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2249_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
v___x_2252_ = l_Lean_MessageData_ofName(v_mod_2246_);
v___x_2253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2251_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12);
v___x_2255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2253_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = l_Lean_MessageData_note(v___x_2255_);
v___x_2257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2257_, 0, v_msg_2213_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
if (v_isShared_2243_ == 0)
{
lean_ctor_set_tag(v___x_2242_, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2257_);
v___x_2259_ = v___x_2242_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2257_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
else
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2272_; 
v___x_2261_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
lean_ctor_set(v___x_2262_, 1, v_c_2231_);
v___x_2263_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14);
v___x_2264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2262_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
v___x_2265_ = l_Lean_MessageData_ofName(v_mod_2246_);
v___x_2266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16);
v___x_2268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2266_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
v___x_2269_ = l_Lean_MessageData_note(v___x_2268_);
v___x_2270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2270_, 0, v_msg_2213_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
if (v_isShared_2243_ == 0)
{
lean_ctor_set_tag(v___x_2242_, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2270_);
v___x_2272_ = v___x_2242_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2275_; 
lean_dec_ref(v_env_2219_);
lean_dec(v_declHint_2214_);
v___x_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2275_, 0, v_msg_2213_);
return v___x_2275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_2276_, lean_object* v_declHint_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2276_, v_declHint_2277_, v___y_2278_);
lean_dec(v___y_2278_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_2281_, lean_object* v_declHint_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v___x_2286_; lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2296_; 
v___x_2286_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2281_, v_declHint_2282_, v___y_2284_);
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2289_ = v___x_2286_;
v_isShared_2290_ = v_isSharedCheck_2296_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2286_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2296_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2294_; 
v___x_2291_ = l_Lean_unknownIdentifierMessageTag;
v___x_2292_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
lean_ctor_set(v___x_2292_, 1, v_a_2287_);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 0, v___x_2292_);
v___x_2294_ = v___x_2289_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2292_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_2297_, lean_object* v_declHint_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2297_, v_declHint_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object* v_msgData_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; lean_object* v_toCold_2308_; lean_object* v_env_2309_; lean_object* v_options_2310_; uint8_t v___x_2311_; lean_object* v_env_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2307_ = lean_st_ref_get(v___y_2305_);
v_toCold_2308_ = lean_ctor_get(v___y_2304_, 0);
v_env_2309_ = lean_ctor_get(v___x_2307_, 0);
lean_inc_ref(v_env_2309_);
lean_dec(v___x_2307_);
v_options_2310_ = lean_ctor_get(v_toCold_2308_, 2);
v___x_2311_ = 0;
v_env_2312_ = l_Lean_Environment_setRecordingDeps(v_env_2309_, v___x_2311_);
v___x_2313_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2314_ = lean_unsigned_to_nat(32u);
v___x_2315_ = lean_mk_empty_array_with_capacity(v___x_2314_);
lean_dec_ref(v___x_2315_);
v___x_2316_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
lean_inc_ref(v_options_2310_);
v___x_2317_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2317_, 0, v_env_2312_);
lean_ctor_set(v___x_2317_, 1, v___x_2313_);
lean_ctor_set(v___x_2317_, 2, v___x_2316_);
lean_ctor_set(v___x_2317_, 3, v_options_2310_);
v___x_2318_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
lean_ctor_set(v___x_2318_, 1, v_msgData_2303_);
v___x_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object* v_msgData_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v_ref_2329_; lean_object* v___x_2330_; lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2339_; 
v_ref_2329_ = lean_ctor_get(v___y_2326_, 2);
v___x_2330_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_2325_, v___y_2326_, v___y_2327_);
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_2339_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2339_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; lean_object* v___x_2337_; 
lean_inc(v_ref_2329_);
v___x_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2335_, 0, v_ref_2329_);
lean_ctor_set(v___x_2335_, 1, v_a_2331_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set_tag(v___x_2333_, 1);
lean_ctor_set(v___x_2333_, 0, v___x_2335_);
v___x_2337_ = v___x_2333_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_2345_, lean_object* v_msg_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v_toCold_2350_; lean_object* v_currRecDepth_2351_; lean_object* v_ref_2352_; uint16_t v_optionFlags_2353_; uint8_t v_suppressElabErrors_2354_; uint8_t v_isRecordingDeps_2355_; lean_object* v_ref_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v_toCold_2350_ = lean_ctor_get(v___y_2347_, 0);
v_currRecDepth_2351_ = lean_ctor_get(v___y_2347_, 1);
v_ref_2352_ = lean_ctor_get(v___y_2347_, 2);
v_optionFlags_2353_ = lean_ctor_get_uint16(v___y_2347_, sizeof(void*)*3);
v_suppressElabErrors_2354_ = lean_ctor_get_uint8(v___y_2347_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2355_ = lean_ctor_get_uint8(v___y_2347_, sizeof(void*)*3 + 3);
v_ref_2356_ = l_Lean_replaceRef(v_ref_2345_, v_ref_2352_);
lean_inc(v_currRecDepth_2351_);
lean_inc_ref(v_toCold_2350_);
v___x_2357_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2357_, 0, v_toCold_2350_);
lean_ctor_set(v___x_2357_, 1, v_currRecDepth_2351_);
lean_ctor_set(v___x_2357_, 2, v_ref_2356_);
lean_ctor_set_uint16(v___x_2357_, sizeof(void*)*3, v_optionFlags_2353_);
lean_ctor_set_uint8(v___x_2357_, sizeof(void*)*3 + 2, v_suppressElabErrors_2354_);
lean_ctor_set_uint8(v___x_2357_, sizeof(void*)*3 + 3, v_isRecordingDeps_2355_);
v___x_2358_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2346_, v___x_2357_, v___y_2348_);
lean_dec_ref_known(v___x_2357_, 3);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_2359_, lean_object* v_msg_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2359_, v_msg_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v_ref_2359_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_2365_, lean_object* v_msg_2366_, lean_object* v_declHint_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v___x_2371_; lean_object* v_a_2372_; lean_object* v___x_2373_; 
v___x_2371_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2366_, v_declHint_2367_, v___y_2368_, v___y_2369_);
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref(v___x_2371_);
v___x_2373_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2365_, v_a_2372_, v___y_2368_, v___y_2369_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2374_, lean_object* v_msg_2375_, lean_object* v_declHint_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2374_, v_msg_2375_, v_declHint_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v_ref_2374_);
return v_res_2380_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_2383_ = l_Lean_stringToMessageData(v___x_2382_);
return v___x_2383_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2));
v___x_2386_ = l_Lean_stringToMessageData(v___x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_2387_, lean_object* v_constName_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v___x_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2392_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_2393_ = 0;
lean_inc(v_constName_2388_);
v___x_2394_ = l_Lean_MessageData_ofConstName(v_constName_2388_, v___x_2393_);
v___x_2395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2392_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_2397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2395_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
v___x_2398_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2387_, v___x_2397_, v_constName_2388_, v___y_2389_, v___y_2390_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2399_, lean_object* v_constName_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2399_, v_constName_2400_, v___y_2401_, v___y_2402_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v_ref_2399_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_ref_2409_; lean_object* v___x_2410_; 
v_ref_2409_ = lean_ctor_get(v___y_2406_, 2);
v___x_2410_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2409_, v_constName_2405_, v___y_2406_, v___y_2407_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2411_, v___y_2412_, v___y_2413_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object* v_constName_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___x_2420_; lean_object* v_env_2421_; uint8_t v___x_2422_; lean_object* v___x_2423_; 
v___x_2420_ = lean_st_ref_get(v___y_2418_);
v_env_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc_ref(v_env_2421_);
lean_dec(v___x_2420_);
v___x_2422_ = 0;
lean_inc(v_constName_2416_);
v___x_2423_ = l_Lean_Environment_findConstVal_x3f(v_env_2421_, v_constName_2416_, v___x_2422_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2416_, v___y_2417_, v___y_2418_);
return v___x_2424_;
}
else
{
lean_object* v_val_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec(v_constName_2416_);
v_val_2425_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2423_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_val_2425_);
lean_dec(v___x_2423_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
lean_ctor_set_tag(v___x_2427_, 0);
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_val_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2433_, v___y_2434_, v___y_2435_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object* v_a_2438_, lean_object* v_a_2439_){
_start:
{
if (lean_obj_tag(v_a_2438_) == 0)
{
lean_object* v___x_2440_; 
v___x_2440_ = l_List_reverse___redArg(v_a_2439_);
return v___x_2440_;
}
else
{
lean_object* v_head_2441_; lean_object* v_tail_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2451_; 
v_head_2441_ = lean_ctor_get(v_a_2438_, 0);
v_tail_2442_ = lean_ctor_get(v_a_2438_, 1);
v_isSharedCheck_2451_ = !lean_is_exclusive(v_a_2438_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2444_ = v_a_2438_;
v_isShared_2445_ = v_isSharedCheck_2451_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_tail_2442_);
lean_inc(v_head_2441_);
lean_dec(v_a_2438_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2451_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2446_ = l_Lean_mkLevelParam(v_head_2441_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 1, v_a_2439_);
lean_ctor_set(v___x_2444_, 0, v___x_2446_);
v___x_2448_ = v___x_2444_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2450_, 1, v_a_2439_);
v___x_2448_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
v_a_2438_ = v_tail_2442_;
v_a_2439_ = v___x_2448_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object* v_constName_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v___x_2456_; 
lean_inc(v_constName_2452_);
v___x_2456_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2452_, v___y_2453_, v___y_2454_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2468_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2468_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2468_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v_levelParams_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
v_levelParams_2461_ = lean_ctor_get(v_a_2457_, 1);
lean_inc(v_levelParams_2461_);
lean_dec(v_a_2457_);
v___x_2462_ = lean_box(0);
v___x_2463_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_2461_, v___x_2462_);
v___x_2464_ = l_Lean_mkConst(v_constName_2452_, v___x_2463_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2464_);
v___x_2466_ = v___x_2459_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec(v_constName_2452_);
v_a_2469_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2456_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2456_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object* v_constName_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object* v_stx_2482_, lean_object* v_n_2483_, lean_object* v_expectedType_x3f_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v___x_2488_; 
v___x_2488_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_2483_, v___y_2485_, v___y_2486_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_a_2489_);
lean_dec_ref_known(v___x_2488_, 1);
v___x_2490_ = lean_box(0);
v___x_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
lean_ctor_set(v___x_2491_, 1, v_stx_2482_);
v___x_2492_ = l_Lean_LocalContext_empty;
v___x_2493_ = 0;
v___x_2494_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2494_, 0, v___x_2491_);
lean_ctor_set(v___x_2494_, 1, v___x_2492_);
lean_ctor_set(v___x_2494_, 2, v_expectedType_x3f_2484_);
lean_ctor_set(v___x_2494_, 3, v_a_2489_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*4, v___x_2493_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*4 + 1, v___x_2493_);
v___x_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
v___x_2496_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_2495_, v___y_2485_, v___y_2486_);
return v___x_2496_;
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_dec(v_expectedType_x3f_2484_);
lean_dec(v_stx_2482_);
v_a_2497_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2488_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2488_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object* v_stx_2505_, lean_object* v_n_2506_, lean_object* v_expectedType_x3f_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_2505_, v_n_2506_, v_expectedType_x3f_2507_, v___y_2508_, v___y_2509_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object* v_id_2512_, lean_object* v_expectedType_x3f_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_){
_start:
{
lean_object* v___x_2517_; 
lean_inc(v_id_2512_);
v___x_2517_ = l_Lean_realizeGlobalConstNoOverload(v_id_2512_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2545_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2545_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2545_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v_infoState_2523_; uint8_t v_enabled_2524_; 
v___x_2522_ = lean_st_ref_get(v_a_2515_);
v_infoState_2523_ = lean_ctor_get(v___x_2522_, 8);
lean_inc_ref(v_infoState_2523_);
lean_dec(v___x_2522_);
v_enabled_2524_ = lean_ctor_get_uint8(v_infoState_2523_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2523_);
if (v_enabled_2524_ == 0)
{
lean_object* v___x_2526_; 
lean_dec(v_expectedType_x3f_2513_);
lean_dec(v_id_2512_);
if (v_isShared_2521_ == 0)
{
v___x_2526_ = v___x_2520_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2518_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
else
{
lean_object* v___x_2528_; 
lean_del_object(v___x_2520_);
lean_inc(v_a_2518_);
v___x_2528_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2512_, v_a_2518_, v_expectedType_x3f_2513_, v_a_2514_, v_a_2515_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2535_ == 0)
{
lean_object* v_unused_2536_; 
v_unused_2536_ = lean_ctor_get(v___x_2528_, 0);
lean_dec(v_unused_2536_);
v___x_2530_ = v___x_2528_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_dec(v___x_2528_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 0, v_a_2518_);
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2518_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec(v_a_2518_);
v_a_2537_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2528_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2528_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2513_);
lean_dec(v_id_2512_);
return v___x_2517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object* v_id_2546_, lean_object* v_expectedType_x3f_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_2546_, v_expectedType_x3f_2547_, v_a_2548_, v_a_2549_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object* v_t_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2552_, v___y_2554_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_2557_, v___y_2558_, v___y_2559_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2562_, lean_object* v_constName_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2563_, v___y_2564_, v___y_2565_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2568_, lean_object* v_constName_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2568_, v_constName_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2574_, lean_object* v_ref_2575_, lean_object* v_constName_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2575_, v_constName_2576_, v___y_2577_, v___y_2578_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2581_, lean_object* v_ref_2582_, lean_object* v_constName_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_2581_, v_ref_2582_, v_constName_2583_, v___y_2584_, v___y_2585_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v_ref_2582_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2588_, lean_object* v_ref_2589_, lean_object* v_msg_2590_, lean_object* v_declHint_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v___x_2595_; 
v___x_2595_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2589_, v_msg_2590_, v_declHint_2591_, v___y_2592_, v___y_2593_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2596_, lean_object* v_ref_2597_, lean_object* v_msg_2598_, lean_object* v_declHint_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_2596_, v_ref_2597_, v_msg_2598_, v_declHint_2599_, v___y_2600_, v___y_2601_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v_ref_2597_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_2604_, lean_object* v_declHint_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2604_, v_declHint_2605_, v___y_2607_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2610_, lean_object* v_declHint_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2610_, v_declHint_2611_, v___y_2612_, v___y_2613_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_2616_, lean_object* v_ref_2617_, lean_object* v_msg_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2617_, v_msg_2618_, v___y_2619_, v___y_2620_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2623_, lean_object* v_ref_2624_, lean_object* v_msg_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_2623_, v_ref_2624_, v_msg_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v_ref_2624_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_2630_, lean_object* v_msg_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2631_, v___y_2632_, v___y_2633_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_2636_, lean_object* v_msg_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_2636_, v_msg_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object* v_id_2642_, lean_object* v_expectedType_x3f_2643_, lean_object* v_as_x27_2644_, lean_object* v_b_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
if (lean_obj_tag(v_as_x27_2644_) == 0)
{
lean_object* v___x_2649_; 
lean_dec(v_expectedType_x3f_2643_);
lean_dec(v_id_2642_);
v___x_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2649_, 0, v_b_2645_);
return v___x_2649_;
}
else
{
lean_object* v_head_2650_; lean_object* v_tail_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v_head_2650_ = lean_ctor_get(v_as_x27_2644_, 0);
v_tail_2651_ = lean_ctor_get(v_as_x27_2644_, 1);
v___x_2652_ = lean_box(0);
lean_inc(v_expectedType_x3f_2643_);
lean_inc(v_head_2650_);
lean_inc(v_id_2642_);
v___x_2653_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2642_, v_head_2650_, v_expectedType_x3f_2643_, v___y_2646_, v___y_2647_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_dec_ref_known(v___x_2653_, 1);
v_as_x27_2644_ = v_tail_2651_;
v_b_2645_ = v___x_2652_;
goto _start;
}
else
{
lean_dec(v_expectedType_x3f_2643_);
lean_dec(v_id_2642_);
return v___x_2653_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object* v_id_2655_, lean_object* v_expectedType_x3f_2656_, lean_object* v_as_x27_2657_, lean_object* v_b_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2655_, v_expectedType_x3f_2656_, v_as_x27_2657_, v_b_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v_as_x27_2657_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object* v_id_2663_, lean_object* v_expectedType_x3f_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_){
_start:
{
lean_object* v___x_2668_; 
lean_inc(v_id_2663_);
v___x_2668_ = l_Lean_realizeGlobalConst(v_id_2663_, v_a_2665_, v_a_2666_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2697_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2671_ = v___x_2668_;
v_isShared_2672_ = v_isSharedCheck_2697_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2668_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2697_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2673_; lean_object* v_infoState_2674_; uint8_t v_enabled_2675_; 
v___x_2673_ = lean_st_ref_get(v_a_2666_);
v_infoState_2674_ = lean_ctor_get(v___x_2673_, 8);
lean_inc_ref(v_infoState_2674_);
lean_dec(v___x_2673_);
v_enabled_2675_ = lean_ctor_get_uint8(v_infoState_2674_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2674_);
if (v_enabled_2675_ == 0)
{
lean_object* v___x_2677_; 
lean_dec(v_expectedType_x3f_2664_);
lean_dec(v_id_2663_);
if (v_isShared_2672_ == 0)
{
v___x_2677_ = v___x_2671_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2669_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
else
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
lean_del_object(v___x_2671_);
v___x_2679_ = lean_box(0);
v___x_2680_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2663_, v_expectedType_x3f_2664_, v_a_2669_, v___x_2679_, v_a_2665_, v_a_2666_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2687_ == 0)
{
lean_object* v_unused_2688_; 
v_unused_2688_ = lean_ctor_get(v___x_2680_, 0);
lean_dec(v_unused_2688_);
v___x_2682_ = v___x_2680_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_dec(v___x_2680_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 0, v_a_2669_);
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2669_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec(v_a_2669_);
v_a_2689_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2680_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2680_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2664_);
lean_dec(v_id_2663_);
return v___x_2668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object* v_id_2698_, lean_object* v_expectedType_x3f_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_2698_, v_expectedType_x3f_2699_, v_a_2700_, v_a_2701_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object* v_id_2704_, lean_object* v_expectedType_x3f_2705_, lean_object* v_as_2706_, lean_object* v_as_x27_2707_, lean_object* v_b_2708_, lean_object* v_a_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2704_, v_expectedType_x3f_2705_, v_as_x27_2707_, v_b_2708_, v___y_2710_, v___y_2711_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object* v_id_2714_, lean_object* v_expectedType_x3f_2715_, lean_object* v_as_2716_, lean_object* v_as_x27_2717_, lean_object* v_b_2718_, lean_object* v_a_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_2714_, v_expectedType_x3f_2715_, v_as_2716_, v_as_x27_2717_, v_b_2718_, v_a_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v_as_x27_2717_);
lean_dec(v_as_2716_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object* v_ref_2724_, lean_object* v_as_x27_2725_, lean_object* v_b_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
if (lean_obj_tag(v_as_x27_2725_) == 0)
{
lean_object* v___x_2730_; 
lean_dec(v_ref_2724_);
v___x_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2730_, 0, v_b_2726_);
return v___x_2730_;
}
else
{
lean_object* v_head_2731_; lean_object* v_tail_2732_; lean_object* v_fst_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v_head_2731_ = lean_ctor_get(v_as_x27_2725_, 0);
v_tail_2732_ = lean_ctor_get(v_as_x27_2725_, 1);
v_fst_2733_ = lean_ctor_get(v_head_2731_, 0);
v___x_2734_ = lean_box(0);
v___x_2735_ = lean_box(0);
lean_inc(v_fst_2733_);
lean_inc(v_ref_2724_);
v___x_2736_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_2724_, v_fst_2733_, v___x_2735_, v___y_2727_, v___y_2728_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_dec_ref_known(v___x_2736_, 1);
v_as_x27_2725_ = v_tail_2732_;
v_b_2726_ = v___x_2734_;
goto _start;
}
else
{
lean_dec(v_ref_2724_);
return v___x_2736_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object* v_ref_2738_, lean_object* v_as_x27_2739_, lean_object* v_b_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2738_, v_as_x27_2739_, v_b_2740_, v___y_2741_, v___y_2742_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v_as_x27_2739_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object* v_ref_2745_, lean_object* v_id_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_realizeGlobalName(v_id_2746_, v_a_2747_, v_a_2748_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2779_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2779_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2779_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v_infoState_2756_; uint8_t v_enabled_2757_; 
v___x_2755_ = lean_st_ref_get(v_a_2748_);
v_infoState_2756_ = lean_ctor_get(v___x_2755_, 8);
lean_inc_ref(v_infoState_2756_);
lean_dec(v___x_2755_);
v_enabled_2757_ = lean_ctor_get_uint8(v_infoState_2756_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2756_);
if (v_enabled_2757_ == 0)
{
lean_object* v___x_2759_; 
lean_dec(v_ref_2745_);
if (v_isShared_2754_ == 0)
{
v___x_2759_ = v___x_2753_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2751_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
else
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_del_object(v___x_2753_);
v___x_2761_ = lean_box(0);
v___x_2762_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2745_, v_a_2751_, v___x_2761_, v_a_2747_, v_a_2748_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2769_ == 0)
{
lean_object* v_unused_2770_; 
v_unused_2770_ = lean_ctor_get(v___x_2762_, 0);
lean_dec(v_unused_2770_);
v___x_2764_ = v___x_2762_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_dec(v___x_2762_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v_a_2751_);
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2751_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec(v_a_2751_);
v_a_2771_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2762_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2762_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
}
else
{
lean_dec(v_ref_2745_);
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object* v_ref_2780_, lean_object* v_id_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_2780_, v_id_2781_, v_a_2782_, v_a_2783_);
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2782_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object* v_ref_2786_, lean_object* v_as_2787_, lean_object* v_as_x27_2788_, lean_object* v_b_2789_, lean_object* v_a_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2786_, v_as_x27_2788_, v_b_2789_, v___y_2791_, v___y_2792_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object* v_ref_2795_, lean_object* v_as_2796_, lean_object* v_as_x27_2797_, lean_object* v_b_2798_, lean_object* v_a_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_2795_, v_as_2796_, v_as_x27_2797_, v_b_2798_, v_a_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v_as_x27_2797_);
lean_dec(v_as_2796_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object* v_self_2804_){
_start:
{
lean_object* v_fst_2805_; 
v_fst_2805_ = lean_ctor_get(v_self_2804_, 0);
lean_inc(v_fst_2805_);
return v_fst_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object* v_self_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_2806_);
lean_dec_ref(v_self_2806_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object* v_info_2808_, lean_object* v_treesSaved_2809_, lean_object* v_s_2810_){
_start:
{
if (lean_obj_tag(v_info_2808_) == 0)
{
uint8_t v_enabled_2811_; lean_object* v_assignment_2812_; lean_object* v_lazyAssignment_2813_; lean_object* v_trees_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2824_; 
v_enabled_2811_ = lean_ctor_get_uint8(v_s_2810_, sizeof(void*)*3);
v_assignment_2812_ = lean_ctor_get(v_s_2810_, 0);
v_lazyAssignment_2813_ = lean_ctor_get(v_s_2810_, 1);
v_trees_2814_ = lean_ctor_get(v_s_2810_, 2);
v_isSharedCheck_2824_ = !lean_is_exclusive(v_s_2810_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2816_ = v_s_2810_;
v_isShared_2817_ = v_isSharedCheck_2824_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_trees_2814_);
lean_inc(v_lazyAssignment_2813_);
lean_inc(v_assignment_2812_);
lean_dec(v_s_2810_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2824_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v_val_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2822_; 
v_val_2818_ = lean_ctor_get(v_info_2808_, 0);
lean_inc(v_val_2818_);
lean_dec_ref_known(v_info_2808_, 1);
v___x_2819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2819_, 0, v_val_2818_);
lean_ctor_set(v___x_2819_, 1, v_trees_2814_);
v___x_2820_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2809_, v___x_2819_);
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 2, v___x_2820_);
v___x_2822_ = v___x_2816_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_assignment_2812_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v_lazyAssignment_2813_);
lean_ctor_set(v_reuseFailAlloc_2823_, 2, v___x_2820_);
lean_ctor_set_uint8(v_reuseFailAlloc_2823_, sizeof(void*)*3, v_enabled_2811_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
else
{
uint8_t v_enabled_2825_; lean_object* v_assignment_2826_; lean_object* v_lazyAssignment_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2843_; 
v_enabled_2825_ = lean_ctor_get_uint8(v_s_2810_, sizeof(void*)*3);
v_assignment_2826_ = lean_ctor_get(v_s_2810_, 0);
v_lazyAssignment_2827_ = lean_ctor_get(v_s_2810_, 1);
v_isSharedCheck_2843_ = !lean_is_exclusive(v_s_2810_);
if (v_isSharedCheck_2843_ == 0)
{
lean_object* v_unused_2844_; 
v_unused_2844_ = lean_ctor_get(v_s_2810_, 2);
lean_dec(v_unused_2844_);
v___x_2829_ = v_s_2810_;
v_isShared_2830_ = v_isSharedCheck_2843_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_lazyAssignment_2827_);
lean_inc(v_assignment_2826_);
lean_dec(v_s_2810_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2843_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v_val_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2842_; 
v_val_2831_ = lean_ctor_get(v_info_2808_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_info_2808_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2833_ = v_info_2808_;
v_isShared_2834_ = v_isSharedCheck_2842_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_val_2831_);
lean_dec(v_info_2808_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2842_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
lean_ctor_set_tag(v___x_2833_, 2);
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_val_2831_);
v___x_2836_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
lean_object* v___x_2837_; lean_object* v___x_2839_; 
v___x_2837_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2809_, v___x_2836_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 2, v___x_2837_);
v___x_2839_ = v___x_2829_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_assignment_2826_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_lazyAssignment_2827_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v___x_2837_);
lean_ctor_set_uint8(v_reuseFailAlloc_2840_, sizeof(void*)*3, v_enabled_2825_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object* v_treesSaved_2845_, lean_object* v_modifyInfoState_2846_, lean_object* v_info_2847_){
_start:
{
lean_object* v___f_2848_; lean_object* v___x_2849_; 
v___f_2848_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2848_, 0, v_info_2847_);
lean_closure_set(v___f_2848_, 1, v_treesSaved_2845_);
v___x_2849_ = lean_apply_1(v_modifyInfoState_2846_, v___f_2848_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object* v___f_2850_, lean_object* v_info_2851_){
_start:
{
lean_object* v___x_2852_; 
v___x_2852_ = lean_apply_1(v___f_2850_, v_info_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object* v_toPure_2853_, lean_object* v_toBind_2854_, lean_object* v___f_2855_, lean_object* v_____do__lift_2856_){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2857_, 0, v_____do__lift_2856_);
v___x_2858_ = lean_apply_2(v_toPure_2853_, lean_box(0), v___x_2857_);
v___x_2859_ = lean_apply_4(v_toBind_2854_, lean_box(0), lean_box(0), v___x_2858_, v___f_2855_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object* v_toBind_2860_, lean_object* v_mkInfoOnError_2861_, lean_object* v___f_2862_, lean_object* v_mkInfo_2863_, lean_object* v___f_2864_, lean_object* v_a_x3f_2865_){
_start:
{
if (lean_obj_tag(v_a_x3f_2865_) == 0)
{
lean_object* v___x_2866_; 
lean_dec(v___f_2864_);
lean_dec(v_mkInfo_2863_);
v___x_2866_ = lean_apply_4(v_toBind_2860_, lean_box(0), lean_box(0), v_mkInfoOnError_2861_, v___f_2862_);
return v___x_2866_;
}
else
{
lean_object* v_val_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
lean_dec(v___f_2862_);
lean_dec(v_mkInfoOnError_2861_);
v_val_2867_ = lean_ctor_get(v_a_x3f_2865_, 0);
lean_inc(v_val_2867_);
lean_dec_ref_known(v_a_x3f_2865_, 1);
v___x_2868_ = lean_apply_1(v_mkInfo_2863_, v_val_2867_);
v___x_2869_ = lean_apply_4(v_toBind_2860_, lean_box(0), lean_box(0), v___x_2868_, v___f_2864_);
return v___x_2869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object* v_toFunctor_2870_, lean_object* v_modifyInfoState_2871_, lean_object* v_toPure_2872_, lean_object* v_toBind_2873_, lean_object* v_mkInfoOnError_2874_, lean_object* v_mkInfo_2875_, lean_object* v_inst_2876_, lean_object* v_x_2877_, lean_object* v___f_2878_, lean_object* v_treesSaved_2879_){
_start:
{
lean_object* v_map_2880_; lean_object* v___f_2881_; lean_object* v___f_2882_; lean_object* v___f_2883_; lean_object* v___f_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_map_2880_ = lean_ctor_get(v_toFunctor_2870_, 0);
lean_inc(v_map_2880_);
lean_dec_ref(v_toFunctor_2870_);
v___f_2881_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2881_, 0, v_treesSaved_2879_);
lean_closure_set(v___f_2881_, 1, v_modifyInfoState_2871_);
v___f_2882_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2882_, 0, v___f_2881_);
lean_inc_ref(v___f_2882_);
lean_inc(v_toBind_2873_);
v___f_2883_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_2883_, 0, v_toPure_2872_);
lean_closure_set(v___f_2883_, 1, v_toBind_2873_);
lean_closure_set(v___f_2883_, 2, v___f_2882_);
v___f_2884_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__6), 6, 5);
lean_closure_set(v___f_2884_, 0, v_toBind_2873_);
lean_closure_set(v___f_2884_, 1, v_mkInfoOnError_2874_);
lean_closure_set(v___f_2884_, 2, v___f_2883_);
lean_closure_set(v___f_2884_, 3, v_mkInfo_2875_);
lean_closure_set(v___f_2884_, 4, v___f_2882_);
v___x_2885_ = lean_apply_4(v_inst_2876_, lean_box(0), lean_box(0), v_x_2877_, v___f_2884_);
v___x_2886_ = lean_apply_4(v_map_2880_, lean_box(0), lean_box(0), v___f_2878_, v___x_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object* v_x_2887_, lean_object* v_inst_2888_, lean_object* v_inst_2889_, lean_object* v_toBind_2890_, lean_object* v___f_2891_, lean_object* v_____do__lift_2892_){
_start:
{
uint8_t v_enabled_2893_; 
v_enabled_2893_ = lean_ctor_get_uint8(v_____do__lift_2892_, sizeof(void*)*3);
if (v_enabled_2893_ == 0)
{
lean_dec(v___f_2891_);
lean_dec(v_toBind_2890_);
lean_dec_ref(v_inst_2889_);
lean_dec_ref(v_inst_2888_);
lean_inc(v_x_2887_);
return v_x_2887_;
}
else
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2888_, v_inst_2889_);
v___x_2895_ = lean_apply_4(v_toBind_2890_, lean_box(0), lean_box(0), v___x_2894_, v___f_2891_);
return v___x_2895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object* v_x_2896_, lean_object* v_inst_2897_, lean_object* v_inst_2898_, lean_object* v_toBind_2899_, lean_object* v___f_2900_, lean_object* v_____do__lift_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__7(v_x_2896_, v_inst_2897_, v_inst_2898_, v_toBind_2899_, v___f_2900_, v_____do__lift_2901_);
lean_dec_ref(v_____do__lift_2901_);
lean_dec(v_x_2896_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object* v_inst_2904_, lean_object* v_inst_2905_, lean_object* v_inst_2906_, lean_object* v_x_2907_, lean_object* v_mkInfo_2908_, lean_object* v_mkInfoOnError_2909_){
_start:
{
lean_object* v_toApplicative_2910_; lean_object* v_toBind_2911_; lean_object* v_getInfoState_2912_; lean_object* v_modifyInfoState_2913_; lean_object* v_toFunctor_2914_; lean_object* v_toPure_2915_; lean_object* v___f_2916_; lean_object* v___f_2917_; lean_object* v___f_2918_; lean_object* v___x_2919_; 
v_toApplicative_2910_ = lean_ctor_get(v_inst_2904_, 0);
v_toBind_2911_ = lean_ctor_get(v_inst_2904_, 1);
lean_inc_n(v_toBind_2911_, 3);
v_getInfoState_2912_ = lean_ctor_get(v_inst_2905_, 0);
lean_inc(v_getInfoState_2912_);
v_modifyInfoState_2913_ = lean_ctor_get(v_inst_2905_, 1);
v_toFunctor_2914_ = lean_ctor_get(v_toApplicative_2910_, 0);
v_toPure_2915_ = lean_ctor_get(v_toApplicative_2910_, 1);
v___f_2916_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2907_);
lean_inc(v_toPure_2915_);
lean_inc(v_modifyInfoState_2913_);
lean_inc_ref(v_toFunctor_2914_);
v___f_2917_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__5), 10, 9);
lean_closure_set(v___f_2917_, 0, v_toFunctor_2914_);
lean_closure_set(v___f_2917_, 1, v_modifyInfoState_2913_);
lean_closure_set(v___f_2917_, 2, v_toPure_2915_);
lean_closure_set(v___f_2917_, 3, v_toBind_2911_);
lean_closure_set(v___f_2917_, 4, v_mkInfoOnError_2909_);
lean_closure_set(v___f_2917_, 5, v_mkInfo_2908_);
lean_closure_set(v___f_2917_, 6, v_inst_2906_);
lean_closure_set(v___f_2917_, 7, v_x_2907_);
lean_closure_set(v___f_2917_, 8, v___f_2916_);
v___f_2918_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2918_, 0, v_x_2907_);
lean_closure_set(v___f_2918_, 1, v_inst_2904_);
lean_closure_set(v___f_2918_, 2, v_inst_2905_);
lean_closure_set(v___f_2918_, 3, v_toBind_2911_);
lean_closure_set(v___f_2918_, 4, v___f_2917_);
v___x_2919_ = lean_apply_4(v_toBind_2911_, lean_box(0), lean_box(0), v_getInfoState_2912_, v___f_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* v_m_2920_, lean_object* v_inst_2921_, lean_object* v_inst_2922_, lean_object* v_00_u03b1_2923_, lean_object* v_inst_2924_, lean_object* v_x_2925_, lean_object* v_mkInfo_2926_, lean_object* v_mkInfoOnError_2927_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = l_Lean_Elab_withInfoContext_x27___redArg(v_inst_2921_, v_inst_2922_, v_inst_2924_, v_x_2925_, v_mkInfo_2926_, v_mkInfoOnError_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object* v_treesSaved_2929_, lean_object* v_tree_2930_, lean_object* v_s_2931_){
_start:
{
uint8_t v_enabled_2932_; lean_object* v_assignment_2933_; lean_object* v_lazyAssignment_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2942_; 
v_enabled_2932_ = lean_ctor_get_uint8(v_s_2931_, sizeof(void*)*3);
v_assignment_2933_ = lean_ctor_get(v_s_2931_, 0);
v_lazyAssignment_2934_ = lean_ctor_get(v_s_2931_, 1);
v_isSharedCheck_2942_ = !lean_is_exclusive(v_s_2931_);
if (v_isSharedCheck_2942_ == 0)
{
lean_object* v_unused_2943_; 
v_unused_2943_ = lean_ctor_get(v_s_2931_, 2);
lean_dec(v_unused_2943_);
v___x_2936_ = v_s_2931_;
v_isShared_2937_ = v_isSharedCheck_2942_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_lazyAssignment_2934_);
lean_inc(v_assignment_2933_);
lean_dec(v_s_2931_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2942_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2938_; lean_object* v___x_2940_; 
v___x_2938_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2929_, v_tree_2930_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 2, v___x_2938_);
v___x_2940_ = v___x_2936_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_assignment_2933_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_lazyAssignment_2934_);
lean_ctor_set(v_reuseFailAlloc_2941_, 2, v___x_2938_);
lean_ctor_set_uint8(v_reuseFailAlloc_2941_, sizeof(void*)*3, v_enabled_2932_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object* v_treesSaved_2944_, lean_object* v_modifyInfoState_2945_, lean_object* v_tree_2946_){
_start:
{
lean_object* v___f_2947_; lean_object* v___x_2948_; 
v___f_2947_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2947_, 0, v_treesSaved_2944_);
lean_closure_set(v___f_2947_, 1, v_tree_2946_);
v___x_2948_ = lean_apply_1(v_modifyInfoState_2945_, v___f_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object* v_mkInfoTree_2949_, lean_object* v_toBind_2950_, lean_object* v___f_2951_, lean_object* v_st_2952_){
_start:
{
lean_object* v_trees_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v_trees_2953_ = lean_ctor_get(v_st_2952_, 2);
lean_inc_ref(v_trees_2953_);
lean_dec_ref(v_st_2952_);
v___x_2954_ = lean_apply_1(v_mkInfoTree_2949_, v_trees_2953_);
v___x_2955_ = lean_apply_4(v_toBind_2950_, lean_box(0), lean_box(0), v___x_2954_, v___f_2951_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object* v_toBind_2956_, lean_object* v_getInfoState_2957_, lean_object* v___f_2958_, lean_object* v_x_2959_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = lean_apply_4(v_toBind_2956_, lean_box(0), lean_box(0), v_getInfoState_2957_, v___f_2958_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object* v_toBind_2961_, lean_object* v_getInfoState_2962_, lean_object* v___f_2963_, lean_object* v_x_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(v_toBind_2961_, v_getInfoState_2962_, v___f_2963_, v_x_2964_);
lean_dec(v_x_2964_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object* v_toFunctor_2966_, lean_object* v_modifyInfoState_2967_, lean_object* v_mkInfoTree_2968_, lean_object* v_toBind_2969_, lean_object* v_getInfoState_2970_, lean_object* v_inst_2971_, lean_object* v_x_2972_, lean_object* v___f_2973_, lean_object* v_treesSaved_2974_){
_start:
{
lean_object* v_map_2975_; lean_object* v___f_2976_; lean_object* v___f_2977_; lean_object* v___f_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v_map_2975_ = lean_ctor_get(v_toFunctor_2966_, 0);
lean_inc(v_map_2975_);
lean_dec_ref(v_toFunctor_2966_);
v___f_2976_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2976_, 0, v_treesSaved_2974_);
lean_closure_set(v___f_2976_, 1, v_modifyInfoState_2967_);
lean_inc(v_toBind_2969_);
v___f_2977_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2977_, 0, v_mkInfoTree_2968_);
lean_closure_set(v___f_2977_, 1, v_toBind_2969_);
lean_closure_set(v___f_2977_, 2, v___f_2976_);
v___f_2978_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_2978_, 0, v_toBind_2969_);
lean_closure_set(v___f_2978_, 1, v_getInfoState_2970_);
lean_closure_set(v___f_2978_, 2, v___f_2977_);
v___x_2979_ = lean_apply_4(v_inst_2971_, lean_box(0), lean_box(0), v_x_2972_, v___f_2978_);
v___x_2980_ = lean_apply_4(v_map_2975_, lean_box(0), lean_box(0), v___f_2973_, v___x_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object* v_inst_2981_, lean_object* v_inst_2982_, lean_object* v_inst_2983_, lean_object* v_x_2984_, lean_object* v_mkInfoTree_2985_){
_start:
{
lean_object* v_toApplicative_2986_; lean_object* v_toBind_2987_; lean_object* v_getInfoState_2988_; lean_object* v_modifyInfoState_2989_; lean_object* v_toFunctor_2990_; lean_object* v___f_2991_; lean_object* v___f_2992_; lean_object* v___f_2993_; lean_object* v___x_2994_; 
v_toApplicative_2986_ = lean_ctor_get(v_inst_2981_, 0);
v_toBind_2987_ = lean_ctor_get(v_inst_2981_, 1);
lean_inc_n(v_toBind_2987_, 3);
v_getInfoState_2988_ = lean_ctor_get(v_inst_2982_, 0);
lean_inc_n(v_getInfoState_2988_, 2);
v_modifyInfoState_2989_ = lean_ctor_get(v_inst_2982_, 1);
v_toFunctor_2990_ = lean_ctor_get(v_toApplicative_2986_, 0);
v___f_2991_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2984_);
lean_inc(v_modifyInfoState_2989_);
lean_inc_ref(v_toFunctor_2990_);
v___f_2992_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2992_, 0, v_toFunctor_2990_);
lean_closure_set(v___f_2992_, 1, v_modifyInfoState_2989_);
lean_closure_set(v___f_2992_, 2, v_mkInfoTree_2985_);
lean_closure_set(v___f_2992_, 3, v_toBind_2987_);
lean_closure_set(v___f_2992_, 4, v_getInfoState_2988_);
lean_closure_set(v___f_2992_, 5, v_inst_2983_);
lean_closure_set(v___f_2992_, 6, v_x_2984_);
lean_closure_set(v___f_2992_, 7, v___f_2991_);
v___f_2993_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2993_, 0, v_x_2984_);
lean_closure_set(v___f_2993_, 1, v_inst_2981_);
lean_closure_set(v___f_2993_, 2, v_inst_2982_);
lean_closure_set(v___f_2993_, 3, v_toBind_2987_);
lean_closure_set(v___f_2993_, 4, v___f_2992_);
v___x_2994_ = lean_apply_4(v_toBind_2987_, lean_box(0), lean_box(0), v_getInfoState_2988_, v___f_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object* v_m_2995_, lean_object* v_inst_2996_, lean_object* v_inst_2997_, lean_object* v_00_u03b1_2998_, lean_object* v_inst_2999_, lean_object* v_x_3000_, lean_object* v_mkInfoTree_3001_){
_start:
{
lean_object* v___x_3002_; 
v___x_3002_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_2996_, v_inst_2997_, v_inst_2999_, v_x_3000_, v_mkInfoTree_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object* v_trees_3003_, lean_object* v_toPure_3004_, lean_object* v_____do__lift_3005_){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3006_, 0, v_____do__lift_3005_);
lean_ctor_set(v___x_3006_, 1, v_trees_3003_);
v___x_3007_ = lean_apply_2(v_toPure_3004_, lean_box(0), v___x_3006_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object* v_toPure_3008_, lean_object* v_toBind_3009_, lean_object* v_mkInfo_3010_, lean_object* v_trees_3011_){
_start:
{
lean_object* v___f_3012_; lean_object* v___x_3013_; 
v___f_3012_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3012_, 0, v_trees_3011_);
lean_closure_set(v___f_3012_, 1, v_toPure_3008_);
v___x_3013_ = lean_apply_4(v_toBind_3009_, lean_box(0), lean_box(0), v_mkInfo_3010_, v___f_3012_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object* v_inst_3014_, lean_object* v_inst_3015_, lean_object* v_inst_3016_, lean_object* v_x_3017_, lean_object* v_mkInfo_3018_){
_start:
{
lean_object* v_toApplicative_3019_; lean_object* v_toBind_3020_; lean_object* v_toPure_3021_; lean_object* v___f_3022_; lean_object* v___x_3023_; 
v_toApplicative_3019_ = lean_ctor_get(v_inst_3014_, 0);
v_toBind_3020_ = lean_ctor_get(v_inst_3014_, 1);
v_toPure_3021_ = lean_ctor_get(v_toApplicative_3019_, 1);
lean_inc(v_toBind_3020_);
lean_inc(v_toPure_3021_);
v___f_3022_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3022_, 0, v_toPure_3021_);
lean_closure_set(v___f_3022_, 1, v_toBind_3020_);
lean_closure_set(v___f_3022_, 2, v_mkInfo_3018_);
v___x_3023_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3014_, v_inst_3015_, v_inst_3016_, v_x_3017_, v___f_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object* v_m_3024_, lean_object* v_inst_3025_, lean_object* v_inst_3026_, lean_object* v_00_u03b1_3027_, lean_object* v_inst_3028_, lean_object* v_x_3029_, lean_object* v_mkInfo_3030_){
_start:
{
lean_object* v_toApplicative_3031_; lean_object* v_toBind_3032_; lean_object* v_toPure_3033_; lean_object* v___f_3034_; lean_object* v___x_3035_; 
v_toApplicative_3031_ = lean_ctor_get(v_inst_3025_, 0);
v_toBind_3032_ = lean_ctor_get(v_inst_3025_, 1);
v_toPure_3033_ = lean_ctor_get(v_toApplicative_3031_, 1);
lean_inc(v_toBind_3032_);
lean_inc(v_toPure_3033_);
v___f_3034_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3034_, 0, v_toPure_3033_);
lean_closure_set(v___f_3034_, 1, v_toBind_3032_);
lean_closure_set(v___f_3034_, 2, v_mkInfo_3030_);
v___x_3035_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3025_, v_inst_3026_, v_inst_3028_, v_x_3029_, v___f_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object* v_treesSaved_3036_, lean_object* v_trees_3037_, lean_object* v_s_3038_){
_start:
{
uint8_t v_enabled_3039_; lean_object* v_assignment_3040_; lean_object* v_lazyAssignment_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3049_; 
v_enabled_3039_ = lean_ctor_get_uint8(v_s_3038_, sizeof(void*)*3);
v_assignment_3040_ = lean_ctor_get(v_s_3038_, 0);
v_lazyAssignment_3041_ = lean_ctor_get(v_s_3038_, 1);
v_isSharedCheck_3049_ = !lean_is_exclusive(v_s_3038_);
if (v_isSharedCheck_3049_ == 0)
{
lean_object* v_unused_3050_; 
v_unused_3050_ = lean_ctor_get(v_s_3038_, 2);
lean_dec(v_unused_3050_);
v___x_3043_ = v_s_3038_;
v_isShared_3044_ = v_isSharedCheck_3049_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_lazyAssignment_3041_);
lean_inc(v_assignment_3040_);
lean_dec(v_s_3038_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3049_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3045_; lean_object* v___x_3047_; 
v___x_3045_ = l_Lean_PersistentArray_append___redArg(v_treesSaved_3036_, v_trees_3037_);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 2, v___x_3045_);
v___x_3047_ = v___x_3043_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_assignment_3040_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_lazyAssignment_3041_);
lean_ctor_set(v_reuseFailAlloc_3048_, 2, v___x_3045_);
lean_ctor_set_uint8(v_reuseFailAlloc_3048_, sizeof(void*)*3, v_enabled_3039_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object* v_treesSaved_3051_, lean_object* v_trees_3052_, lean_object* v_s_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_3051_, v_trees_3052_, v_s_3053_);
lean_dec_ref(v_trees_3052_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object* v_treesSaved_3055_, lean_object* v_modifyInfoState_3056_, lean_object* v_trees_3057_){
_start:
{
lean_object* v___f_3058_; lean_object* v___x_3059_; 
v___f_3058_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3058_, 0, v_treesSaved_3055_);
lean_closure_set(v___f_3058_, 1, v_trees_3057_);
v___x_3059_ = lean_apply_1(v_modifyInfoState_3056_, v___f_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object* v_toPure_3060_, lean_object* v_tree_3061_, lean_object* v_____do__lift_3062_){
_start:
{
if (lean_obj_tag(v_____do__lift_3062_) == 0)
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_apply_2(v_toPure_3060_, lean_box(0), v_tree_3061_);
return v___x_3063_;
}
else
{
lean_object* v_val_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v_val_3064_ = lean_ctor_get(v_____do__lift_3062_, 0);
lean_inc(v_val_3064_);
v___x_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3065_, 0, v_val_3064_);
lean_ctor_set(v___x_3065_, 1, v_tree_3061_);
v___x_3066_ = lean_apply_2(v_toPure_3060_, lean_box(0), v___x_3065_);
return v___x_3066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object* v_toPure_3067_, lean_object* v_tree_3068_, lean_object* v_____do__lift_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_3067_, v_tree_3068_, v_____do__lift_3069_);
lean_dec(v_____do__lift_3069_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object* v_assignment_3071_, lean_object* v_toPure_3072_, lean_object* v_toBind_3073_, lean_object* v_ctx_x3f_3074_, lean_object* v_tree_3075_){
_start:
{
lean_object* v_tree_3076_; lean_object* v___f_3077_; lean_object* v___x_3078_; 
v_tree_3076_ = l_Lean_Elab_InfoTree_substitute(v_tree_3075_, v_assignment_3071_);
v___f_3077_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3077_, 0, v_toPure_3072_);
lean_closure_set(v___f_3077_, 1, v_tree_3076_);
v___x_3078_ = lean_apply_4(v_toBind_3073_, lean_box(0), lean_box(0), v_ctx_x3f_3074_, v___f_3077_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object* v_assignment_3079_, lean_object* v_toPure_3080_, lean_object* v_toBind_3081_, lean_object* v_ctx_x3f_3082_, lean_object* v_tree_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(v_assignment_3079_, v_toPure_3080_, v_toBind_3081_, v_ctx_x3f_3082_, v_tree_3083_);
lean_dec_ref(v_assignment_3079_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object* v_toPure_3085_, lean_object* v_toBind_3086_, lean_object* v_ctx_x3f_3087_, lean_object* v_inst_3088_, lean_object* v___f_3089_, lean_object* v_st_3090_){
_start:
{
lean_object* v_assignment_3091_; lean_object* v_trees_3092_; lean_object* v___f_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v_assignment_3091_ = lean_ctor_get(v_st_3090_, 0);
lean_inc_ref(v_assignment_3091_);
v_trees_3092_ = lean_ctor_get(v_st_3090_, 2);
lean_inc_ref(v_trees_3092_);
lean_dec_ref(v_st_3090_);
lean_inc(v_toBind_3086_);
v___f_3093_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_3093_, 0, v_assignment_3091_);
lean_closure_set(v___f_3093_, 1, v_toPure_3085_);
lean_closure_set(v___f_3093_, 2, v_toBind_3086_);
lean_closure_set(v___f_3093_, 3, v_ctx_x3f_3087_);
v___x_3094_ = l_Lean_PersistentArray_mapM___redArg(v_inst_3088_, v___f_3093_, v_trees_3092_);
v___x_3095_ = lean_apply_4(v_toBind_3086_, lean_box(0), lean_box(0), v___x_3094_, v___f_3089_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object* v_toFunctor_3096_, lean_object* v_modifyInfoState_3097_, lean_object* v_toPure_3098_, lean_object* v_toBind_3099_, lean_object* v_ctx_x3f_3100_, lean_object* v_inst_3101_, lean_object* v_getInfoState_3102_, lean_object* v_inst_3103_, lean_object* v_x_3104_, lean_object* v___f_3105_, lean_object* v_treesSaved_3106_){
_start:
{
lean_object* v_map_3107_; lean_object* v___f_3108_; lean_object* v___f_3109_; lean_object* v___f_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v_map_3107_ = lean_ctor_get(v_toFunctor_3096_, 0);
lean_inc(v_map_3107_);
lean_dec_ref(v_toFunctor_3096_);
v___f_3108_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3108_, 0, v_treesSaved_3106_);
lean_closure_set(v___f_3108_, 1, v_modifyInfoState_3097_);
lean_inc(v_toBind_3099_);
v___f_3109_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4), 6, 5);
lean_closure_set(v___f_3109_, 0, v_toPure_3098_);
lean_closure_set(v___f_3109_, 1, v_toBind_3099_);
lean_closure_set(v___f_3109_, 2, v_ctx_x3f_3100_);
lean_closure_set(v___f_3109_, 3, v_inst_3101_);
lean_closure_set(v___f_3109_, 4, v___f_3108_);
v___f_3110_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3110_, 0, v_toBind_3099_);
lean_closure_set(v___f_3110_, 1, v_getInfoState_3102_);
lean_closure_set(v___f_3110_, 2, v___f_3109_);
v___x_3111_ = lean_apply_4(v_inst_3103_, lean_box(0), lean_box(0), v_x_3104_, v___f_3110_);
v___x_3112_ = lean_apply_4(v_map_3107_, lean_box(0), lean_box(0), v___f_3105_, v___x_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object* v_inst_3113_, lean_object* v_inst_3114_, lean_object* v_inst_3115_, lean_object* v_x_3116_, lean_object* v_ctx_x3f_3117_){
_start:
{
lean_object* v_toApplicative_3118_; lean_object* v_toBind_3119_; lean_object* v_getInfoState_3120_; lean_object* v_modifyInfoState_3121_; lean_object* v_toFunctor_3122_; lean_object* v_toPure_3123_; lean_object* v___f_3124_; lean_object* v___f_3125_; lean_object* v___f_3126_; lean_object* v___x_3127_; 
v_toApplicative_3118_ = lean_ctor_get(v_inst_3113_, 0);
v_toBind_3119_ = lean_ctor_get(v_inst_3113_, 1);
lean_inc_n(v_toBind_3119_, 3);
v_getInfoState_3120_ = lean_ctor_get(v_inst_3114_, 0);
lean_inc_n(v_getInfoState_3120_, 2);
v_modifyInfoState_3121_ = lean_ctor_get(v_inst_3114_, 1);
v_toFunctor_3122_ = lean_ctor_get(v_toApplicative_3118_, 0);
v_toPure_3123_ = lean_ctor_get(v_toApplicative_3118_, 1);
v___f_3124_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3116_);
lean_inc_ref(v_inst_3113_);
lean_inc(v_toPure_3123_);
lean_inc(v_modifyInfoState_3121_);
lean_inc_ref(v_toFunctor_3122_);
v___f_3125_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6), 11, 10);
lean_closure_set(v___f_3125_, 0, v_toFunctor_3122_);
lean_closure_set(v___f_3125_, 1, v_modifyInfoState_3121_);
lean_closure_set(v___f_3125_, 2, v_toPure_3123_);
lean_closure_set(v___f_3125_, 3, v_toBind_3119_);
lean_closure_set(v___f_3125_, 4, v_ctx_x3f_3117_);
lean_closure_set(v___f_3125_, 5, v_inst_3113_);
lean_closure_set(v___f_3125_, 6, v_getInfoState_3120_);
lean_closure_set(v___f_3125_, 7, v_inst_3115_);
lean_closure_set(v___f_3125_, 8, v_x_3116_);
lean_closure_set(v___f_3125_, 9, v___f_3124_);
v___f_3126_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3126_, 0, v_x_3116_);
lean_closure_set(v___f_3126_, 1, v_inst_3113_);
lean_closure_set(v___f_3126_, 2, v_inst_3114_);
lean_closure_set(v___f_3126_, 3, v_toBind_3119_);
lean_closure_set(v___f_3126_, 4, v___f_3125_);
v___x_3127_ = lean_apply_4(v_toBind_3119_, lean_box(0), lean_box(0), v_getInfoState_3120_, v___f_3126_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object* v_m_3128_, lean_object* v_inst_3129_, lean_object* v_inst_3130_, lean_object* v_00_u03b1_3131_, lean_object* v_inst_3132_, lean_object* v_x_3133_, lean_object* v_ctx_x3f_3134_){
_start:
{
lean_object* v___x_3135_; 
v___x_3135_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3129_, v_inst_3130_, v_inst_3132_, v_x_3133_, v_ctx_x3f_3134_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object* v_toPure_3136_, lean_object* v_____do__lift_3137_){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3138_, 0, v_____do__lift_3137_);
v___x_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
v___x_3140_ = lean_apply_2(v_toPure_3136_, lean_box(0), v___x_3139_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object* v_inst_3141_, lean_object* v_inst_3142_, lean_object* v_inst_3143_, lean_object* v_inst_3144_, lean_object* v_inst_3145_, lean_object* v_inst_3146_, lean_object* v_inst_3147_, lean_object* v_inst_3148_, lean_object* v_inst_3149_, lean_object* v_x_3150_){
_start:
{
lean_object* v_toApplicative_3151_; lean_object* v_toBind_3152_; lean_object* v_toPure_3153_; lean_object* v___x_3154_; lean_object* v___f_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v_toApplicative_3151_ = lean_ctor_get(v_inst_3141_, 0);
v_toBind_3152_ = lean_ctor_get(v_inst_3141_, 1);
v_toPure_3153_ = lean_ctor_get(v_toApplicative_3151_, 1);
lean_inc_ref(v_inst_3141_);
v___x_3154_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_3141_, v_inst_3145_, v_inst_3147_, v_inst_3146_, v_inst_3148_, v_inst_3143_, v_inst_3149_);
lean_inc(v_toPure_3153_);
v___f_3155_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3155_, 0, v_toPure_3153_);
lean_inc(v_toBind_3152_);
v___x_3156_ = lean_apply_4(v_toBind_3152_, lean_box(0), lean_box(0), v___x_3154_, v___f_3155_);
v___x_3157_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3141_, v_inst_3142_, v_inst_3144_, v_x_3150_, v___x_3156_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object* v_m_3158_, lean_object* v_inst_3159_, lean_object* v_inst_3160_, lean_object* v_00_u03b1_3161_, lean_object* v_inst_3162_, lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_inst_3165_, lean_object* v_inst_3166_, lean_object* v_inst_3167_, lean_object* v_inst_3168_, lean_object* v_x_3169_){
_start:
{
lean_object* v___x_3170_; 
v___x_3170_ = l_Lean_Elab_withSaveInfoContext___redArg(v_inst_3159_, v_inst_3160_, v_inst_3162_, v_inst_3163_, v_inst_3164_, v_inst_3165_, v_inst_3166_, v_inst_3167_, v_inst_3168_, v_x_3169_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object* v_toPure_3171_, lean_object* v_____x_3172_){
_start:
{
if (lean_obj_tag(v_____x_3172_) == 1)
{
lean_object* v_val_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3182_; 
v_val_3173_ = lean_ctor_get(v_____x_3172_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v_____x_3172_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3175_ = v_____x_3172_;
v_isShared_3176_ = v_isSharedCheck_3182_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_val_3173_);
lean_dec(v_____x_3172_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3182_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3177_; lean_object* v___x_3179_; 
v___x_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3177_, 0, v_val_3173_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 0, v___x_3177_);
v___x_3179_ = v___x_3175_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3177_);
v___x_3179_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3180_; 
v___x_3180_ = lean_apply_2(v_toPure_3171_, lean_box(0), v___x_3179_);
return v___x_3180_;
}
}
}
else
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
lean_dec(v_____x_3172_);
v___x_3183_ = lean_box(0);
v___x_3184_ = lean_apply_2(v_toPure_3171_, lean_box(0), v___x_3183_);
return v___x_3184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object* v_inst_3185_, lean_object* v_inst_3186_, lean_object* v_inst_3187_, lean_object* v_inst_3188_, lean_object* v_x_3189_){
_start:
{
lean_object* v_toApplicative_3190_; lean_object* v_toBind_3191_; lean_object* v_toPure_3192_; lean_object* v___f_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v_toApplicative_3190_ = lean_ctor_get(v_inst_3185_, 0);
v_toBind_3191_ = lean_ctor_get(v_inst_3185_, 1);
v_toPure_3192_ = lean_ctor_get(v_toApplicative_3190_, 1);
lean_inc(v_toPure_3192_);
v___f_3193_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3193_, 0, v_toPure_3192_);
lean_inc(v_toBind_3191_);
v___x_3194_ = lean_apply_4(v_toBind_3191_, lean_box(0), lean_box(0), v_inst_3188_, v___f_3193_);
v___x_3195_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3185_, v_inst_3186_, v_inst_3187_, v_x_3189_, v___x_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object* v_m_3196_, lean_object* v_inst_3197_, lean_object* v_inst_3198_, lean_object* v_00_u03b1_3199_, lean_object* v_inst_3200_, lean_object* v_inst_3201_, lean_object* v_x_3202_){
_start:
{
lean_object* v___x_3203_; 
v___x_3203_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(v_inst_3197_, v_inst_3198_, v_inst_3200_, v_inst_3201_, v_x_3202_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object* v_toPure_3204_, lean_object* v_autoImplicits_3205_){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3206_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3206_, 0, v_autoImplicits_3205_);
v___x_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
v___x_3208_ = lean_apply_2(v_toPure_3204_, lean_box(0), v___x_3207_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object* v_inst_3209_, lean_object* v_inst_3210_, lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_x_3213_){
_start:
{
lean_object* v_toApplicative_3214_; lean_object* v_toBind_3215_; lean_object* v_toPure_3216_; lean_object* v___f_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v_toApplicative_3214_ = lean_ctor_get(v_inst_3209_, 0);
v_toBind_3215_ = lean_ctor_get(v_inst_3209_, 1);
v_toPure_3216_ = lean_ctor_get(v_toApplicative_3214_, 1);
lean_inc(v_toPure_3216_);
v___f_3217_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3217_, 0, v_toPure_3216_);
lean_inc(v_toBind_3215_);
v___x_3218_ = lean_apply_4(v_toBind_3215_, lean_box(0), lean_box(0), v_inst_3212_, v___f_3217_);
v___x_3219_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3209_, v_inst_3210_, v_inst_3211_, v_x_3213_, v___x_3218_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object* v_m_3220_, lean_object* v_inst_3221_, lean_object* v_inst_3222_, lean_object* v_00_u03b1_3223_, lean_object* v_inst_3224_, lean_object* v_inst_3225_, lean_object* v_x_3226_){
_start:
{
lean_object* v___x_3227_; 
v___x_3227_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(v_inst_3221_, v_inst_3222_, v_inst_3224_, v_inst_3225_, v_x_3226_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object* v___x_3228_, lean_object* v___x_3229_, lean_object* v_mvarId_3230_, lean_object* v_toPure_3231_, lean_object* v_____do__lift_3232_){
_start:
{
lean_object* v_assignment_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v_assignment_3233_ = lean_ctor_get(v_____do__lift_3232_, 0);
v___x_3234_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_3228_, v___x_3229_, v_assignment_3233_, v_mvarId_3230_);
v___x_3235_ = lean_apply_2(v_toPure_3231_, lean_box(0), v___x_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object* v___x_3236_, lean_object* v___x_3237_, lean_object* v_mvarId_3238_, lean_object* v_toPure_3239_, lean_object* v_____do__lift_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(v___x_3236_, v___x_3237_, v_mvarId_3238_, v_toPure_3239_, v_____do__lift_3240_);
lean_dec_ref(v_____do__lift_3240_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object* v_inst_3244_, lean_object* v_inst_3245_, lean_object* v_mvarId_3246_){
_start:
{
lean_object* v_toApplicative_3247_; lean_object* v_toBind_3248_; lean_object* v_getInfoState_3249_; lean_object* v_toPure_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___f_3253_; lean_object* v___x_3254_; 
v_toApplicative_3247_ = lean_ctor_get(v_inst_3244_, 0);
lean_inc_ref(v_toApplicative_3247_);
v_toBind_3248_ = lean_ctor_get(v_inst_3244_, 1);
lean_inc(v_toBind_3248_);
lean_dec_ref(v_inst_3244_);
v_getInfoState_3249_ = lean_ctor_get(v_inst_3245_, 0);
lean_inc(v_getInfoState_3249_);
lean_dec_ref(v_inst_3245_);
v_toPure_3250_ = lean_ctor_get(v_toApplicative_3247_, 1);
lean_inc(v_toPure_3250_);
lean_dec_ref(v_toApplicative_3247_);
v___x_3251_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3252_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___f_3253_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3253_, 0, v___x_3251_);
lean_closure_set(v___f_3253_, 1, v___x_3252_);
lean_closure_set(v___f_3253_, 2, v_mvarId_3246_);
lean_closure_set(v___f_3253_, 3, v_toPure_3250_);
v___x_3254_ = lean_apply_4(v_toBind_3248_, lean_box(0), lean_box(0), v_getInfoState_3249_, v___f_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* v_m_3255_, lean_object* v_inst_3256_, lean_object* v_inst_3257_, lean_object* v_mvarId_3258_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3256_, v_inst_3257_, v_mvarId_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object* v___x_3260_, lean_object* v___x_3261_, lean_object* v_mvarId_3262_, lean_object* v_infoTree_3263_, lean_object* v_s_3264_){
_start:
{
uint8_t v_enabled_3265_; lean_object* v_assignment_3266_; lean_object* v_lazyAssignment_3267_; lean_object* v_trees_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3276_; 
v_enabled_3265_ = lean_ctor_get_uint8(v_s_3264_, sizeof(void*)*3);
v_assignment_3266_ = lean_ctor_get(v_s_3264_, 0);
v_lazyAssignment_3267_ = lean_ctor_get(v_s_3264_, 1);
v_trees_3268_ = lean_ctor_get(v_s_3264_, 2);
v_isSharedCheck_3276_ = !lean_is_exclusive(v_s_3264_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3270_ = v_s_3264_;
v_isShared_3271_ = v_isSharedCheck_3276_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_trees_3268_);
lean_inc(v_lazyAssignment_3267_);
lean_inc(v_assignment_3266_);
lean_dec(v_s_3264_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3276_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3272_; lean_object* v___x_3274_; 
v___x_3272_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3260_, v___x_3261_, v_assignment_3266_, v_mvarId_3262_, v_infoTree_3263_);
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 0, v___x_3272_);
v___x_3274_ = v___x_3270_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3272_);
lean_ctor_set(v_reuseFailAlloc_3275_, 1, v_lazyAssignment_3267_);
lean_ctor_set(v_reuseFailAlloc_3275_, 2, v_trees_3268_);
lean_ctor_set_uint8(v_reuseFailAlloc_3275_, sizeof(void*)*3, v_enabled_3265_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3280_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2));
v___x_3281_ = lean_unsigned_to_nat(2u);
v___x_3282_ = lean_unsigned_to_nat(384u);
v___x_3283_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1));
v___x_3284_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0));
v___x_3285_ = l_mkPanicMessageWithDecl(v___x_3284_, v___x_3283_, v___x_3282_, v___x_3281_, v___x_3280_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object* v_inst_3286_, lean_object* v___f_3287_, lean_object* v___x_3288_, lean_object* v_____do__lift_3289_){
_start:
{
if (lean_obj_tag(v_____do__lift_3289_) == 0)
{
lean_object* v_modifyInfoState_3290_; lean_object* v___x_3291_; 
v_modifyInfoState_3290_ = lean_ctor_get(v_inst_3286_, 1);
lean_inc(v_modifyInfoState_3290_);
lean_dec_ref(v_inst_3286_);
v___x_3291_ = lean_apply_1(v_modifyInfoState_3290_, v___f_3287_);
return v___x_3291_;
}
else
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_dec_ref(v___f_3287_);
lean_dec_ref(v_inst_3286_);
v___x_3292_ = lean_obj_once(&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3, &l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3_once, _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3);
v___x_3293_ = l_panic___redArg(v___x_3288_, v___x_3292_);
return v___x_3293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object* v_inst_3294_, lean_object* v___f_3295_, lean_object* v___x_3296_, lean_object* v_____do__lift_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(v_inst_3294_, v___f_3295_, v___x_3296_, v_____do__lift_3297_);
lean_dec(v_____do__lift_3297_);
lean_dec(v___x_3296_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object* v_inst_3299_, lean_object* v_inst_3300_, lean_object* v_mvarId_3301_, lean_object* v_infoTree_3302_){
_start:
{
lean_object* v_toBind_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___f_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___f_3310_; lean_object* v___x_3311_; 
v_toBind_3303_ = lean_ctor_get(v_inst_3299_, 1);
lean_inc(v_toBind_3303_);
v___x_3304_ = lean_box(0);
v___x_3305_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3306_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
lean_inc(v_mvarId_3301_);
v___f_3307_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__0), 5, 4);
lean_closure_set(v___f_3307_, 0, v___x_3305_);
lean_closure_set(v___f_3307_, 1, v___x_3306_);
lean_closure_set(v___f_3307_, 2, v_mvarId_3301_);
lean_closure_set(v___f_3307_, 3, v_infoTree_3302_);
lean_inc_ref(v_inst_3300_);
lean_inc_ref(v_inst_3299_);
v___x_3308_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3299_, v_inst_3300_, v_mvarId_3301_);
v___x_3309_ = l_instInhabitedOfMonad___redArg(v_inst_3299_, v___x_3304_);
v___f_3310_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3310_, 0, v_inst_3300_);
lean_closure_set(v___f_3310_, 1, v___f_3307_);
lean_closure_set(v___f_3310_, 2, v___x_3309_);
v___x_3311_ = lean_apply_4(v_toBind_3303_, lean_box(0), lean_box(0), v___x_3308_, v___f_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* v_m_3312_, lean_object* v_inst_3313_, lean_object* v_inst_3314_, lean_object* v_mvarId_3315_, lean_object* v_infoTree_3316_){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = l_Lean_Elab_assignInfoHoleId___redArg(v_inst_3313_, v_inst_3314_, v_mvarId_3315_, v_infoTree_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object* v_stx_3318_, lean_object* v_output_3319_, lean_object* v_toPure_3320_, lean_object* v_____do__lift_3321_){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3322_, 0, v_____do__lift_3321_);
lean_ctor_set(v___x_3322_, 1, v_stx_3318_);
lean_ctor_set(v___x_3322_, 2, v_output_3319_);
v___x_3323_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
v___x_3324_ = lean_apply_2(v_toPure_3320_, lean_box(0), v___x_3323_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object* v_inst_3325_, lean_object* v_inst_3326_, lean_object* v_inst_3327_, lean_object* v_inst_3328_, lean_object* v_stx_3329_, lean_object* v_output_3330_, lean_object* v_x_3331_){
_start:
{
lean_object* v_toApplicative_3332_; lean_object* v_toBind_3333_; lean_object* v_toPure_3334_; lean_object* v___f_3335_; lean_object* v_mkInfo_3336_; lean_object* v___f_3337_; lean_object* v___x_3338_; 
v_toApplicative_3332_ = lean_ctor_get(v_inst_3326_, 0);
v_toBind_3333_ = lean_ctor_get(v_inst_3326_, 1);
v_toPure_3334_ = lean_ctor_get(v_toApplicative_3332_, 1);
lean_inc_n(v_toPure_3334_, 2);
v___f_3335_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3335_, 0, v_stx_3329_);
lean_closure_set(v___f_3335_, 1, v_output_3330_);
lean_closure_set(v___f_3335_, 2, v_toPure_3334_);
lean_inc_n(v_toBind_3333_, 2);
v_mkInfo_3336_ = lean_apply_4(v_toBind_3333_, lean_box(0), lean_box(0), v_inst_3328_, v___f_3335_);
v___f_3337_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3337_, 0, v_toPure_3334_);
lean_closure_set(v___f_3337_, 1, v_toBind_3333_);
lean_closure_set(v___f_3337_, 2, v_mkInfo_3336_);
v___x_3338_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3326_, v_inst_3327_, v_inst_3325_, v_x_3331_, v___f_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* v_m_3339_, lean_object* v_00_u03b1_3340_, lean_object* v_inst_3341_, lean_object* v_inst_3342_, lean_object* v_inst_3343_, lean_object* v_inst_3344_, lean_object* v_stx_3345_, lean_object* v_output_3346_, lean_object* v_x_3347_){
_start:
{
lean_object* v___x_3348_; 
v___x_3348_ = l_Lean_Elab_withMacroExpansionInfo___redArg(v_inst_3341_, v_inst_3342_, v_inst_3343_, v_inst_3344_, v_stx_3345_, v_output_3346_, v_x_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object* v_treesSaved_3349_, lean_object* v___x_3350_, lean_object* v___x_3351_, lean_object* v___x_3352_, lean_object* v_mvarId_3353_, lean_object* v_s_3354_){
_start:
{
lean_object* v_trees_3355_; uint8_t v_enabled_3356_; lean_object* v_assignment_3357_; lean_object* v_lazyAssignment_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3375_; 
v_trees_3355_ = lean_ctor_get(v_s_3354_, 2);
v_enabled_3356_ = lean_ctor_get_uint8(v_s_3354_, sizeof(void*)*3);
v_assignment_3357_ = lean_ctor_get(v_s_3354_, 0);
v_lazyAssignment_3358_ = lean_ctor_get(v_s_3354_, 1);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_s_3354_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3360_ = v_s_3354_;
v_isShared_3361_ = v_isSharedCheck_3375_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_trees_3355_);
lean_inc(v_lazyAssignment_3358_);
lean_inc(v_assignment_3357_);
lean_dec(v_s_3354_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3375_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v_size_3362_; lean_object* v___x_3363_; uint8_t v___x_3364_; 
v_size_3362_ = lean_ctor_get(v_trees_3355_, 2);
v___x_3363_ = lean_unsigned_to_nat(0u);
v___x_3364_ = lean_nat_dec_lt(v___x_3363_, v_size_3362_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3366_; 
lean_dec_ref(v_trees_3355_);
lean_dec(v_mvarId_3353_);
lean_dec_ref(v___x_3352_);
lean_dec_ref(v___x_3351_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 2, v_treesSaved_3349_);
v___x_3366_ = v___x_3360_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_assignment_3357_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_lazyAssignment_3358_);
lean_ctor_set(v_reuseFailAlloc_3367_, 2, v_treesSaved_3349_);
lean_ctor_set_uint8(v_reuseFailAlloc_3367_, sizeof(void*)*3, v_enabled_3356_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3373_; 
v___x_3368_ = lean_unsigned_to_nat(1u);
v___x_3369_ = lean_nat_sub(v_size_3362_, v___x_3368_);
v___x_3370_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3350_, v_trees_3355_, v___x_3369_);
lean_dec(v___x_3369_);
lean_dec_ref(v_trees_3355_);
v___x_3371_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3351_, v___x_3352_, v_assignment_3357_, v_mvarId_3353_, v___x_3370_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 2, v_treesSaved_3349_);
lean_ctor_set(v___x_3360_, 0, v___x_3371_);
v___x_3373_ = v___x_3360_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3371_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v_lazyAssignment_3358_);
lean_ctor_set(v_reuseFailAlloc_3374_, 2, v_treesSaved_3349_);
lean_ctor_set_uint8(v_reuseFailAlloc_3374_, sizeof(void*)*3, v_enabled_3356_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1___boxed(lean_object* v_treesSaved_3376_, lean_object* v___x_3377_, lean_object* v___x_3378_, lean_object* v___x_3379_, lean_object* v_mvarId_3380_, lean_object* v_s_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_Elab_withInfoHole___redArg___lam__1(v_treesSaved_3376_, v___x_3377_, v___x_3378_, v___x_3379_, v_mvarId_3380_, v_s_3381_);
lean_dec_ref(v___x_3377_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object* v_modifyInfoState_3383_, lean_object* v___f_3384_, lean_object* v_x_3385_){
_start:
{
lean_object* v___x_3386_; 
v___x_3386_ = lean_apply_1(v_modifyInfoState_3383_, v___f_3384_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object* v_modifyInfoState_3387_, lean_object* v___f_3388_, lean_object* v_x_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_3387_, v___f_3388_, v_x_3389_);
lean_dec(v_x_3389_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object* v_toFunctor_3391_, lean_object* v___x_3392_, lean_object* v___x_3393_, lean_object* v___x_3394_, lean_object* v_mvarId_3395_, lean_object* v_modifyInfoState_3396_, lean_object* v_inst_3397_, lean_object* v_x_3398_, lean_object* v___f_3399_, lean_object* v_treesSaved_3400_){
_start:
{
lean_object* v_map_3401_; lean_object* v___f_3402_; lean_object* v___f_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v_map_3401_ = lean_ctor_get(v_toFunctor_3391_, 0);
lean_inc(v_map_3401_);
lean_dec_ref(v_toFunctor_3391_);
v___f_3402_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_3402_, 0, v_treesSaved_3400_);
lean_closure_set(v___f_3402_, 1, v___x_3392_);
lean_closure_set(v___f_3402_, 2, v___x_3393_);
lean_closure_set(v___f_3402_, 3, v___x_3394_);
lean_closure_set(v___f_3402_, 4, v_mvarId_3395_);
v___f_3403_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3403_, 0, v_modifyInfoState_3396_);
lean_closure_set(v___f_3403_, 1, v___f_3402_);
v___x_3404_ = lean_apply_4(v_inst_3397_, lean_box(0), lean_box(0), v_x_3398_, v___f_3403_);
v___x_3405_ = lean_apply_4(v_map_3401_, lean_box(0), lean_box(0), v___f_3399_, v___x_3404_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object* v_inst_3406_, lean_object* v_inst_3407_, lean_object* v_inst_3408_, lean_object* v_mvarId_3409_, lean_object* v_x_3410_){
_start:
{
lean_object* v_toApplicative_3411_; lean_object* v_toBind_3412_; lean_object* v_getInfoState_3413_; lean_object* v_modifyInfoState_3414_; lean_object* v_toFunctor_3415_; lean_object* v___f_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___f_3420_; lean_object* v___f_3421_; lean_object* v___x_3422_; 
v_toApplicative_3411_ = lean_ctor_get(v_inst_3407_, 0);
v_toBind_3412_ = lean_ctor_get(v_inst_3407_, 1);
lean_inc_n(v_toBind_3412_, 2);
v_getInfoState_3413_ = lean_ctor_get(v_inst_3408_, 0);
lean_inc(v_getInfoState_3413_);
v_modifyInfoState_3414_ = lean_ctor_get(v_inst_3408_, 1);
v_toFunctor_3415_ = lean_ctor_get(v_toApplicative_3411_, 0);
v___f_3416_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
v___x_3417_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3418_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3419_ = l_Lean_Elab_instInhabitedInfoTree_default;
lean_inc(v_x_3410_);
lean_inc(v_modifyInfoState_3414_);
lean_inc_ref(v_toFunctor_3415_);
v___f_3420_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3420_, 0, v_toFunctor_3415_);
lean_closure_set(v___f_3420_, 1, v___x_3419_);
lean_closure_set(v___f_3420_, 2, v___x_3417_);
lean_closure_set(v___f_3420_, 3, v___x_3418_);
lean_closure_set(v___f_3420_, 4, v_mvarId_3409_);
lean_closure_set(v___f_3420_, 5, v_modifyInfoState_3414_);
lean_closure_set(v___f_3420_, 6, v_inst_3406_);
lean_closure_set(v___f_3420_, 7, v_x_3410_);
lean_closure_set(v___f_3420_, 8, v___f_3416_);
v___f_3421_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3421_, 0, v_x_3410_);
lean_closure_set(v___f_3421_, 1, v_inst_3407_);
lean_closure_set(v___f_3421_, 2, v_inst_3408_);
lean_closure_set(v___f_3421_, 3, v_toBind_3412_);
lean_closure_set(v___f_3421_, 4, v___f_3420_);
v___x_3422_ = lean_apply_4(v_toBind_3412_, lean_box(0), lean_box(0), v_getInfoState_3413_, v___f_3421_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object* v_m_3423_, lean_object* v_00_u03b1_3424_, lean_object* v_inst_3425_, lean_object* v_inst_3426_, lean_object* v_inst_3427_, lean_object* v_mvarId_3428_, lean_object* v_x_3429_){
_start:
{
lean_object* v_toApplicative_3430_; lean_object* v_toBind_3431_; lean_object* v_getInfoState_3432_; lean_object* v_modifyInfoState_3433_; lean_object* v_toFunctor_3434_; lean_object* v___f_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___f_3439_; lean_object* v___f_3440_; lean_object* v___x_3441_; 
v_toApplicative_3430_ = lean_ctor_get(v_inst_3426_, 0);
v_toBind_3431_ = lean_ctor_get(v_inst_3426_, 1);
lean_inc_n(v_toBind_3431_, 2);
v_getInfoState_3432_ = lean_ctor_get(v_inst_3427_, 0);
lean_inc(v_getInfoState_3432_);
v_modifyInfoState_3433_ = lean_ctor_get(v_inst_3427_, 1);
v_toFunctor_3434_ = lean_ctor_get(v_toApplicative_3430_, 0);
v___f_3435_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
v___x_3436_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3437_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3438_ = l_Lean_Elab_instInhabitedInfoTree_default;
lean_inc(v_x_3429_);
lean_inc(v_modifyInfoState_3433_);
lean_inc_ref(v_toFunctor_3434_);
v___f_3439_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3439_, 0, v_toFunctor_3434_);
lean_closure_set(v___f_3439_, 1, v___x_3438_);
lean_closure_set(v___f_3439_, 2, v___x_3436_);
lean_closure_set(v___f_3439_, 3, v___x_3437_);
lean_closure_set(v___f_3439_, 4, v_mvarId_3428_);
lean_closure_set(v___f_3439_, 5, v_modifyInfoState_3433_);
lean_closure_set(v___f_3439_, 6, v_inst_3425_);
lean_closure_set(v___f_3439_, 7, v_x_3429_);
lean_closure_set(v___f_3439_, 8, v___f_3435_);
v___f_3440_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3440_, 0, v_x_3429_);
lean_closure_set(v___f_3440_, 1, v_inst_3426_);
lean_closure_set(v___f_3440_, 2, v_inst_3427_);
lean_closure_set(v___f_3440_, 3, v_toBind_3431_);
lean_closure_set(v___f_3440_, 4, v___f_3439_);
v___x_3441_ = lean_apply_4(v_toBind_3431_, lean_box(0), lean_box(0), v_getInfoState_3432_, v___f_3440_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t v_flag_3442_, lean_object* v_s_3443_){
_start:
{
lean_object* v_assignment_3444_; lean_object* v_lazyAssignment_3445_; lean_object* v_trees_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
v_assignment_3444_ = lean_ctor_get(v_s_3443_, 0);
v_lazyAssignment_3445_ = lean_ctor_get(v_s_3443_, 1);
v_trees_3446_ = lean_ctor_get(v_s_3443_, 2);
v_isSharedCheck_3453_ = !lean_is_exclusive(v_s_3443_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v_s_3443_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_trees_3446_);
lean_inc(v_lazyAssignment_3445_);
lean_inc(v_assignment_3444_);
lean_dec(v_s_3443_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_assignment_3444_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_lazyAssignment_3445_);
lean_ctor_set(v_reuseFailAlloc_3452_, 2, v_trees_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_ctor_set_uint8(v___x_3451_, sizeof(void*)*3, v_flag_3442_);
return v___x_3451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object* v_flag_3454_, lean_object* v_s_3455_){
_start:
{
uint8_t v_flag_boxed_3456_; lean_object* v_res_3457_; 
v_flag_boxed_3456_ = lean_unbox(v_flag_3454_);
v_res_3457_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_3456_, v_s_3455_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object* v_inst_3458_, uint8_t v_flag_3459_){
_start:
{
lean_object* v_modifyInfoState_3460_; lean_object* v___x_3461_; lean_object* v___f_3462_; lean_object* v___x_3463_; 
v_modifyInfoState_3460_ = lean_ctor_get(v_inst_3458_, 1);
lean_inc(v_modifyInfoState_3460_);
lean_dec_ref(v_inst_3458_);
v___x_3461_ = lean_box(v_flag_3459_);
v___f_3462_ = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3462_, 0, v___x_3461_);
v___x_3463_ = lean_apply_1(v_modifyInfoState_3460_, v___f_3462_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object* v_inst_3464_, lean_object* v_flag_3465_){
_start:
{
uint8_t v_flag_boxed_3466_; lean_object* v_res_3467_; 
v_flag_boxed_3466_ = lean_unbox(v_flag_3465_);
v_res_3467_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3464_, v_flag_boxed_3466_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object* v_m_3468_, lean_object* v_inst_3469_, uint8_t v_flag_3470_){
_start:
{
lean_object* v___x_3471_; 
v___x_3471_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3469_, v_flag_3470_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object* v_m_3472_, lean_object* v_inst_3473_, lean_object* v_flag_3474_){
_start:
{
uint8_t v_flag_boxed_3475_; lean_object* v_res_3476_; 
v_flag_boxed_3475_ = lean_unbox(v_flag_3474_);
v_res_3476_ = l_Lean_Elab_enableInfoTree(v_m_3472_, v_inst_3473_, v_flag_boxed_3475_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object* v_x_3477_){
_start:
{
lean_object* v_fst_3478_; 
v_fst_3478_ = lean_ctor_get(v_x_3477_, 0);
lean_inc(v_fst_3478_);
return v_fst_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object* v_x_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_3479_);
lean_dec_ref(v_x_3479_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object* v_x_3481_, lean_object* v_____r_3482_){
_start:
{
lean_inc(v_x_3481_);
return v_x_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object* v_x_3483_, lean_object* v_____r_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_3483_, v_____r_3484_);
lean_dec(v_x_3483_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object* v___x_3486_, lean_object* v_x_3487_){
_start:
{
lean_inc(v___x_3486_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object* v___x_3488_, lean_object* v_x_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_3488_, v_x_3489_);
lean_dec(v_x_3489_);
lean_dec(v___x_3488_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object* v_toFunctor_3491_, lean_object* v_inst_3492_, uint8_t v_flag_3493_, lean_object* v_toBind_3494_, lean_object* v___f_3495_, lean_object* v_inst_3496_, lean_object* v___f_3497_, lean_object* v_____do__lift_3498_){
_start:
{
uint8_t v_enabled_3499_; lean_object* v_map_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___f_3504_; lean_object* v_y_3505_; lean_object* v___x_3506_; 
v_enabled_3499_ = lean_ctor_get_uint8(v_____do__lift_3498_, sizeof(void*)*3);
v_map_3500_ = lean_ctor_get(v_toFunctor_3491_, 0);
lean_inc(v_map_3500_);
lean_dec_ref(v_toFunctor_3491_);
lean_inc_ref(v_inst_3492_);
v___x_3501_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3492_, v_flag_3493_);
v___x_3502_ = lean_apply_4(v_toBind_3494_, lean_box(0), lean_box(0), v___x_3501_, v___f_3495_);
v___x_3503_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3492_, v_enabled_3499_);
v___f_3504_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_3504_, 0, v___x_3503_);
v_y_3505_ = lean_apply_4(v_inst_3496_, lean_box(0), lean_box(0), v___x_3502_, v___f_3504_);
v___x_3506_ = lean_apply_4(v_map_3500_, lean_box(0), lean_box(0), v___f_3497_, v_y_3505_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object* v_toFunctor_3507_, lean_object* v_inst_3508_, lean_object* v_flag_3509_, lean_object* v_toBind_3510_, lean_object* v___f_3511_, lean_object* v_inst_3512_, lean_object* v___f_3513_, lean_object* v_____do__lift_3514_){
_start:
{
uint8_t v_flag_boxed_3515_; lean_object* v_res_3516_; 
v_flag_boxed_3515_ = lean_unbox(v_flag_3509_);
v_res_3516_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_3507_, v_inst_3508_, v_flag_boxed_3515_, v_toBind_3510_, v___f_3511_, v_inst_3512_, v___f_3513_, v_____do__lift_3514_);
lean_dec_ref(v_____do__lift_3514_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object* v_inst_3518_, lean_object* v_inst_3519_, lean_object* v_inst_3520_, uint8_t v_flag_3521_, lean_object* v_x_3522_){
_start:
{
lean_object* v_toApplicative_3523_; lean_object* v_toBind_3524_; lean_object* v_getInfoState_3525_; lean_object* v_toFunctor_3526_; lean_object* v___f_3527_; lean_object* v___f_3528_; lean_object* v___x_3529_; lean_object* v___f_3530_; lean_object* v___x_3531_; 
v_toApplicative_3523_ = lean_ctor_get(v_inst_3518_, 0);
lean_inc_ref(v_toApplicative_3523_);
v_toBind_3524_ = lean_ctor_get(v_inst_3518_, 1);
lean_inc_n(v_toBind_3524_, 2);
lean_dec_ref(v_inst_3518_);
v_getInfoState_3525_ = lean_ctor_get(v_inst_3519_, 0);
lean_inc(v_getInfoState_3525_);
v_toFunctor_3526_ = lean_ctor_get(v_toApplicative_3523_, 0);
lean_inc_ref(v_toFunctor_3526_);
lean_dec_ref(v_toApplicative_3523_);
v___f_3527_ = ((lean_object*)(l_Lean_Elab_withEnableInfoTree___redArg___closed__0));
v___f_3528_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3528_, 0, v_x_3522_);
v___x_3529_ = lean_box(v_flag_3521_);
v___f_3530_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_3530_, 0, v_toFunctor_3526_);
lean_closure_set(v___f_3530_, 1, v_inst_3519_);
lean_closure_set(v___f_3530_, 2, v___x_3529_);
lean_closure_set(v___f_3530_, 3, v_toBind_3524_);
lean_closure_set(v___f_3530_, 4, v___f_3528_);
lean_closure_set(v___f_3530_, 5, v_inst_3520_);
lean_closure_set(v___f_3530_, 6, v___f_3527_);
v___x_3531_ = lean_apply_4(v_toBind_3524_, lean_box(0), lean_box(0), v_getInfoState_3525_, v___f_3530_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object* v_inst_3532_, lean_object* v_inst_3533_, lean_object* v_inst_3534_, lean_object* v_flag_3535_, lean_object* v_x_3536_){
_start:
{
uint8_t v_flag_boxed_3537_; lean_object* v_res_3538_; 
v_flag_boxed_3537_ = lean_unbox(v_flag_3535_);
v_res_3538_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3532_, v_inst_3533_, v_inst_3534_, v_flag_boxed_3537_, v_x_3536_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object* v_m_3539_, lean_object* v_00_u03b1_3540_, lean_object* v_inst_3541_, lean_object* v_inst_3542_, lean_object* v_inst_3543_, uint8_t v_flag_3544_, lean_object* v_x_3545_){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3541_, v_inst_3542_, v_inst_3543_, v_flag_3544_, v_x_3545_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object* v_m_3547_, lean_object* v_00_u03b1_3548_, lean_object* v_inst_3549_, lean_object* v_inst_3550_, lean_object* v_inst_3551_, lean_object* v_flag_3552_, lean_object* v_x_3553_){
_start:
{
uint8_t v_flag_boxed_3554_; lean_object* v_res_3555_; 
v_flag_boxed_3554_ = lean_unbox(v_flag_3552_);
v_res_3555_ = l_Lean_Elab_withEnableInfoTree(v_m_3547_, v_00_u03b1_3548_, v_inst_3549_, v_inst_3550_, v_inst_3551_, v_flag_boxed_3554_, v_x_3553_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object* v_toPure_3556_, lean_object* v_____do__lift_3557_){
_start:
{
lean_object* v_trees_3558_; lean_object* v___x_3559_; 
v_trees_3558_ = lean_ctor_get(v_____do__lift_3557_, 2);
lean_inc_ref(v_trees_3558_);
lean_dec_ref(v_____do__lift_3557_);
v___x_3559_ = lean_apply_2(v_toPure_3556_, lean_box(0), v_trees_3558_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object* v_inst_3560_, lean_object* v_inst_3561_){
_start:
{
lean_object* v_toApplicative_3562_; lean_object* v_toBind_3563_; lean_object* v_getInfoState_3564_; lean_object* v_toPure_3565_; lean_object* v___f_3566_; lean_object* v___x_3567_; 
v_toApplicative_3562_ = lean_ctor_get(v_inst_3561_, 0);
lean_inc_ref(v_toApplicative_3562_);
v_toBind_3563_ = lean_ctor_get(v_inst_3561_, 1);
lean_inc(v_toBind_3563_);
lean_dec_ref(v_inst_3561_);
v_getInfoState_3564_ = lean_ctor_get(v_inst_3560_, 0);
lean_inc(v_getInfoState_3564_);
lean_dec_ref(v_inst_3560_);
v_toPure_3565_ = lean_ctor_get(v_toApplicative_3562_, 1);
lean_inc(v_toPure_3565_);
lean_dec_ref(v_toApplicative_3562_);
v___f_3566_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3566_, 0, v_toPure_3565_);
v___x_3567_ = lean_apply_4(v_toBind_3563_, lean_box(0), lean_box(0), v_getInfoState_3564_, v___f_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object* v_m_3568_, lean_object* v_inst_3569_, lean_object* v_inst_3570_){
_start:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_3569_, v_inst_3570_);
return v___x_3571_;
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
