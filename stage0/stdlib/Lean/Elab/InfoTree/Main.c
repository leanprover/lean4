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
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__20;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__21 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__21_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__22;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__23 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__23_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__24;
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
lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg(lean_object* v_info_221_, lean_object* v_x_222_){
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
LEAN_EXPORT void l_Lean_Elab_ContextInfo_runCoreM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_221_ = stack[0].m_obj;
lean_object* v_x_222_ = stack[1].m_obj;
lean_object* v_res_415_;
v_res_415_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_221_, v_x_222_);
stack->m_obj
 = v_res_415_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___boxed(lean_object* v_info_416_, lean_object* v_x_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_416_, v_x_417_);
return v_res_419_;
}
}
lean_object* l_Lean_Elab_ContextInfo_runCoreM(lean_object* v_00_u03b1_420_, lean_object* v_info_421_, lean_object* v_x_422_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_421_, v_x_422_);
return v___x_424_;
}
}
LEAN_EXPORT void l_Lean_Elab_ContextInfo_runCoreM_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_421_ = stack[1].m_obj;
lean_object* v_x_422_ = stack[2].m_obj;
lean_object* v_res_425_;
v_res_425_ = l_Lean_Elab_ContextInfo_runCoreM(lean_box(0), v_info_421_, v_x_422_);
stack->m_obj
 = v_res_425_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___boxed(lean_object* v_00_u03b1_426_, lean_object* v_info_427_, lean_object* v_x_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Elab_ContextInfo_runCoreM(v_00_u03b1_426_, v_info_427_, v_x_428_);
return v_res_430_;
}
}
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(lean_object* v___x_431_, lean_object* v_x_432_, lean_object* v___x_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_st_mk_ref(v___x_431_);
lean_inc(v___x_437_);
v___x_438_ = lean_apply_5(v_x_432_, v___x_433_, v___x_437_, v___y_434_, v___y_435_, lean_box(0));
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_448_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_448_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_448_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_448_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_443_ = lean_st_ref_get(v___x_437_);
lean_dec(v___x_437_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v_a_439_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_444_);
v___x_446_ = v___x_441_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
lean_dec(v___x_437_);
v_a_449_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_438_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_438_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_431_ = stack[0].m_obj;
lean_object* v_x_432_ = stack[1].m_obj;
lean_object* v___x_433_ = stack[2].m_obj;
lean_object* v___y_434_ = stack[3].m_obj;
lean_object* v___y_435_ = stack[4].m_obj;
lean_object* v_res_457_;
v_res_457_ = l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(v___x_431_, v_x_432_, v___x_433_, v___y_434_, v___y_435_);
stack->m_obj
 = v_res_457_;
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
v___x_481_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
lean_ctor_set(v___x_481_, 2, v___x_480_);
lean_ctor_set(v___x_481_, 3, v___x_480_);
lean_ctor_set(v___x_481_, 4, v___x_480_);
lean_ctor_set(v___x_481_, 5, v___x_480_);
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
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object* v_info_493_, lean_object* v_lctx_494_, lean_object* v_x_495_){
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
LEAN_EXPORT void l_Lean_Elab_ContextInfo_runMetaM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_493_ = stack[0].m_obj;
lean_object* v_lctx_494_ = stack[1].m_obj;
lean_object* v_x_495_ = stack[2].m_obj;
lean_object* v_res_530_;
v_res_530_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_493_, v_lctx_494_, v_x_495_);
stack->m_obj
 = v_res_530_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object* v_info_531_, lean_object* v_lctx_532_, lean_object* v_x_533_, lean_object* v_a_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_531_, v_lctx_532_, v_x_533_);
return v_res_535_;
}
}
lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object* v_00_u03b1_536_, lean_object* v_info_537_, lean_object* v_lctx_538_, lean_object* v_x_539_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_537_, v_lctx_538_, v_x_539_);
return v___x_541_;
}
}
LEAN_EXPORT void l_Lean_Elab_ContextInfo_runMetaM_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_537_ = stack[1].m_obj;
lean_object* v_lctx_538_ = stack[2].m_obj;
lean_object* v_x_539_ = stack[3].m_obj;
lean_object* v_res_542_;
v_res_542_ = l_Lean_Elab_ContextInfo_runMetaM(lean_box(0), v_info_537_, v_lctx_538_, v_x_539_);
stack->m_obj
 = v_res_542_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object* v_00_u03b1_543_, lean_object* v_info_544_, lean_object* v_lctx_545_, lean_object* v_x_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Elab_ContextInfo_runMetaM(v_00_u03b1_543_, v_info_544_, v_lctx_545_, v_x_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object* v_info_549_, lean_object* v_lctx_550_){
_start:
{
lean_object* v_toCommandContextInfo_551_; lean_object* v_env_552_; lean_object* v_mctx_553_; lean_object* v_options_554_; lean_object* v_currNamespace_555_; lean_object* v_openDecls_556_; lean_object* v___x_557_; 
v_toCommandContextInfo_551_ = lean_ctor_get(v_info_549_, 0);
v_env_552_ = lean_ctor_get(v_toCommandContextInfo_551_, 0);
v_mctx_553_ = lean_ctor_get(v_toCommandContextInfo_551_, 3);
v_options_554_ = lean_ctor_get(v_toCommandContextInfo_551_, 4);
v_currNamespace_555_ = lean_ctor_get(v_toCommandContextInfo_551_, 5);
v_openDecls_556_ = lean_ctor_get(v_toCommandContextInfo_551_, 6);
lean_inc(v_openDecls_556_);
lean_inc(v_currNamespace_555_);
lean_inc_ref(v_options_554_);
lean_inc_ref(v_mctx_553_);
lean_inc_ref(v_env_552_);
v___x_557_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_557_, 0, v_env_552_);
lean_ctor_set(v___x_557_, 1, v_mctx_553_);
lean_ctor_set(v___x_557_, 2, v_lctx_550_);
lean_ctor_set(v___x_557_, 3, v_options_554_);
lean_ctor_set(v___x_557_, 4, v_currNamespace_555_);
lean_ctor_set(v___x_557_, 5, v_openDecls_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object* v_info_558_, lean_object* v_lctx_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_558_, v_lctx_559_);
lean_dec_ref(v_info_558_);
return v_res_560_;
}
}
lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object* v_info_561_, lean_object* v_lctx_562_, lean_object* v_stx_563_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_565_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_561_, v_lctx_562_);
v___x_566_ = l_Lean_ppTerm(v___x_565_, v_stx_563_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT void l_Lean_Elab_ContextInfo_ppSyntax_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_561_ = stack[0].m_obj;
lean_object* v_lctx_562_ = stack[1].m_obj;
lean_object* v_stx_563_ = stack[2].m_obj;
lean_object* v_res_568_;
v_res_568_ = l_Lean_Elab_ContextInfo_ppSyntax(v_info_561_, v_lctx_562_, v_stx_563_);
stack->m_obj
 = v_res_568_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object* v_info_569_, lean_object* v_lctx_570_, lean_object* v_stx_571_, lean_object* v_a_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Elab_ContextInfo_ppSyntax(v_info_569_, v_lctx_570_, v_stx_571_);
lean_dec_ref(v_info_569_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(lean_object* v_ctx_589_, lean_object* v_pos_590_, lean_object* v_info_591_){
_start:
{
lean_object* v_toCommandContextInfo_592_; lean_object* v_fileMap_593_; lean_object* v___x_594_; lean_object* v_line_595_; lean_object* v_column_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_619_; 
v_toCommandContextInfo_592_ = lean_ctor_get(v_ctx_589_, 0);
lean_inc_ref(v_toCommandContextInfo_592_);
lean_dec_ref(v_ctx_589_);
v_fileMap_593_ = lean_ctor_get(v_toCommandContextInfo_592_, 2);
lean_inc_ref(v_fileMap_593_);
lean_dec_ref(v_toCommandContextInfo_592_);
v___x_594_ = l_Lean_FileMap_toPosition(v_fileMap_593_, v_pos_590_);
v_line_595_ = lean_ctor_get(v___x_594_, 0);
v_column_596_ = lean_ctor_get(v___x_594_, 1);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_619_ == 0)
{
v___x_598_ = v___x_594_;
v_isShared_599_ = v_isSharedCheck_619_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_column_596_);
lean_inc(v_line_595_);
lean_dec(v___x_594_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_619_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_600_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_601_ = l_Nat_reprFast(v_line_595_);
v___x_602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
if (v_isShared_599_ == 0)
{
lean_ctor_set_tag(v___x_598_, 5);
lean_ctor_set(v___x_598_, 1, v___x_602_);
lean_ctor_set(v___x_598_, 0, v___x_600_);
v___x_604_ = v___x_598_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v___x_602_);
v___x_604_ = v_reuseFailAlloc_618_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v_pos_611_; 
v___x_605_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
v___x_606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = l_Nat_reprFast(v_column_596_);
v___x_608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
v___x_609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_606_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v_pos_611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_pos_611_, 0, v___x_609_);
lean_ctor_set(v_pos_611_, 1, v___x_610_);
switch(lean_obj_tag(v_info_591_))
{
case 0:
{
return v_pos_611_;
}
case 1:
{
uint8_t v_canonical_615_; 
v_canonical_615_ = lean_ctor_get_uint8(v_info_591_, sizeof(void*)*2);
if (v_canonical_615_ == 1)
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9));
v___x_617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_617_, 0, v_pos_611_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
return v___x_617_;
}
else
{
goto v___jp_612_;
}
}
default: 
{
goto v___jp_612_;
}
}
v___jp_612_:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7));
v___x_614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_614_, 0, v_pos_611_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
return v___x_614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(lean_object* v_ctx_620_, lean_object* v_pos_621_, lean_object* v_info_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_620_, v_pos_621_, v_info_622_);
lean_dec(v_info_622_);
lean_dec(v_pos_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(lean_object* v_ctx_627_, lean_object* v_stx_628_){
_start:
{
lean_object* v___y_630_; lean_object* v___y_631_; uint8_t v___x_639_; lean_object* v___y_641_; lean_object* v___x_644_; 
v___x_639_ = 0;
v___x_644_ = l_Lean_Syntax_getPos_x3f(v_stx_628_, v___x_639_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v___x_645_; 
v___x_645_ = lean_unsigned_to_nat(0u);
v___y_641_ = v___x_645_;
goto v___jp_640_;
}
else
{
lean_object* v_val_646_; 
v_val_646_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v___x_644_, 1);
v___y_641_ = v_val_646_;
goto v___jp_640_;
}
v___jp_629_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_632_ = l_Lean_Syntax_getHeadInfo(v_stx_628_);
lean_inc_ref(v_ctx_627_);
v___x_633_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_627_, v___y_630_, v___x_632_);
lean_dec(v___x_632_);
lean_dec(v___y_630_);
v___x_634_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = l_Lean_Syntax_getTailInfo(v_stx_628_);
v___x_637_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_627_, v___y_631_, v___x_636_);
lean_dec(v___x_636_);
lean_dec(v___y_631_);
v___x_638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_635_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
return v___x_638_;
}
v___jp_640_:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Syntax_getTailPos_x3f(v_stx_628_, v___x_639_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_inc(v___y_641_);
v___y_630_ = v___y_641_;
v___y_631_ = v___y_641_;
goto v___jp_629_;
}
else
{
lean_object* v_val_643_; 
v_val_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_val_643_);
lean_dec_ref_known(v___x_642_, 1);
v___y_630_ = v___y_641_;
v___y_631_ = v_val_643_;
goto v___jp_629_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(lean_object* v_ctx_647_, lean_object* v_stx_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_647_, v_stx_648_);
lean_dec(v_stx_648_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(lean_object* v_ctx_653_, lean_object* v_info_654_){
_start:
{
lean_object* v_elaborator_655_; lean_object* v_stx_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_671_; 
v_elaborator_655_ = lean_ctor_get(v_info_654_, 0);
v_stx_656_ = lean_ctor_get(v_info_654_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_info_654_);
if (v_isSharedCheck_671_ == 0)
{
v___x_658_ = v_info_654_;
v_isShared_659_ = v_isSharedCheck_671_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_stx_656_);
lean_inc(v_elaborator_655_);
lean_dec(v_info_654_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_671_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
uint8_t v___x_660_; 
v___x_660_ = l_Lean_Name_isAnonymous(v_elaborator_655_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_661_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_653_, v_stx_656_);
lean_dec(v_stx_656_);
v___x_662_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
if (v_isShared_659_ == 0)
{
lean_ctor_set_tag(v___x_658_, 5);
lean_ctor_set(v___x_658_, 1, v___x_662_);
lean_ctor_set(v___x_658_, 0, v___x_661_);
v___x_664_ = v___x_658_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_662_);
v___x_664_ = v_reuseFailAlloc_669_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
uint8_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_665_ = 1;
v___x_666_ = l_Lean_Name_toString(v_elaborator_655_, v___x_665_);
v___x_667_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
v___x_668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_664_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
return v___x_668_;
}
}
else
{
lean_object* v___x_670_; 
lean_del_object(v___x_658_);
lean_dec(v_elaborator_655_);
v___x_670_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_653_, v_stx_656_);
lean_dec(v_stx_656_);
return v___x_670_;
}
}
}
}
lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object* v_info_672_, lean_object* v_ctx_673_, lean_object* v_x_674_){
_start:
{
lean_object* v_lctx_676_; lean_object* v___x_677_; 
v_lctx_676_ = lean_ctor_get(v_info_672_, 1);
lean_inc_ref(v_lctx_676_);
lean_dec_ref(v_info_672_);
v___x_677_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_673_, v_lctx_676_, v_x_674_);
return v___x_677_;
}
}
LEAN_EXPORT void l_Lean_Elab_TermInfo_runMetaM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_672_ = stack[0].m_obj;
lean_object* v_ctx_673_ = stack[1].m_obj;
lean_object* v_x_674_ = stack[2].m_obj;
lean_object* v_res_678_;
v_res_678_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_672_, v_ctx_673_, v_x_674_);
stack->m_obj
 = v_res_678_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(lean_object* v_info_679_, lean_object* v_ctx_680_, lean_object* v_x_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_679_, v_ctx_680_, v_x_681_);
return v_res_683_;
}
}
lean_object* l_Lean_Elab_TermInfo_runMetaM(lean_object* v_00_u03b1_684_, lean_object* v_info_685_, lean_object* v_ctx_686_, lean_object* v_x_687_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_685_, v_ctx_686_, v_x_687_);
return v___x_689_;
}
}
LEAN_EXPORT void l_Lean_Elab_TermInfo_runMetaM_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_685_ = stack[1].m_obj;
lean_object* v_ctx_686_ = stack[2].m_obj;
lean_object* v_x_687_ = stack[3].m_obj;
lean_object* v_res_690_;
v_res_690_ = l_Lean_Elab_TermInfo_runMetaM(lean_box(0), v_info_685_, v_ctx_686_, v_x_687_);
stack->m_obj
 = v_res_690_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___boxed(lean_object* v_00_u03b1_691_, lean_object* v_info_692_, lean_object* v_ctx_693_, lean_object* v_x_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_Elab_TermInfo_runMetaM(v_00_u03b1_691_, v_info_692_, v_ctx_693_, v_x_694_);
return v_res_696_;
}
}
lean_object* l_Lean_Elab_TermInfo_format___lam__0(lean_object* v_ctx_711_, lean_object* v_toElabInfo_712_, lean_object* v_expr_713_, uint8_t v_isBinder_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v_a_735_; lean_object* v___y_745_; uint8_t v___y_746_; lean_object* v___y_749_; lean_object* v_a_750_; lean_object* v___x_753_; 
lean_inc(v___y_718_);
lean_inc_ref(v___y_717_);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
lean_inc_ref(v_expr_713_);
v___x_753_ = lean_infer_type(v_expr_713_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_755_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_753_, 1);
v___x_755_ = l_Lean_Meta_ppExpr(v_a_754_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
v_a_735_ = v_a_756_;
goto v___jp_734_;
}
else
{
lean_object* v_a_757_; 
v_a_757_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_757_);
v___y_749_ = v___x_755_;
v_a_750_ = v_a_757_;
goto v___jp_748_;
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
v_a_758_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_753_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_753_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
lean_inc(v_a_758_);
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
v___y_749_ = v___x_763_;
v_a_750_ = v_a_758_;
goto v___jp_748_;
}
}
}
v___jp_720_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
lean_inc_ref(v___y_723_);
v___x_724_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_724_, 0, v___y_723_);
v___x_725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_725_, 0, v___y_722_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v___y_721_);
v___x_729_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_711_, v_toElabInfo_712_);
v___x_732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
v___jp_734_:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_Meta_ppExpr(v_expr_713_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref_known(v___x_736_, 1);
v___x_738_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__3));
v___x_739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v_a_737_);
v___x_740_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
v___x_741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
if (v_isBinder_714_ == 0)
{
lean_object* v___x_742_; 
v___x_742_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__6));
v___y_721_ = v_a_735_;
v___y_722_ = v___x_741_;
v___y_723_ = v___x_742_;
goto v___jp_720_;
}
else
{
lean_object* v___x_743_; 
v___x_743_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__7));
v___y_721_ = v_a_735_;
v___y_722_ = v___x_741_;
v___y_723_ = v___x_743_;
goto v___jp_720_;
}
}
else
{
lean_dec(v_a_735_);
lean_dec_ref(v_toElabInfo_712_);
lean_dec_ref(v_ctx_711_);
return v___x_736_;
}
}
v___jp_744_:
{
if (v___y_746_ == 0)
{
lean_object* v___x_747_; 
lean_dec_ref(v___y_745_);
v___x_747_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__9));
v_a_735_ = v___x_747_;
goto v___jp_734_;
}
else
{
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec_ref(v_expr_713_);
lean_dec_ref(v_toElabInfo_712_);
lean_dec_ref(v_ctx_711_);
return v___y_745_;
}
}
v___jp_748_:
{
uint8_t v___x_751_; 
v___x_751_ = l_Lean_Exception_isInterrupt(v_a_750_);
if (v___x_751_ == 0)
{
uint8_t v___x_752_; 
v___x_752_ = l_Lean_Exception_isRuntime(v_a_750_);
v___y_745_ = v___y_749_;
v___y_746_ = v___x_752_;
goto v___jp_744_;
}
else
{
lean_dec_ref(v_a_750_);
v___y_745_ = v___y_749_;
v___y_746_ = v___x_751_;
goto v___jp_744_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_TermInfo_format___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_711_ = stack[0].m_obj;
lean_object* v_toElabInfo_712_ = stack[1].m_obj;
lean_object* v_expr_713_ = stack[2].m_obj;
uint8_t v_isBinder_714_ = stack[3].m_num;
lean_object* v___y_715_ = stack[4].m_obj;
lean_object* v___y_716_ = stack[5].m_obj;
lean_object* v___y_717_ = stack[6].m_obj;
lean_object* v___y_718_ = stack[7].m_obj;
lean_object* v_res_766_;
v_res_766_ = l_Lean_Elab_TermInfo_format___lam__0(v_ctx_711_, v_toElabInfo_712_, v_expr_713_, v_isBinder_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
stack->m_obj
 = v_res_766_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0___boxed(lean_object* v_ctx_767_, lean_object* v_toElabInfo_768_, lean_object* v_expr_769_, lean_object* v_isBinder_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
uint8_t v_isBinder_boxed_776_; lean_object* v_res_777_; 
v_isBinder_boxed_776_ = lean_unbox(v_isBinder_770_);
v_res_777_ = l_Lean_Elab_TermInfo_format___lam__0(v_ctx_767_, v_toElabInfo_768_, v_expr_769_, v_isBinder_boxed_776_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
return v_res_777_;
}
}
lean_object* l_Lean_Elab_TermInfo_format(lean_object* v_ctx_778_, lean_object* v_info_779_){
_start:
{
lean_object* v_toElabInfo_781_; lean_object* v_expr_782_; uint8_t v_isBinder_783_; lean_object* v___x_784_; lean_object* v___f_785_; lean_object* v___x_786_; 
v_toElabInfo_781_ = lean_ctor_get(v_info_779_, 0);
v_expr_782_ = lean_ctor_get(v_info_779_, 3);
v_isBinder_783_ = lean_ctor_get_uint8(v_info_779_, sizeof(void*)*4);
v___x_784_ = lean_box(v_isBinder_783_);
lean_inc_ref(v_expr_782_);
lean_inc_ref(v_toElabInfo_781_);
lean_inc_ref(v_ctx_778_);
v___f_785_ = lean_alloc_closure((void*)(l_Lean_Elab_TermInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_785_, 0, v_ctx_778_);
lean_closure_set(v___f_785_, 1, v_toElabInfo_781_);
lean_closure_set(v___f_785_, 2, v_expr_782_);
lean_closure_set(v___f_785_, 3, v___x_784_);
v___x_786_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_779_, v_ctx_778_, v___f_785_);
return v___x_786_;
}
}
LEAN_EXPORT void l_Lean_Elab_TermInfo_format_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_778_ = stack[0].m_obj;
lean_object* v_info_779_ = stack[1].m_obj;
lean_object* v_res_787_;
v_res_787_ = l_Lean_Elab_TermInfo_format(v_ctx_778_, v_info_779_);
stack->m_obj
 = v_res_787_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___boxed(lean_object* v_ctx_788_, lean_object* v_info_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_Elab_TermInfo_format(v_ctx_788_, v_info_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialTermInfo_format(lean_object* v_ctx_795_, lean_object* v_info_796_){
_start:
{
lean_object* v_toElabInfo_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_toElabInfo_797_ = lean_ctor_get(v_info_796_, 0);
lean_inc_ref(v_toElabInfo_797_);
lean_dec_ref(v_info_796_);
v___x_798_ = ((lean_object*)(l_Lean_Elab_PartialTermInfo_format___closed__1));
v___x_799_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_795_, v_toElabInfo_797_);
v___x_800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(lean_object* v_x_807_){
_start:
{
if (lean_obj_tag(v_x_807_) == 0)
{
lean_object* v___x_808_; 
v___x_808_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_808_;
}
else
{
lean_object* v_val_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_819_; 
v_val_809_ = lean_ctor_get(v_x_807_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_x_807_);
if (v_isSharedCheck_819_ == 0)
{
v___x_811_ = v_x_807_;
v_isShared_812_ = v_isSharedCheck_819_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_val_809_);
lean_dec(v_x_807_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_819_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_813_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_814_ = lean_expr_dbg_to_string(v_val_809_);
lean_dec(v_val_809_);
if (v_isShared_812_ == 0)
{
lean_ctor_set_tag(v___x_811_, 3);
lean_ctor_set(v___x_811_, 0, v___x_814_);
v___x_816_ = v___x_811_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_818_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; 
v___x_817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_813_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
return v___x_817_;
}
}
}
}
}
lean_object* l_Lean_Elab_CompletionInfo_format___lam__0(lean_object* v_ctx_826_, lean_object* v_lctx_827_, lean_object* v_stx_828_, lean_object* v_expectedType_x3f_829_, lean_object* v_info_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_855_; 
v___x_836_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_826_, v_lctx_827_, v_stx_828_);
v_a_837_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_855_ == 0)
{
v___x_839_ = v___x_836_;
v_isShared_840_ = v_isSharedCheck_855_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_855_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_841_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__1));
v___x_842_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v_a_837_);
v___x_843_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_842_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_829_);
v___x_846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_844_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = l_Lean_Elab_CompletionInfo_stx(v_info_830_);
v___x_850_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_826_, v___x_849_);
lean_dec(v___x_849_);
v___x_851_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_848_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_851_);
v___x_853_ = v___x_839_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_CompletionInfo_format___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_826_ = stack[0].m_obj;
lean_object* v_lctx_827_ = stack[1].m_obj;
lean_object* v_stx_828_ = stack[2].m_obj;
lean_object* v_expectedType_x3f_829_ = stack[3].m_obj;
lean_object* v_info_830_ = stack[4].m_obj;
lean_object* v___y_831_ = stack[5].m_obj;
lean_object* v___y_832_ = stack[6].m_obj;
lean_object* v___y_833_ = stack[7].m_obj;
lean_object* v___y_834_ = stack[8].m_obj;
lean_object* v_res_856_;
v_res_856_ = l_Lean_Elab_CompletionInfo_format___lam__0(v_ctx_826_, v_lctx_827_, v_stx_828_, v_expectedType_x3f_829_, v_info_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
stack->m_obj
 = v_res_856_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___boxed(lean_object* v_ctx_857_, lean_object* v_lctx_858_, lean_object* v_stx_859_, lean_object* v_expectedType_x3f_860_, lean_object* v_info_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Elab_CompletionInfo_format___lam__0(v_ctx_857_, v_lctx_858_, v_stx_859_, v_expectedType_x3f_860_, v_info_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v_info_861_);
return v_res_867_;
}
}
lean_object* l_Lean_Elab_CompletionInfo_format(lean_object* v_ctx_874_, lean_object* v_info_875_){
_start:
{
switch(lean_obj_tag(v_info_875_))
{
case 0:
{
lean_object* v_termInfo_877_; lean_object* v_expectedType_x3f_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_899_; 
v_termInfo_877_ = lean_ctor_get(v_info_875_, 0);
v_expectedType_x3f_878_ = lean_ctor_get(v_info_875_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_info_875_);
if (v_isSharedCheck_899_ == 0)
{
v___x_880_ = v_info_875_;
v_isShared_881_ = v_isSharedCheck_899_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_expectedType_x3f_878_);
lean_inc(v_termInfo_877_);
lean_dec(v_info_875_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_899_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_Elab_TermInfo_format(v_ctx_874_, v_termInfo_877_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_898_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_898_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_898_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_898_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__1));
if (v_isShared_881_ == 0)
{
lean_ctor_set_tag(v___x_880_, 5);
lean_ctor_set(v___x_880_, 1, v_a_883_);
lean_ctor_set(v___x_880_, 0, v___x_887_);
v___x_889_ = v___x_880_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_a_883_);
v___x_889_ = v_reuseFailAlloc_897_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_890_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_878_);
v___x_893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_893_);
v___x_895_ = v___x_885_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
lean_del_object(v___x_880_);
lean_dec(v_expectedType_x3f_878_);
return v___x_882_;
}
}
}
case 1:
{
lean_object* v_stx_900_; lean_object* v_lctx_901_; lean_object* v_expectedType_x3f_902_; lean_object* v___f_903_; lean_object* v___x_904_; 
v_stx_900_ = lean_ctor_get(v_info_875_, 0);
lean_inc(v_stx_900_);
v_lctx_901_ = lean_ctor_get(v_info_875_, 2);
lean_inc_ref_n(v_lctx_901_, 2);
v_expectedType_x3f_902_ = lean_ctor_get(v_info_875_, 3);
lean_inc(v_expectedType_x3f_902_);
lean_inc_ref(v_ctx_874_);
v___f_903_ = lean_alloc_closure((void*)(l_Lean_Elab_CompletionInfo_format___lam__0___boxed), 10, 5);
lean_closure_set(v___f_903_, 0, v_ctx_874_);
lean_closure_set(v___f_903_, 1, v_lctx_901_);
lean_closure_set(v___f_903_, 2, v_stx_900_);
lean_closure_set(v___f_903_, 3, v_expectedType_x3f_902_);
lean_closure_set(v___f_903_, 4, v_info_875_);
v___x_904_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_874_, v_lctx_901_, v___f_903_);
return v___x_904_;
}
default: 
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_905_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__3));
v___x_906_ = l_Lean_Elab_CompletionInfo_stx(v_info_875_);
lean_dec_ref(v_info_875_);
v___x_907_ = lean_box(0);
v___x_908_ = 0;
lean_inc(v___x_906_);
v___x_909_ = l_Lean_Syntax_formatStx(v___x_906_, v___x_907_, v___x_908_);
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_905_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_910_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_874_, v___x_906_);
lean_dec(v___x_906_);
v___x_914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_912_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
return v___x_915_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_CompletionInfo_format_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_874_ = stack[0].m_obj;
lean_object* v_info_875_ = stack[1].m_obj;
lean_object* v_res_916_;
v_res_916_ = l_Lean_Elab_CompletionInfo_format(v_ctx_874_, v_info_875_);
stack->m_obj
 = v_res_916_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___boxed(lean_object* v_ctx_917_, lean_object* v_info_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Elab_CompletionInfo_format(v_ctx_917_, v_info_918_);
return v_res_920_;
}
}
lean_object* l_Lean_Elab_CommandInfo_format(lean_object* v_ctx_924_, lean_object* v_info_925_){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_927_ = ((lean_object*)(l_Lean_Elab_CommandInfo_format___closed__1));
v___x_928_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_924_, v_info_925_);
v___x_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT void l_Lean_Elab_CommandInfo_format_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_924_ = stack[0].m_obj;
lean_object* v_info_925_ = stack[1].m_obj;
lean_object* v_res_931_;
v_res_931_ = l_Lean_Elab_CommandInfo_format(v_ctx_924_, v_info_925_);
stack->m_obj
 = v_res_931_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format___boxed(lean_object* v_ctx_932_, lean_object* v_info_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_Elab_CommandInfo_format(v_ctx_932_, v_info_933_);
return v_res_935_;
}
}
lean_object* l_Lean_Elab_OptionInfo_format(lean_object* v_ctx_939_, lean_object* v_info_940_){
_start:
{
lean_object* v_stx_942_; lean_object* v_optionName_943_; lean_object* v___x_944_; uint8_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v_stx_942_ = lean_ctor_get(v_info_940_, 0);
lean_inc(v_stx_942_);
v_optionName_943_ = lean_ctor_get(v_info_940_, 1);
lean_inc(v_optionName_943_);
lean_dec_ref(v_info_940_);
v___x_944_ = ((lean_object*)(l_Lean_Elab_OptionInfo_format___closed__1));
v___x_945_ = 1;
v___x_946_ = l_Lean_Name_toString(v_optionName_943_, v___x_945_);
v___x_947_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
v___x_948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_944_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_948_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_939_, v_stx_942_);
lean_dec(v_stx_942_);
v___x_952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT void l_Lean_Elab_OptionInfo_format_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_939_ = stack[0].m_obj;
lean_object* v_info_940_ = stack[1].m_obj;
lean_object* v_res_954_;
v_res_954_ = l_Lean_Elab_OptionInfo_format(v_ctx_939_, v_info_940_);
stack->m_obj
 = v_res_954_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format___boxed(lean_object* v_ctx_955_, lean_object* v_info_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Elab_OptionInfo_format(v_ctx_955_, v_info_956_);
return v_res_958_;
}
}
lean_object* l_Lean_Elab_ErrorNameInfo_format(lean_object* v_ctx_962_, lean_object* v_info_963_){
_start:
{
lean_object* v_stx_965_; lean_object* v_errorName_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_982_; 
v_stx_965_ = lean_ctor_get(v_info_963_, 0);
v_errorName_966_ = lean_ctor_get(v_info_963_, 1);
v_isSharedCheck_982_ = !lean_is_exclusive(v_info_963_);
if (v_isSharedCheck_982_ == 0)
{
v___x_968_ = v_info_963_;
v_isShared_969_ = v_isSharedCheck_982_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_errorName_966_);
lean_inc(v_stx_965_);
lean_dec(v_info_963_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_982_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; uint8_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_970_ = ((lean_object*)(l_Lean_Elab_ErrorNameInfo_format___closed__1));
v___x_971_ = 1;
v___x_972_ = l_Lean_Name_toString(v_errorName_966_, v___x_971_);
v___x_973_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
if (v_isShared_969_ == 0)
{
lean_ctor_set_tag(v___x_968_, 5);
lean_ctor_set(v___x_968_, 1, v___x_973_);
lean_ctor_set(v___x_968_, 0, v___x_970_);
v___x_975_ = v___x_968_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v___x_973_);
v___x_975_ = v_reuseFailAlloc_981_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_976_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_962_, v_stx_965_);
lean_dec(v_stx_965_);
v___x_979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_977_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
return v___x_980_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ErrorNameInfo_format_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_962_ = stack[0].m_obj;
lean_object* v_info_963_ = stack[1].m_obj;
lean_object* v_res_983_;
v_res_983_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_962_, v_info_963_);
stack->m_obj
 = v_res_983_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format___boxed(lean_object* v_ctx_984_, lean_object* v_info_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_984_, v_info_985_);
return v_res_987_;
}
}
lean_object* l_Lean_Elab_FieldInfo_format___lam__0(lean_object* v_val_994_, lean_object* v_fieldName_995_, lean_object* v_ctx_996_, lean_object* v_stx_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; 
lean_inc(v___y_1001_);
lean_inc_ref(v___y_1000_);
lean_inc(v___y_999_);
lean_inc_ref(v___y_998_);
lean_inc_ref(v_val_994_);
v___x_1003_ = lean_infer_type(v_val_994_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = l_Lean_Meta_ppExpr(v_a_1004_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1036_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1036_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1036_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_Meta_ppExpr(v_val_994_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1035_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1013_ = v___x_1010_;
v_isShared_1014_ = v_isSharedCheck_1035_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1010_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1035_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; uint8_t v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1015_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__1));
v___x_1016_ = 1;
v___x_1017_ = l_Lean_Name_toString(v_fieldName_995_, v___x_1016_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set_tag(v___x_1008_, 3);
lean_ctor_set(v___x_1008_, 0, v___x_1017_);
v___x_1019_ = v___x_1008_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1015_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v_a_1006_);
v___x_1024_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__3));
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1023_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set(v___x_1026_, 1, v_a_1011_);
v___x_1027_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_996_, v_stx_997_);
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1030_);
v___x_1032_ = v___x_1013_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
else
{
lean_del_object(v___x_1008_);
lean_dec(v_a_1006_);
lean_dec_ref(v_ctx_996_);
lean_dec(v_fieldName_995_);
return v___x_1010_;
}
}
}
else
{
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec_ref(v_ctx_996_);
lean_dec(v_fieldName_995_);
lean_dec_ref(v_val_994_);
return v___x_1005_;
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec_ref(v_ctx_996_);
lean_dec(v_fieldName_995_);
lean_dec_ref(v_val_994_);
v_a_1037_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1003_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1003_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_FieldInfo_format___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_994_ = stack[0].m_obj;
lean_object* v_fieldName_995_ = stack[1].m_obj;
lean_object* v_ctx_996_ = stack[2].m_obj;
lean_object* v_stx_997_ = stack[3].m_obj;
lean_object* v___y_998_ = stack[4].m_obj;
lean_object* v___y_999_ = stack[5].m_obj;
lean_object* v___y_1000_ = stack[6].m_obj;
lean_object* v___y_1001_ = stack[7].m_obj;
lean_object* v_res_1045_;
v_res_1045_ = l_Lean_Elab_FieldInfo_format___lam__0(v_val_994_, v_fieldName_995_, v_ctx_996_, v_stx_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
stack->m_obj
 = v_res_1045_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0___boxed(lean_object* v_val_1046_, lean_object* v_fieldName_1047_, lean_object* v_ctx_1048_, lean_object* v_stx_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_Elab_FieldInfo_format___lam__0(v_val_1046_, v_fieldName_1047_, v_ctx_1048_, v_stx_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v_stx_1049_);
return v_res_1055_;
}
}
lean_object* l_Lean_Elab_FieldInfo_format(lean_object* v_ctx_1056_, lean_object* v_info_1057_){
_start:
{
lean_object* v_fieldName_1059_; lean_object* v_lctx_1060_; lean_object* v_val_1061_; lean_object* v_stx_1062_; lean_object* v___f_1063_; lean_object* v___x_1064_; 
v_fieldName_1059_ = lean_ctor_get(v_info_1057_, 1);
lean_inc(v_fieldName_1059_);
v_lctx_1060_ = lean_ctor_get(v_info_1057_, 2);
lean_inc_ref(v_lctx_1060_);
v_val_1061_ = lean_ctor_get(v_info_1057_, 3);
lean_inc_ref(v_val_1061_);
v_stx_1062_ = lean_ctor_get(v_info_1057_, 4);
lean_inc(v_stx_1062_);
lean_dec_ref(v_info_1057_);
lean_inc_ref(v_ctx_1056_);
v___f_1063_ = lean_alloc_closure((void*)(l_Lean_Elab_FieldInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1063_, 0, v_val_1061_);
lean_closure_set(v___f_1063_, 1, v_fieldName_1059_);
lean_closure_set(v___f_1063_, 2, v_ctx_1056_);
lean_closure_set(v___f_1063_, 3, v_stx_1062_);
v___x_1064_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1056_, v_lctx_1060_, v___f_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT void l_Lean_Elab_FieldInfo_format_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1056_ = stack[0].m_obj;
lean_object* v_info_1057_ = stack[1].m_obj;
lean_object* v_res_1065_;
v_res_1065_ = l_Lean_Elab_FieldInfo_format(v_ctx_1056_, v_info_1057_);
stack->m_obj
 = v_res_1065_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___boxed(lean_object* v_ctx_1066_, lean_object* v_info_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_Elab_FieldInfo_format(v_ctx_1066_, v_info_1067_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(lean_object* v_pre_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_){
_start:
{
if (lean_obj_tag(v_x_1072_) == 0)
{
lean_dec(v_pre_1070_);
return v_x_1071_;
}
else
{
lean_object* v_head_1073_; lean_object* v_tail_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1083_; 
v_head_1073_ = lean_ctor_get(v_x_1072_, 0);
v_tail_1074_ = lean_ctor_get(v_x_1072_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_x_1072_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1076_ = v_x_1072_;
v_isShared_1077_ = v_isSharedCheck_1083_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_tail_1074_);
lean_inc(v_head_1073_);
lean_dec(v_x_1072_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1083_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
lean_inc(v_pre_1070_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set_tag(v___x_1076_, 5);
lean_ctor_set(v___x_1076_, 1, v_pre_1070_);
lean_ctor_set(v___x_1076_, 0, v_x_1071_);
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_x_1071_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_pre_1070_);
v___x_1079_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v_head_1073_);
v_x_1071_ = v___x_1080_;
v_x_1072_ = v_tail_1074_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(lean_object* v_pre_1084_, lean_object* v_x_1085_){
_start:
{
if (lean_obj_tag(v_x_1085_) == 0)
{
lean_object* v___x_1086_; 
lean_dec(v_pre_1084_);
v___x_1086_ = lean_box(0);
return v___x_1086_;
}
else
{
lean_object* v_head_1087_; lean_object* v_tail_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1096_; 
v_head_1087_ = lean_ctor_get(v_x_1085_, 0);
v_tail_1088_ = lean_ctor_get(v_x_1085_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_x_1085_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1090_ = v_x_1085_;
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_tail_1088_);
lean_inc(v_head_1087_);
lean_dec(v_x_1085_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
lean_inc(v_pre_1084_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set_tag(v___x_1090_, 5);
lean_ctor_set(v___x_1090_, 1, v_head_1087_);
lean_ctor_set(v___x_1090_, 0, v_pre_1084_);
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_pre_1084_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_head_1087_);
v___x_1093_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(v_pre_1084_, v___x_1093_, v_tail_1088_);
return v___x_1094_;
}
}
}
}
}
lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(lean_object* v_x_1097_, lean_object* v_x_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
if (lean_obj_tag(v_x_1097_) == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = l_List_reverse___redArg(v_x_1098_);
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
else
{
lean_object* v_head_1106_; lean_object* v_tail_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1125_; 
v_head_1106_ = lean_ctor_get(v_x_1097_, 0);
v_tail_1107_ = lean_ctor_get(v_x_1097_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_x_1097_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1109_ = v_x_1097_;
v_isShared_1110_ = v_isSharedCheck_1125_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_tail_1107_);
lean_inc(v_head_1106_);
lean_dec(v_x_1097_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1125_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_Meta_ppGoal(v_head_1106_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v_head_1106_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1114_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1111_, 1);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 1, v_x_1098_);
lean_ctor_set(v___x_1109_, 0, v_a_1112_);
v___x_1114_ = v___x_1109_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1112_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_x_1098_);
v___x_1114_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
v_x_1097_ = v_tail_1107_;
v_x_1098_ = v___x_1114_;
goto _start;
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_del_object(v___x_1109_);
lean_dec(v_tail_1107_);
lean_dec(v_x_1098_);
v_a_1117_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1111_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1111_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1097_ = stack[0].m_obj;
lean_object* v_x_1098_ = stack[1].m_obj;
lean_object* v___y_1099_ = stack[2].m_obj;
lean_object* v___y_1100_ = stack[3].m_obj;
lean_object* v___y_1101_ = stack[4].m_obj;
lean_object* v___y_1102_ = stack[5].m_obj;
lean_object* v_res_1126_;
v_res_1126_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_x_1097_, v_x_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
stack->m_obj
 = v_res_1126_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(lean_object* v_x_1127_, lean_object* v_x_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_x_1127_, v_x_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
return v_res_1134_;
}
}
lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0(lean_object* v_goals_1138_, lean_object* v___x_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_goals_1138_, v___x_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1155_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1155_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1155_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1150_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1151_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1150_, v_a_1146_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1151_);
v___x_1153_ = v___x_1148_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
v_a_1156_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1145_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1145_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ContextInfo_ppGoals___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goals_1138_ = stack[0].m_obj;
lean_object* v___x_1139_ = stack[1].m_obj;
lean_object* v___y_1140_ = stack[2].m_obj;
lean_object* v___y_1141_ = stack[3].m_obj;
lean_object* v___y_1142_ = stack[4].m_obj;
lean_object* v___y_1143_ = stack[5].m_obj;
lean_object* v_res_1164_;
v_res_1164_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0(v_goals_1138_, v___x_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
stack->m_obj
 = v_res_1164_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(lean_object* v_goals_1165_, lean_object* v___x_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0(v_goals_1165_, v___x_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
return v_res_1172_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
return v___x_1174_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1175_ = lean_unsigned_to_nat(32u);
v___x_1176_ = lean_mk_empty_array_with_capacity(v___x_1175_);
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
return v___x_1177_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2(void){
_start:
{
size_t v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1178_ = ((size_t)5ULL);
v___x_1179_ = lean_unsigned_to_nat(0u);
v___x_1180_ = lean_unsigned_to_nat(32u);
v___x_1181_ = lean_mk_empty_array_with_capacity(v___x_1180_);
v___x_1182_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__1, &l_Lean_Elab_ContextInfo_ppGoals___closed__1_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1);
v___x_1183_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
lean_ctor_set(v___x_1183_, 1, v___x_1181_);
lean_ctor_set(v___x_1183_, 2, v___x_1179_);
lean_ctor_set(v___x_1183_, 3, v___x_1179_);
lean_ctor_set_usize(v___x_1183_, 4, v___x_1178_);
return v___x_1183_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1184_ = lean_box(1);
v___x_1185_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_1186_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__0, &l_Lean_Elab_ContextInfo_ppGoals___closed__0_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0);
v___x_1187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v___x_1185_);
lean_ctor_set(v___x_1187_, 2, v___x_1184_);
return v___x_1187_;
}
}
lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object* v_ctx_1191_, lean_object* v_goals_1192_){
_start:
{
uint8_t v___x_1194_; 
v___x_1194_ = l_List_isEmpty___redArg(v_goals_1192_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___f_1197_; lean_object* v___x_1198_; 
v___x_1195_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_1196_ = lean_box(0);
v___f_1197_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1197_, 0, v_goals_1192_);
lean_closure_set(v___f_1197_, 1, v___x_1196_);
v___x_1198_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1191_, v___x_1195_, v___f_1197_);
return v___x_1198_;
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_dec(v_goals_1192_);
lean_dec_ref(v_ctx_1191_);
v___x_1199_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___closed__5));
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
return v___x_1200_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_ContextInfo_ppGoals_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1191_ = stack[0].m_obj;
lean_object* v_goals_1192_ = stack[1].m_obj;
lean_object* v_res_1201_;
v_res_1201_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctx_1191_, v_goals_1192_);
stack->m_obj
 = v_res_1201_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object* v_ctx_1202_, lean_object* v_goals_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctx_1202_, v_goals_1203_);
return v_res_1205_;
}
}
lean_object* l_Lean_Elab_TacticInfo_format(lean_object* v_ctx_1215_, lean_object* v_info_1216_){
_start:
{
lean_object* v_toCommandContextInfo_1218_; lean_object* v_parentDecl_x3f_1219_; lean_object* v_autoImplicits_1220_; lean_object* v_env_1221_; lean_object* v_cmdEnv_x3f_1222_; lean_object* v_fileMap_1223_; lean_object* v_options_1224_; lean_object* v_currNamespace_1225_; lean_object* v_openDecls_1226_; lean_object* v_ngen_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1269_; 
v_toCommandContextInfo_1218_ = lean_ctor_get(v_ctx_1215_, 0);
lean_inc_ref(v_toCommandContextInfo_1218_);
v_parentDecl_x3f_1219_ = lean_ctor_get(v_ctx_1215_, 1);
v_autoImplicits_1220_ = lean_ctor_get(v_ctx_1215_, 2);
v_env_1221_ = lean_ctor_get(v_toCommandContextInfo_1218_, 0);
v_cmdEnv_x3f_1222_ = lean_ctor_get(v_toCommandContextInfo_1218_, 1);
v_fileMap_1223_ = lean_ctor_get(v_toCommandContextInfo_1218_, 2);
v_options_1224_ = lean_ctor_get(v_toCommandContextInfo_1218_, 4);
v_currNamespace_1225_ = lean_ctor_get(v_toCommandContextInfo_1218_, 5);
v_openDecls_1226_ = lean_ctor_get(v_toCommandContextInfo_1218_, 6);
v_ngen_1227_ = lean_ctor_get(v_toCommandContextInfo_1218_, 7);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_toCommandContextInfo_1218_);
if (v_isSharedCheck_1269_ == 0)
{
lean_object* v_unused_1270_; 
v_unused_1270_ = lean_ctor_get(v_toCommandContextInfo_1218_, 3);
lean_dec(v_unused_1270_);
v___x_1229_ = v_toCommandContextInfo_1218_;
v_isShared_1230_ = v_isSharedCheck_1269_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_ngen_1227_);
lean_inc(v_openDecls_1226_);
lean_inc(v_currNamespace_1225_);
lean_inc(v_options_1224_);
lean_inc(v_fileMap_1223_);
lean_inc(v_cmdEnv_x3f_1222_);
lean_inc(v_env_1221_);
lean_dec(v_toCommandContextInfo_1218_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1269_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v_toElabInfo_1231_; lean_object* v_mctxBefore_1232_; lean_object* v_goalsBefore_1233_; lean_object* v_mctxAfter_1234_; lean_object* v_goalsAfter_1235_; lean_object* v___x_1237_; 
v_toElabInfo_1231_ = lean_ctor_get(v_info_1216_, 0);
lean_inc_ref(v_toElabInfo_1231_);
v_mctxBefore_1232_ = lean_ctor_get(v_info_1216_, 1);
lean_inc_ref(v_mctxBefore_1232_);
v_goalsBefore_1233_ = lean_ctor_get(v_info_1216_, 2);
lean_inc(v_goalsBefore_1233_);
v_mctxAfter_1234_ = lean_ctor_get(v_info_1216_, 3);
lean_inc_ref(v_mctxAfter_1234_);
v_goalsAfter_1235_ = lean_ctor_get(v_info_1216_, 4);
lean_inc(v_goalsAfter_1235_);
lean_dec_ref(v_info_1216_);
lean_inc_ref(v_ngen_1227_);
lean_inc(v_openDecls_1226_);
lean_inc(v_currNamespace_1225_);
lean_inc_ref(v_options_1224_);
lean_inc_ref(v_fileMap_1223_);
lean_inc(v_cmdEnv_x3f_1222_);
lean_inc_ref(v_env_1221_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 3, v_mctxBefore_1232_);
v___x_1237_ = v___x_1229_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_env_1221_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_cmdEnv_x3f_1222_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v_fileMap_1223_);
lean_ctor_set(v_reuseFailAlloc_1268_, 3, v_mctxBefore_1232_);
lean_ctor_set(v_reuseFailAlloc_1268_, 4, v_options_1224_);
lean_ctor_set(v_reuseFailAlloc_1268_, 5, v_currNamespace_1225_);
lean_ctor_set(v_reuseFailAlloc_1268_, 6, v_openDecls_1226_);
lean_ctor_set(v_reuseFailAlloc_1268_, 7, v_ngen_1227_);
v___x_1237_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v_ctxB_1238_; lean_object* v___x_1239_; lean_object* v_ctxA_1240_; lean_object* v___x_1241_; 
lean_inc_ref_n(v_autoImplicits_1220_, 2);
lean_inc_n(v_parentDecl_x3f_1219_, 2);
v_ctxB_1238_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxB_1238_, 0, v___x_1237_);
lean_ctor_set(v_ctxB_1238_, 1, v_parentDecl_x3f_1219_);
lean_ctor_set(v_ctxB_1238_, 2, v_autoImplicits_1220_);
v___x_1239_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1239_, 0, v_env_1221_);
lean_ctor_set(v___x_1239_, 1, v_cmdEnv_x3f_1222_);
lean_ctor_set(v___x_1239_, 2, v_fileMap_1223_);
lean_ctor_set(v___x_1239_, 3, v_mctxAfter_1234_);
lean_ctor_set(v___x_1239_, 4, v_options_1224_);
lean_ctor_set(v___x_1239_, 5, v_currNamespace_1225_);
lean_ctor_set(v___x_1239_, 6, v_openDecls_1226_);
lean_ctor_set(v___x_1239_, 7, v_ngen_1227_);
v_ctxA_1240_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxA_1240_, 0, v___x_1239_);
lean_ctor_set(v_ctxA_1240_, 1, v_parentDecl_x3f_1219_);
lean_ctor_set(v_ctxA_1240_, 2, v_autoImplicits_1220_);
v___x_1241_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxB_1238_, v_goalsBefore_1233_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1243_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1243_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxA_1240_, v_goalsAfter_1235_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1267_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1267_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1267_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_stx_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1265_; 
v_stx_1248_ = lean_ctor_get(v_toElabInfo_1231_, 1);
lean_inc(v_stx_1248_);
v___x_1249_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__1));
v___x_1250_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1215_, v_toElabInfo_1231_);
v___x_1251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1249_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
v___x_1252_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1251_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
v___x_1254_ = lean_box(0);
v___x_1255_ = 0;
v___x_1256_ = l_Lean_Syntax_formatStx(v_stx_1248_, v___x_1254_, v___x_1255_);
v___x_1257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1253_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__3));
v___x_1259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v_a_1242_);
v___x_1261_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__5));
v___x_1262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
lean_ctor_set(v___x_1263_, 1, v_a_1244_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1263_);
v___x_1265_ = v___x_1246_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
else
{
lean_dec(v_a_1242_);
lean_dec_ref(v_toElabInfo_1231_);
lean_dec_ref(v_ctx_1215_);
return v___x_1243_;
}
}
else
{
lean_dec_ref_known(v_ctxA_1240_, 3);
lean_dec(v_goalsAfter_1235_);
lean_dec_ref(v_toElabInfo_1231_);
lean_dec_ref(v_ctx_1215_);
return v___x_1241_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_TacticInfo_format_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1215_ = stack[0].m_obj;
lean_object* v_info_1216_ = stack[1].m_obj;
lean_object* v_res_1271_;
v_res_1271_ = l_Lean_Elab_TacticInfo_format(v_ctx_1215_, v_info_1216_);
stack->m_obj
 = v_res_1271_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format___boxed(lean_object* v_ctx_1272_, lean_object* v_info_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_Elab_TacticInfo_format(v_ctx_1272_, v_info_1273_);
return v_res_1275_;
}
}
lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object* v_ctx_1282_, lean_object* v_info_1283_){
_start:
{
lean_object* v_lctx_1285_; lean_object* v_stx_1286_; lean_object* v_output_1287_; lean_object* v___x_1288_; lean_object* v_a_1289_; lean_object* v___x_1290_; lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1303_; 
v_lctx_1285_ = lean_ctor_get(v_info_1283_, 0);
lean_inc_ref_n(v_lctx_1285_, 2);
v_stx_1286_ = lean_ctor_get(v_info_1283_, 1);
lean_inc(v_stx_1286_);
v_output_1287_ = lean_ctor_get(v_info_1283_, 2);
lean_inc(v_output_1287_);
lean_dec_ref(v_info_1283_);
v___x_1288_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1282_, v_lctx_1285_, v_stx_1286_);
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref(v___x_1288_);
v___x_1290_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1282_, v_lctx_1285_, v_output_1287_);
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1303_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1303_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1295_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__1));
v___x_1296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
lean_ctor_set(v___x_1296_, 1, v_a_1289_);
v___x_1297_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__3));
v___x_1298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1296_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v_a_1291_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1299_);
v___x_1301_ = v___x_1293_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_MacroExpansionInfo_format_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1282_ = stack[0].m_obj;
lean_object* v_info_1283_ = stack[1].m_obj;
lean_object* v_res_1304_;
v_res_1304_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1282_, v_info_1283_);
stack->m_obj
 = v_res_1304_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object* v_ctx_1305_, lean_object* v_info_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1305_, v_info_1306_);
lean_dec_ref(v_ctx_1305_);
return v_res_1308_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__0(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
return v___x_1310_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__1(void){
_start:
{
uint8_t v___x_1311_; size_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1311_ = 1;
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__0, &l_Lean_Elab_UserWidgetInfo_format___closed__0_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__0);
v___x_1314_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
lean_ctor_set_usize(v___x_1314_, 2, v___x_1312_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*3, v___x_1311_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_UserWidgetInfo_format(lean_object* v_info_1318_){
_start:
{
lean_object* v_toWidgetInstance_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1348_; 
v_toWidgetInstance_1319_ = lean_ctor_get(v_info_1318_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_info_1318_);
if (v_isSharedCheck_1348_ == 0)
{
lean_object* v_unused_1349_; 
v_unused_1349_ = lean_ctor_get(v_info_1318_, 1);
lean_dec(v_unused_1349_);
v___x_1321_ = v_info_1318_;
v_isShared_1322_ = v_isSharedCheck_1348_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_toWidgetInstance_1319_);
lean_dec(v_info_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1348_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v_id_1323_; lean_object* v_props_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v_fst_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1346_; 
v_id_1323_ = lean_ctor_get(v_toWidgetInstance_1319_, 0);
lean_inc(v_id_1323_);
v_props_1324_ = lean_ctor_get(v_toWidgetInstance_1319_, 1);
lean_inc_ref(v_props_1324_);
lean_dec_ref(v_toWidgetInstance_1319_);
v___x_1325_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__1, &l_Lean_Elab_UserWidgetInfo_format___closed__1_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__1);
v___x_1326_ = lean_apply_1(v_props_1324_, v___x_1325_);
v_fst_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; 
v_unused_1347_ = lean_ctor_get(v___x_1326_, 1);
lean_dec(v_unused_1347_);
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1346_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_fst_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1346_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1331_ = ((lean_object*)(l_Lean_Elab_UserWidgetInfo_format___closed__3));
v___x_1332_ = 1;
v___x_1333_ = l_Lean_Name_toString(v_id_1323_, v___x_1332_);
v___x_1334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set_tag(v___x_1329_, 5);
lean_ctor_set(v___x_1329_, 1, v___x_1334_);
lean_ctor_set(v___x_1329_, 0, v___x_1331_);
v___x_1336_ = v___x_1329_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1331_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1337_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
if (v_isShared_1322_ == 0)
{
lean_ctor_set_tag(v___x_1321_, 5);
lean_ctor_set(v___x_1321_, 1, v___x_1337_);
lean_ctor_set(v___x_1321_, 0, v___x_1336_);
v___x_1339_ = v___x_1321_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1340_ = lean_unsigned_to_nat(80u);
v___x_1341_ = l_Lean_Json_pretty(v_fst_1327_, v___x_1340_);
v___x_1342_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
v___x_1343_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1339_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
return v___x_1343_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FVarAliasInfo_format(lean_object* v_info_1356_){
_start:
{
lean_object* v_userName_1357_; lean_object* v_id_1358_; lean_object* v_baseId_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v_userName_1357_ = lean_ctor_get(v_info_1356_, 0);
lean_inc(v_userName_1357_);
v_id_1358_ = lean_ctor_get(v_info_1356_, 1);
lean_inc(v_id_1358_);
v_baseId_1359_ = lean_ctor_get(v_info_1356_, 2);
lean_inc(v_baseId_1359_);
lean_dec_ref(v_info_1356_);
v___x_1360_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__1));
v___x_1361_ = l_Lean_Name_eraseMacroScopes(v_userName_1357_);
lean_dec(v_userName_1357_);
v___x_1362_ = 1;
v___x_1363_ = l_Lean_Name_toString(v___x_1361_, v___x_1362_);
v___x_1364_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
v___x_1365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1360_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v___x_1366_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_1367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = l_Lean_Name_toString(v_id_1358_, v___x_1362_);
v___x_1369_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
v___x_1370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1367_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__3));
v___x_1372_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1370_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
v___x_1373_ = l_Lean_Name_toString(v_baseId_1359_, v___x_1362_);
v___x_1374_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
v___x_1375_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1372_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format(lean_object* v_ctx_1379_, lean_object* v_info_1380_){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1381_ = ((lean_object*)(l_Lean_Elab_FieldRedeclInfo_format___closed__1));
v___x_1382_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1379_, v_info_1380_);
v___x_1383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1381_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format___boxed(lean_object* v_ctx_1384_, lean_object* v_info_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1384_, v_info_1385_);
lean_dec(v_info_1385_);
return v_res_1386_;
}
}
lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f(lean_object* v_ppCtx_1389_, lean_object* v_info_1390_){
_start:
{
lean_object* v_mkDocString_x3f_1392_; 
v_mkDocString_x3f_1392_ = lean_ctor_get(v_info_1390_, 2);
lean_inc(v_mkDocString_x3f_1392_);
lean_dec_ref(v_info_1390_);
if (lean_obj_tag(v_mkDocString_x3f_1392_) == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
lean_dec_ref(v_ppCtx_1389_);
v___x_1393_ = lean_box(0);
v___x_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
return v___x_1394_;
}
else
{
lean_object* v_val_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1427_; 
v_val_1395_ = lean_ctor_get(v_mkDocString_x3f_1392_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_mkDocString_x3f_1392_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1397_ = v_mkDocString_x3f_1392_;
v_isShared_1398_ = v_isSharedCheck_1427_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_val_1395_);
lean_dec(v_mkDocString_x3f_1392_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1427_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; 
v___x_1399_ = lean_apply_2(v_val_1395_, v_ppCtx_1389_, lean_box(0));
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1410_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1410_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1410_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v_a_1400_);
v___x_1405_ = v___x_1397_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1407_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1405_);
v___x_1407_ = v___x_1402_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1426_; 
v_a_1411_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1413_ = v___x_1399_;
v_isShared_1414_ = v_isSharedCheck_1426_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1399_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1426_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1415_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0));
v___x_1416_ = lean_io_error_to_string(v_a_1411_);
v___x_1417_ = lean_string_append(v___x_1415_, v___x_1416_);
lean_dec_ref(v___x_1416_);
v___x_1418_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1419_ = lean_string_append(v___x_1417_, v___x_1418_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1419_);
v___x_1421_ = v___x_1397_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1423_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set_tag(v___x_1413_, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1421_);
v___x_1423_ = v___x_1413_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_DelabTermInfo_docString_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_ppCtx_1389_ = stack[0].m_obj;
lean_object* v_info_1390_ = stack[1].m_obj;
lean_object* v_res_1428_;
v_res_1428_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_ppCtx_1389_, v_info_1390_);
stack->m_obj
 = v_res_1428_;
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
lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object* v_ctx_1465_, lean_object* v_info_1466_){
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
LEAN_EXPORT void l_Lean_Elab_DelabTermInfo_format_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1465_ = stack[0].m_obj;
lean_object* v_info_1466_ = stack[1].m_obj;
lean_object* v_res_1562_;
v_res_1562_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1465_, v_info_1466_);
stack->m_obj
 = v_res_1562_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object* v_ctx_1563_, lean_object* v_info_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1563_, v_info_1564_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object* v_ctx_1570_, lean_object* v_info_1571_){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1572_ = ((lean_object*)(l_Lean_Elab_ChoiceInfo_format___closed__1));
v___x_1573_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1570_, v_info_1571_);
v___x_1574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1572_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceResolutionInfo_format(lean_object* v_ctx_1587_, lean_object* v_info_1588_){
_start:
{
lean_object* v_stx_1589_; lean_object* v_chosenAltIdx_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1618_; 
v_stx_1589_ = lean_ctor_get(v_info_1588_, 0);
v_chosenAltIdx_1590_ = lean_ctor_get(v_info_1588_, 1);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_info_1588_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1592_ = v_info_1588_;
v_isShared_1593_ = v_isSharedCheck_1618_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_chosenAltIdx_1590_);
lean_inc(v_stx_1589_);
lean_dec(v_info_1588_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1618_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1594_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__1));
lean_inc(v_chosenAltIdx_1590_);
v___x_1595_ = l_Nat_reprFast(v_chosenAltIdx_1590_);
v___x_1596_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 5);
lean_ctor_set(v___x_1592_, 1, v___x_1596_);
lean_ctor_set(v___x_1592_, 0, v___x_1594_);
v___x_1598_ = v___x_1592_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1599_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__3));
v___x_1600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1598_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
v___x_1601_ = l_Lean_Syntax_getNumArgs(v_stx_1589_);
v___x_1602_ = l_Nat_reprFast(v___x_1601_);
v___x_1603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
v___x_1604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1600_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
v___x_1605_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__5));
v___x_1606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1604_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = l_Lean_Syntax_getArg(v_stx_1589_, v_chosenAltIdx_1590_);
lean_dec(v_chosenAltIdx_1590_);
v___x_1608_ = l_Lean_Syntax_getKind(v___x_1607_);
v___x_1609_ = 1;
v___x_1610_ = l_Lean_Name_toString(v___x_1608_, v___x_1609_);
v___x_1611_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
v___x_1612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1606_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__7));
v___x_1614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1587_, v_stx_1589_);
lean_dec(v_stx_1589_);
v___x_1616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
return v___x_1616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object* v_ctx_1622_, lean_object* v_info_1623_){
_start:
{
lean_object* v_stx_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v_stx_1624_ = lean_ctor_get(v_info_1623_, 1);
v___x_1625_ = ((lean_object*)(l_Lean_Elab_DocInfo_format___closed__1));
lean_inc(v_stx_1624_);
v___x_1626_ = l_Lean_Syntax_getKind(v_stx_1624_);
v___x_1627_ = 1;
v___x_1628_ = l_Lean_Name_toString(v___x_1626_, v___x_1627_);
v___x_1629_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
v___x_1630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1625_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1622_, v_info_1623_);
v___x_1634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object* v_ctx_1638_, lean_object* v_info_1639_){
_start:
{
lean_object* v_toElabInfo_1640_; lean_object* v_name_1641_; uint8_t v_kind_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v_toElabInfo_1640_ = lean_ctor_get(v_info_1639_, 0);
lean_inc_ref(v_toElabInfo_1640_);
v_name_1641_ = lean_ctor_get(v_info_1639_, 1);
lean_inc(v_name_1641_);
v_kind_1642_ = lean_ctor_get_uint8(v_info_1639_, sizeof(void*)*2);
lean_dec_ref(v_info_1639_);
v___x_1643_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__1));
v___x_1644_ = 1;
v___x_1645_ = l_Lean_Name_toString(v_name_1641_, v___x_1644_);
v___x_1646_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
v___x_1647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1643_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__5));
v___x_1649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = lean_unsigned_to_nat(0u);
v___x_1651_ = l_Lean_Elab_instReprDocElabKind_repr(v_kind_1642_, v___x_1650_);
v___x_1652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1649_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__7));
v___x_1654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1638_, v_toElabInfo_1640_);
v___x_1656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1654_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
return v___x_1656_;
}
}
lean_object* l_Lean_Elab_Info_format(lean_object* v_ctx_1657_, lean_object* v_x_1658_){
_start:
{
switch(lean_obj_tag(v_x_1658_))
{
case 0:
{
lean_object* v_i_1660_; lean_object* v___x_1661_; 
v_i_1660_ = lean_ctor_get(v_x_1658_, 0);
lean_inc_ref(v_i_1660_);
lean_dec_ref_known(v_x_1658_, 1);
v___x_1661_ = l_Lean_Elab_TacticInfo_format(v_ctx_1657_, v_i_1660_);
return v___x_1661_;
}
case 1:
{
lean_object* v_i_1662_; lean_object* v___x_1663_; 
v_i_1662_ = lean_ctor_get(v_x_1658_, 0);
lean_inc_ref(v_i_1662_);
lean_dec_ref_known(v_x_1658_, 1);
v___x_1663_ = l_Lean_Elab_TermInfo_format(v_ctx_1657_, v_i_1662_);
return v___x_1663_;
}
case 2:
{
lean_object* v_i_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1672_; 
v_i_1664_ = lean_ctor_get(v_x_1658_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_x_1658_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1666_ = v_x_1658_;
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_i_1664_);
lean_dec(v_x_1658_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1668_ = l_Lean_Elab_PartialTermInfo_format(v_ctx_1657_, v_i_1664_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set_tag(v___x_1666_, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1668_);
v___x_1670_ = v___x_1666_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
case 3:
{
lean_object* v_i_1673_; lean_object* v___x_1674_; 
v_i_1673_ = lean_ctor_get(v_x_1658_, 0);
lean_inc_ref(v_i_1673_);
lean_dec_ref_known(v_x_1658_, 1);
v___x_1674_ = l_Lean_Elab_CommandInfo_format(v_ctx_1657_, v_i_1673_);
return v___x_1674_;
}
case 4:
{
lean_object* v_i_1675_; lean_object* v___x_1676_; 
v_i_1675_ = lean_ctor_get(v_x_1658_, 0);
lean_inc_ref(v_i_1675_);
lean_dec_ref_known(v_x_1658_, 1);
v___x_1676_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1657_, v_i_1675_);
lean_dec_ref(v_ctx_1657_);
return v___x_1676_;
}
case 5:
{
lean_object* v_i_1677_; lean_object* v___x_1678_; 
v_i_1677_ = lean_ctor_get(v_x_1658_, 0);
lean_inc_ref(v_i_1677_);
lean_dec_ref_known(v_x_1658_, 1);
v___x_1678_ = l_Lean_Elab_OptionInfo_format(v_ctx_1657_, v_i_1677_);
return v___x_1678_;
}
case 6:
{
lean_object* v_i_1679_; lean_object* v___x_1680_; 
v_i_1679_ = lean_ctor_get(v_x_1658_, 0);
lean_inc_ref(v_i_1679_);
lean_dec_ref_known(v_x_1658_, 1);
v___x_1680_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_1657_, v_i_1679_);
return v___x_1680_;
}
case 7:
{
lean_object* v_i_1681_; lean_object* v___x_1682_; 
v_i_1681_ = lean_ctor_get(v_x_1658_, 0);
lean_inc_ref(v_i_1681_);
lean_dec_ref_known(v_x_1658_, 1);
v___x_1682_ = l_Lean_Elab_FieldInfo_format(v_ctx_1657_, v_i_1681_);
return v___x_1682_;
}
case 8:
{
lean_object* v_i_1683_; lean_object* v___x_1684_; 
v_i_1683_ = lean_ctor_get(v_x_1658_, 0);
lean_inc_ref(v_i_1683_);
lean_dec_ref_known(v_x_1658_, 1);
v___x_1684_ = l_Lean_Elab_CompletionInfo_format(v_ctx_1657_, v_i_1683_);
return v___x_1684_;
}
case 9:
{
lean_object* v_i_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1693_; 
lean_dec_ref(v_ctx_1657_);
v_i_1685_ = lean_ctor_get(v_x_1658_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_x_1658_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1687_ = v_x_1658_;
v_isShared_1688_ = v_isSharedCheck_1693_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_i_1685_);
lean_dec(v_x_1658_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1693_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1689_ = l_Lean_Elab_UserWidgetInfo_format(v_i_1685_);
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
case 10:
{
lean_object* v_i_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1702_; 
lean_dec_ref(v_ctx_1657_);
v_i_1694_ = lean_ctor_get(v_x_1658_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_x_1658_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1696_ = v_x_1658_;
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_i_1694_);
lean_dec(v_x_1658_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1698_ = l_Lean_Elab_CustomInfo_format(v_i_1694_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set_tag(v___x_1696_, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1698_);
v___x_1700_ = v___x_1696_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
case 11:
{
lean_object* v_i_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1711_; 
lean_dec_ref(v_ctx_1657_);
v_i_1703_ = lean_ctor_get(v_x_1658_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_x_1658_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1705_ = v_x_1658_;
v_isShared_1706_ = v_isSharedCheck_1711_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_i_1703_);
lean_dec(v_x_1658_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1711_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1707_ = l_Lean_Elab_FVarAliasInfo_format(v_i_1703_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set_tag(v___x_1705_, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1707_);
v___x_1709_ = v___x_1705_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
case 12:
{
lean_object* v_i_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1720_; 
v_i_1712_ = lean_ctor_get(v_x_1658_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_x_1658_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1714_ = v_x_1658_;
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_i_1712_);
lean_dec(v_x_1658_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1716_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1657_, v_i_1712_);
lean_dec(v_i_1712_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set_tag(v___x_1714_, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1716_);
v___x_1718_ = v___x_1714_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
case 13:
{
lean_object* v_i_1721_; lean_object* v___x_1722_; 
v_i_1721_ = lean_ctor_get(v_x_1658_, 0);
lean_inc_ref(v_i_1721_);
lean_dec_ref_known(v_x_1658_, 1);
v___x_1722_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1657_, v_i_1721_);
return v___x_1722_;
}
case 14:
{
lean_object* v_i_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1731_; 
v_i_1723_ = lean_ctor_get(v_x_1658_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_x_1658_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1725_ = v_x_1658_;
v_isShared_1726_ = v_isSharedCheck_1731_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_i_1723_);
lean_dec(v_x_1658_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1731_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1727_ = l_Lean_Elab_ChoiceInfo_format(v_ctx_1657_, v_i_1723_);
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
case 15:
{
lean_object* v_i_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1740_; 
v_i_1732_ = lean_ctor_get(v_x_1658_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_x_1658_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1734_ = v_x_1658_;
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_i_1732_);
lean_dec(v_x_1658_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1736_ = l_Lean_Elab_ChoiceResolutionInfo_format(v_ctx_1657_, v_i_1732_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set_tag(v___x_1734_, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1736_);
v___x_1738_ = v___x_1734_;
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
case 16:
{
lean_object* v_i_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1749_; 
v_i_1741_ = lean_ctor_get(v_x_1658_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_x_1658_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1743_ = v_x_1658_;
v_isShared_1744_ = v_isSharedCheck_1749_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_i_1741_);
lean_dec(v_x_1658_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1749_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; lean_object* v___x_1747_; 
v___x_1745_ = l_Lean_Elab_DocInfo_format(v_ctx_1657_, v_i_1741_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set_tag(v___x_1743_, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1745_);
v___x_1747_ = v___x_1743_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
default: 
{
lean_object* v_i_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1758_; 
v_i_1750_ = lean_ctor_get(v_x_1658_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_x_1658_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1752_ = v_x_1658_;
v_isShared_1753_ = v_isSharedCheck_1758_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_i_1750_);
lean_dec(v_x_1658_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1758_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1754_ = l_Lean_Elab_DocElabInfo_format(v_ctx_1657_, v_i_1750_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set_tag(v___x_1752_, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1754_);
v___x_1756_ = v___x_1752_;
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
}
}
LEAN_EXPORT void l_Lean_Elab_Info_format_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1657_ = stack[0].m_obj;
lean_object* v_x_1658_ = stack[1].m_obj;
lean_object* v_res_1759_;
v_res_1759_ = l_Lean_Elab_Info_format(v_ctx_1657_, v_x_1658_);
stack->m_obj
 = v_res_1759_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object* v_ctx_1760_, lean_object* v_x_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_Elab_Info_format(v_ctx_1760_, v_x_1761_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object* v_x_1764_, lean_object* v_x_1765_){
_start:
{
if (lean_obj_tag(v_x_1765_) == 0)
{
return v_x_1764_;
}
else
{
lean_object* v_head_1766_; lean_object* v_tail_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_head_1766_ = lean_ctor_get(v_x_1765_, 0);
v_tail_1767_ = lean_ctor_get(v_x_1765_, 1);
v___x_1768_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2));
v___x_1769_ = lean_string_append(v_x_1764_, v___x_1768_);
v___x_1770_ = lean_expr_dbg_to_string(v_head_1766_);
v___x_1771_ = lean_string_append(v___x_1769_, v___x_1770_);
lean_dec_ref(v___x_1770_);
v_x_1764_ = v___x_1771_;
v_x_1765_ = v_tail_1767_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object* v_x_1773_, lean_object* v_x_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v_x_1773_, v_x_1774_);
lean_dec(v_x_1774_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object* v_x_1778_){
_start:
{
if (lean_obj_tag(v_x_1778_) == 0)
{
lean_object* v___x_1779_; 
v___x_1779_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0));
return v___x_1779_;
}
else
{
lean_object* v_tail_1780_; 
v_tail_1780_ = lean_ctor_get(v_x_1778_, 1);
if (lean_obj_tag(v_tail_1780_) == 0)
{
lean_object* v_head_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_head_1781_ = lean_ctor_get(v_x_1778_, 0);
v___x_1782_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1783_ = lean_expr_dbg_to_string(v_head_1781_);
v___x_1784_ = lean_string_append(v___x_1782_, v___x_1783_);
lean_dec_ref(v___x_1783_);
v___x_1785_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1786_ = lean_string_append(v___x_1784_, v___x_1785_);
return v___x_1786_;
}
else
{
lean_object* v_head_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint32_t v___x_1792_; lean_object* v___x_1793_; 
v_head_1787_ = lean_ctor_get(v_x_1778_, 0);
v___x_1788_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1789_ = lean_expr_dbg_to_string(v_head_1787_);
v___x_1790_ = lean_string_append(v___x_1788_, v___x_1789_);
lean_dec_ref(v___x_1789_);
v___x_1791_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v___x_1790_, v_tail_1780_);
v___x_1792_ = 93;
v___x_1793_ = lean_string_push(v___x_1791_, v___x_1792_);
return v___x_1793_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object* v_x_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v_x_1794_);
lean_dec(v_x_1794_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object* v_ctx_1802_){
_start:
{
switch(lean_obj_tag(v_ctx_1802_))
{
case 0:
{
lean_object* v___x_1803_; 
lean_dec_ref_known(v_ctx_1802_, 1);
v___x_1803_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__1));
return v___x_1803_;
}
case 1:
{
lean_object* v_parentDecl_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1817_; 
v_parentDecl_1804_ = lean_ctor_get(v_ctx_1802_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_ctx_1802_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1806_ = v_ctx_1802_;
v_isShared_1807_ = v_isSharedCheck_1817_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_parentDecl_1804_);
lean_dec(v_ctx_1802_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1817_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1808_; uint8_t v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1808_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__2));
v___x_1809_ = 1;
v___x_1810_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_parentDecl_1804_, v___x_1809_);
v___x_1811_ = lean_string_append(v___x_1808_, v___x_1810_);
lean_dec_ref(v___x_1810_);
v___x_1812_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1813_ = lean_string_append(v___x_1811_, v___x_1812_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set_tag(v___x_1806_, 3);
lean_ctor_set(v___x_1806_, 0, v___x_1813_);
v___x_1815_ = v___x_1806_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
default: 
{
lean_object* v_autoImplicits_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1833_; 
v_autoImplicits_1818_ = lean_ctor_get(v_ctx_1802_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_ctx_1802_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1820_ = v_ctx_1802_;
v_isShared_1821_ = v_isSharedCheck_1833_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_autoImplicits_1818_);
lean_dec(v_ctx_1802_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1833_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1831_; 
v___x_1822_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__3));
v___x_1823_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__4));
v___x_1824_ = lean_array_to_list(v_autoImplicits_1818_);
v___x_1825_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v___x_1824_);
lean_dec(v___x_1824_);
v___x_1826_ = lean_string_append(v___x_1823_, v___x_1825_);
lean_dec_ref(v___x_1825_);
v___x_1827_ = lean_string_append(v___x_1822_, v___x_1826_);
lean_dec_ref(v___x_1826_);
v___x_1828_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1829_ = lean_string_append(v___x_1827_, v___x_1828_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set_tag(v___x_1820_, 3);
lean_ctor_set(v___x_1820_, 0, v___x_1829_);
v___x_1831_ = v___x_1820_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
}
lean_object* l_Lean_Elab_InfoTree_format(lean_object* v_tree_1843_, lean_object* v_ctx_x3f_1844_){
_start:
{
switch(lean_obj_tag(v_tree_1843_))
{
case 0:
{
lean_object* v_i_1846_; lean_object* v_t_1847_; lean_object* v___x_1848_; 
v_i_1846_ = lean_ctor_get(v_tree_1843_, 0);
lean_inc_ref(v_i_1846_);
v_t_1847_ = lean_ctor_get(v_tree_1843_, 1);
lean_inc_ref(v_t_1847_);
lean_dec_ref_known(v_tree_1843_, 2);
v___x_1848_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1846_, v_ctx_x3f_1844_);
v_tree_1843_ = v_t_1847_;
v_ctx_x3f_1844_ = v___x_1848_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_ctx_x3f_1844_) == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_dec_ref_known(v_tree_1843_, 2);
v___x_1850_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__1));
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
return v___x_1851_;
}
else
{
lean_object* v_i_1852_; lean_object* v_children_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1903_; 
v_i_1852_ = lean_ctor_get(v_tree_1843_, 0);
v_children_1853_ = lean_ctor_get(v_tree_1843_, 1);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_tree_1843_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1855_ = v_tree_1843_;
v_isShared_1856_ = v_isSharedCheck_1903_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_children_1853_);
lean_inc(v_i_1852_);
lean_dec(v_tree_1843_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1903_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v_val_1857_; lean_object* v___x_1858_; 
v_val_1857_ = lean_ctor_get(v_ctx_x3f_1844_, 0);
lean_inc_ref(v_i_1852_);
lean_inc(v_val_1857_);
v___x_1858_ = l_Lean_Elab_Info_format(v_val_1857_, v_i_1852_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1902_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1902_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1902_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v_size_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; 
v_size_1863_ = lean_ctor_get(v_children_1853_, 2);
v___x_1864_ = lean_unsigned_to_nat(0u);
v___x_1865_ = lean_nat_dec_eq(v_size_1863_, v___x_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_del_object(v___x_1861_);
v___x_1866_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_1844_, v_i_1852_);
lean_dec_ref(v_i_1852_);
v___x_1867_ = l_Lean_PersistentArray_toList___redArg(v_children_1853_);
lean_dec_ref(v_children_1853_);
v___x_1868_ = lean_box(0);
v___x_1869_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1866_, v___x_1867_, v___x_1868_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1885_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1885_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1885_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1874_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1856_ == 0)
{
lean_ctor_set_tag(v___x_1855_, 5);
lean_ctor_set(v___x_1855_, 1, v_a_1859_);
lean_ctor_set(v___x_1855_, 0, v___x_1874_);
v___x_1876_ = v___x_1855_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1874_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_a_1859_);
v___x_1876_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1877_ = lean_box(1);
v___x_1878_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1877_, v_a_1870_);
v___x_1879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1876_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = l_Std_Format_nestD(v___x_1879_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1880_);
v___x_1882_ = v___x_1872_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_a_1859_);
lean_del_object(v___x_1855_);
v_a_1886_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1869_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1869_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
lean_dec_ref(v_children_1853_);
lean_dec_ref(v_i_1852_);
lean_dec_ref_known(v_ctx_x3f_1844_, 1);
v___x_1894_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1856_ == 0)
{
lean_ctor_set_tag(v___x_1855_, 5);
lean_ctor_set(v___x_1855_, 1, v_a_1859_);
lean_ctor_set(v___x_1855_, 0, v___x_1894_);
v___x_1896_ = v___x_1855_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_a_1859_);
v___x_1896_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1897_ = l_Std_Format_nestD(v___x_1896_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1897_);
v___x_1899_ = v___x_1861_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
}
else
{
lean_del_object(v___x_1855_);
lean_dec_ref(v_children_1853_);
lean_dec_ref(v_i_1852_);
lean_dec_ref_known(v_ctx_x3f_1844_, 1);
return v___x_1858_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1917_; 
lean_dec(v_ctx_x3f_1844_);
v_mvarId_1904_ = lean_ctor_get(v_tree_1843_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_tree_1843_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1906_ = v_tree_1843_;
v_isShared_1907_ = v_isSharedCheck_1917_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_mvarId_1904_);
lean_dec(v_tree_1843_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1917_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; uint8_t v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1908_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__5));
v___x_1909_ = 1;
v___x_1910_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_1904_, v___x_1909_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set_tag(v___x_1906_, 3);
lean_ctor_set(v___x_1906_, 0, v___x_1910_);
v___x_1912_ = v___x_1906_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1908_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = l_Std_Format_nestD(v___x_1913_);
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
return v___x_1915_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_format_0interp(lean_interpreter_value* stack)
{
lean_object* v_tree_1843_ = stack[0].m_obj;
lean_object* v_ctx_x3f_1844_ = stack[1].m_obj;
lean_object* v_res_1918_;
v_res_1918_ = l_Lean_Elab_InfoTree_format(v_tree_1843_, v_ctx_x3f_1844_);
stack->m_obj
 = v_res_1918_;
}
lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object* v___x_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_){
_start:
{
if (lean_obj_tag(v_x_1920_) == 0)
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
lean_dec(v___x_1919_);
v___x_1923_ = l_List_reverse___redArg(v_x_1921_);
v___x_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
return v___x_1924_;
}
else
{
lean_object* v_head_1925_; lean_object* v_tail_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1944_; 
v_head_1925_ = lean_ctor_get(v_x_1920_, 0);
v_tail_1926_ = lean_ctor_get(v_x_1920_, 1);
v_isSharedCheck_1944_ = !lean_is_exclusive(v_x_1920_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1928_ = v_x_1920_;
v_isShared_1929_ = v_isSharedCheck_1944_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_tail_1926_);
lean_inc(v_head_1925_);
lean_dec(v_x_1920_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1944_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; 
lean_inc(v___x_1919_);
v___x_1930_ = l_Lean_Elab_InfoTree_format(v_head_1925_, v___x_1919_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1933_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref_known(v___x_1930_, 1);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 1, v_x_1921_);
lean_ctor_set(v___x_1928_, 0, v_a_1931_);
v___x_1933_ = v___x_1928_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1931_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_x_1921_);
v___x_1933_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
v_x_1920_ = v_tail_1926_;
v_x_1921_ = v___x_1933_;
goto _start;
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_del_object(v___x_1928_);
lean_dec(v_tail_1926_);
lean_dec(v_x_1921_);
lean_dec(v___x_1919_);
v_a_1936_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1930_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1930_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
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
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1919_ = stack[0].m_obj;
lean_object* v_x_1920_ = stack[1].m_obj;
lean_object* v_x_1921_ = stack[2].m_obj;
lean_object* v_res_1945_;
v_res_1945_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1919_, v_x_1920_, v_x_1921_);
stack->m_obj
 = v_res_1945_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object* v___x_1946_, lean_object* v_x_1947_, lean_object* v_x_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1946_, v_x_1947_, v_x_1948_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object* v_tree_1951_, lean_object* v_ctx_x3f_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_Elab_InfoTree_format(v_tree_1951_, v_ctx_x3f_1952_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object* v_f_1955_, lean_object* v_s_1956_){
_start:
{
uint8_t v_enabled_1957_; lean_object* v_assignment_1958_; lean_object* v_lazyAssignment_1959_; lean_object* v_trees_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1968_; 
v_enabled_1957_ = lean_ctor_get_uint8(v_s_1956_, sizeof(void*)*3);
v_assignment_1958_ = lean_ctor_get(v_s_1956_, 0);
v_lazyAssignment_1959_ = lean_ctor_get(v_s_1956_, 1);
v_trees_1960_ = lean_ctor_get(v_s_1956_, 2);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_s_1956_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1962_ = v_s_1956_;
v_isShared_1963_ = v_isSharedCheck_1968_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_trees_1960_);
lean_inc(v_lazyAssignment_1959_);
lean_inc(v_assignment_1958_);
lean_dec(v_s_1956_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1968_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; lean_object* v___x_1966_; 
v___x_1964_ = lean_apply_1(v_f_1955_, v_trees_1960_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 2, v___x_1964_);
v___x_1966_ = v___x_1962_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_assignment_1958_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_lazyAssignment_1959_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v___x_1964_);
lean_ctor_set_uint8(v_reuseFailAlloc_1967_, sizeof(void*)*3, v_enabled_1957_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object* v_inst_1969_, lean_object* v_f_1970_){
_start:
{
lean_object* v_modifyInfoState_1971_; lean_object* v___f_1972_; lean_object* v___x_1973_; 
v_modifyInfoState_1971_ = lean_ctor_get(v_inst_1969_, 1);
lean_inc(v_modifyInfoState_1971_);
lean_dec_ref(v_inst_1969_);
v___f_1972_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1972_, 0, v_f_1970_);
v___x_1973_ = lean_apply_1(v_modifyInfoState_1971_, v___f_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object* v_m_1974_, lean_object* v_inst_1975_, lean_object* v_f_1976_){
_start:
{
lean_object* v_modifyInfoState_1977_; lean_object* v___f_1978_; lean_object* v___x_1979_; 
v_modifyInfoState_1977_ = lean_ctor_get(v_inst_1975_, 1);
lean_inc(v_modifyInfoState_1977_);
lean_dec_ref(v_inst_1975_);
v___f_1978_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1978_, 0, v_f_1976_);
v___x_1979_ = lean_apply_1(v_modifyInfoState_1977_, v___f_1978_);
return v___x_1979_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1980_ = lean_unsigned_to_nat(32u);
v___x_1981_ = lean_mk_empty_array_with_capacity(v___x_1980_);
v___x_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
return v___x_1982_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1983_ = ((size_t)5ULL);
v___x_1984_ = lean_unsigned_to_nat(0u);
v___x_1985_ = lean_unsigned_to_nat(32u);
v___x_1986_ = lean_mk_empty_array_with_capacity(v___x_1985_);
v___x_1987_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0);
v___x_1988_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
lean_ctor_set(v___x_1988_, 1, v___x_1986_);
lean_ctor_set(v___x_1988_, 2, v___x_1984_);
lean_ctor_set(v___x_1988_, 3, v___x_1984_);
lean_ctor_set_usize(v___x_1988_, 4, v___x_1983_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object* v_s_1989_){
_start:
{
uint8_t v_enabled_1990_; lean_object* v_assignment_1991_; lean_object* v_lazyAssignment_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2000_; 
v_enabled_1990_ = lean_ctor_get_uint8(v_s_1989_, sizeof(void*)*3);
v_assignment_1991_ = lean_ctor_get(v_s_1989_, 0);
v_lazyAssignment_1992_ = lean_ctor_get(v_s_1989_, 1);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_s_1989_);
if (v_isSharedCheck_2000_ == 0)
{
lean_object* v_unused_2001_; 
v_unused_2001_ = lean_ctor_get(v_s_1989_, 2);
lean_dec(v_unused_2001_);
v___x_1994_ = v_s_1989_;
v_isShared_1995_ = v_isSharedCheck_2000_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_lazyAssignment_1992_);
lean_inc(v_assignment_1991_);
lean_dec(v_s_1989_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2000_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; lean_object* v___x_1998_; 
v___x_1996_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 2, v___x_1996_);
v___x_1998_ = v___x_1994_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_assignment_1991_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_lazyAssignment_1992_);
lean_ctor_set(v_reuseFailAlloc_1999_, 2, v___x_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_1999_, sizeof(void*)*3, v_enabled_1990_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object* v_toPure_2002_, lean_object* v_trees_2003_, lean_object* v_____r_2004_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = lean_apply_2(v_toPure_2002_, lean_box(0), v_trees_2003_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object* v_toPure_2006_, lean_object* v_modifyInfoState_2007_, lean_object* v___f_2008_, lean_object* v_toBind_2009_, lean_object* v_____do__lift_2010_){
_start:
{
lean_object* v_trees_2011_; lean_object* v___f_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_trees_2011_ = lean_ctor_get(v_____do__lift_2010_, 2);
lean_inc_ref(v_trees_2011_);
lean_dec_ref(v_____do__lift_2010_);
v___f_2012_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2012_, 0, v_toPure_2006_);
lean_closure_set(v___f_2012_, 1, v_trees_2011_);
v___x_2013_ = lean_apply_1(v_modifyInfoState_2007_, v___f_2008_);
v___x_2014_ = lean_apply_4(v_toBind_2009_, lean_box(0), lean_box(0), v___x_2013_, v___f_2012_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object* v_inst_2016_, lean_object* v_inst_2017_){
_start:
{
lean_object* v_toApplicative_2018_; lean_object* v_toBind_2019_; lean_object* v_getInfoState_2020_; lean_object* v_modifyInfoState_2021_; lean_object* v_toPure_2022_; lean_object* v___f_2023_; lean_object* v___f_2024_; lean_object* v___x_2025_; 
v_toApplicative_2018_ = lean_ctor_get(v_inst_2016_, 0);
lean_inc_ref(v_toApplicative_2018_);
v_toBind_2019_ = lean_ctor_get(v_inst_2016_, 1);
lean_inc_n(v_toBind_2019_, 2);
lean_dec_ref(v_inst_2016_);
v_getInfoState_2020_ = lean_ctor_get(v_inst_2017_, 0);
lean_inc(v_getInfoState_2020_);
v_modifyInfoState_2021_ = lean_ctor_get(v_inst_2017_, 1);
lean_inc(v_modifyInfoState_2021_);
lean_dec_ref(v_inst_2017_);
v_toPure_2022_ = lean_ctor_get(v_toApplicative_2018_, 1);
lean_inc(v_toPure_2022_);
lean_dec_ref(v_toApplicative_2018_);
v___f_2023_ = ((lean_object*)(l_Lean_Elab_getResetInfoTrees___redArg___closed__0));
v___f_2024_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2024_, 0, v_toPure_2022_);
lean_closure_set(v___f_2024_, 1, v_modifyInfoState_2021_);
lean_closure_set(v___f_2024_, 2, v___f_2023_);
lean_closure_set(v___f_2024_, 3, v_toBind_2019_);
v___x_2025_ = lean_apply_4(v_toBind_2019_, lean_box(0), lean_box(0), v_getInfoState_2020_, v___f_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object* v_m_2026_, lean_object* v_inst_2027_, lean_object* v_inst_2028_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2027_, v_inst_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object* v_t_2030_, lean_object* v_s_2031_){
_start:
{
uint8_t v_enabled_2032_; lean_object* v_assignment_2033_; lean_object* v_lazyAssignment_2034_; lean_object* v_trees_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2043_; 
v_enabled_2032_ = lean_ctor_get_uint8(v_s_2031_, sizeof(void*)*3);
v_assignment_2033_ = lean_ctor_get(v_s_2031_, 0);
v_lazyAssignment_2034_ = lean_ctor_get(v_s_2031_, 1);
v_trees_2035_ = lean_ctor_get(v_s_2031_, 2);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_s_2031_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2037_ = v_s_2031_;
v_isShared_2038_ = v_isSharedCheck_2043_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_trees_2035_);
lean_inc(v_lazyAssignment_2034_);
lean_inc(v_assignment_2033_);
lean_dec(v_s_2031_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2043_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2039_ = l_Lean_PersistentArray_push___redArg(v_trees_2035_, v_t_2030_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 2, v___x_2039_);
v___x_2041_ = v___x_2037_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_assignment_2033_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_lazyAssignment_2034_);
lean_ctor_set(v_reuseFailAlloc_2042_, 2, v___x_2039_);
lean_ctor_set_uint8(v_reuseFailAlloc_2042_, sizeof(void*)*3, v_enabled_2032_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object* v_toPure_2044_, lean_object* v_modifyInfoState_2045_, lean_object* v___f_2046_, lean_object* v_____do__lift_2047_){
_start:
{
uint8_t v_enabled_2048_; 
v_enabled_2048_ = lean_ctor_get_uint8(v_____do__lift_2047_, sizeof(void*)*3);
if (v_enabled_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
lean_dec_ref(v___f_2046_);
lean_dec(v_modifyInfoState_2045_);
v___x_2049_ = lean_box(0);
v___x_2050_ = lean_apply_2(v_toPure_2044_, lean_box(0), v___x_2049_);
return v___x_2050_;
}
else
{
lean_object* v___x_2051_; 
lean_dec(v_toPure_2044_);
v___x_2051_ = lean_apply_1(v_modifyInfoState_2045_, v___f_2046_);
return v___x_2051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object* v_toPure_2052_, lean_object* v_modifyInfoState_2053_, lean_object* v___f_2054_, lean_object* v_____do__lift_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Lean_Elab_pushInfoTree___redArg___lam__1(v_toPure_2052_, v_modifyInfoState_2053_, v___f_2054_, v_____do__lift_2055_);
lean_dec_ref(v_____do__lift_2055_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object* v_inst_2057_, lean_object* v_inst_2058_, lean_object* v_t_2059_){
_start:
{
lean_object* v_toApplicative_2060_; lean_object* v_toBind_2061_; lean_object* v_getInfoState_2062_; lean_object* v_modifyInfoState_2063_; lean_object* v_toPure_2064_; lean_object* v___f_2065_; lean_object* v___f_2066_; lean_object* v___x_2067_; 
v_toApplicative_2060_ = lean_ctor_get(v_inst_2057_, 0);
lean_inc_ref(v_toApplicative_2060_);
v_toBind_2061_ = lean_ctor_get(v_inst_2057_, 1);
lean_inc(v_toBind_2061_);
lean_dec_ref(v_inst_2057_);
v_getInfoState_2062_ = lean_ctor_get(v_inst_2058_, 0);
lean_inc(v_getInfoState_2062_);
v_modifyInfoState_2063_ = lean_ctor_get(v_inst_2058_, 1);
lean_inc(v_modifyInfoState_2063_);
lean_dec_ref(v_inst_2058_);
v_toPure_2064_ = lean_ctor_get(v_toApplicative_2060_, 1);
lean_inc(v_toPure_2064_);
lean_dec_ref(v_toApplicative_2060_);
v___f_2065_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2065_, 0, v_t_2059_);
v___f_2066_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2066_, 0, v_toPure_2064_);
lean_closure_set(v___f_2066_, 1, v_modifyInfoState_2063_);
lean_closure_set(v___f_2066_, 2, v___f_2065_);
v___x_2067_ = lean_apply_4(v_toBind_2061_, lean_box(0), lean_box(0), v_getInfoState_2062_, v___f_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object* v_m_2068_, lean_object* v_inst_2069_, lean_object* v_inst_2070_, lean_object* v_t_2071_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2069_, v_inst_2070_, v_t_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object* v_toPure_2073_, lean_object* v_t_2074_, lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_____do__lift_2077_){
_start:
{
uint8_t v_enabled_2078_; 
v_enabled_2078_ = lean_ctor_get_uint8(v_____do__lift_2077_, sizeof(void*)*3);
if (v_enabled_2078_ == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
lean_dec_ref(v_inst_2076_);
lean_dec_ref(v_inst_2075_);
lean_dec_ref(v_t_2074_);
v___x_2079_ = lean_box(0);
v___x_2080_ = lean_apply_2(v_toPure_2073_, lean_box(0), v___x_2079_);
return v___x_2080_;
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
lean_dec(v_toPure_2073_);
v___x_2081_ = lean_unsigned_to_nat(32u);
v___x_2082_ = lean_mk_empty_array_with_capacity(v___x_2081_);
lean_dec_ref(v___x_2082_);
v___x_2083_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2084_, 0, v_t_2074_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
v___x_2085_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2075_, v_inst_2076_, v___x_2084_);
return v___x_2085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object* v_toPure_2086_, lean_object* v_t_2087_, lean_object* v_inst_2088_, lean_object* v_inst_2089_, lean_object* v_____do__lift_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_Elab_pushInfoLeaf___redArg___lam__0(v_toPure_2086_, v_t_2087_, v_inst_2088_, v_inst_2089_, v_____do__lift_2090_);
lean_dec_ref(v_____do__lift_2090_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object* v_inst_2092_, lean_object* v_inst_2093_, lean_object* v_t_2094_){
_start:
{
lean_object* v_toApplicative_2095_; lean_object* v_toBind_2096_; lean_object* v_getInfoState_2097_; lean_object* v_toPure_2098_; lean_object* v___f_2099_; lean_object* v___x_2100_; 
v_toApplicative_2095_ = lean_ctor_get(v_inst_2092_, 0);
v_toBind_2096_ = lean_ctor_get(v_inst_2092_, 1);
lean_inc(v_toBind_2096_);
v_getInfoState_2097_ = lean_ctor_get(v_inst_2093_, 0);
lean_inc(v_getInfoState_2097_);
v_toPure_2098_ = lean_ctor_get(v_toApplicative_2095_, 1);
lean_inc(v_toPure_2098_);
v___f_2099_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2099_, 0, v_toPure_2098_);
lean_closure_set(v___f_2099_, 1, v_t_2094_);
lean_closure_set(v___f_2099_, 2, v_inst_2092_);
lean_closure_set(v___f_2099_, 3, v_inst_2093_);
v___x_2100_ = lean_apply_4(v_toBind_2096_, lean_box(0), lean_box(0), v_getInfoState_2097_, v___f_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object* v_m_2101_, lean_object* v_inst_2102_, lean_object* v_inst_2103_, lean_object* v_t_2104_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2102_, v_inst_2103_, v_t_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object* v_inst_2106_, lean_object* v_inst_2107_, lean_object* v_info_2108_){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2109_, 0, v_info_2108_);
v___x_2110_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2106_, v_inst_2107_, v___x_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object* v_m_2111_, lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_info_2114_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_2112_, v_inst_2113_, v_info_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object* v_stx_2116_, lean_object* v_expectedType_x3f_2117_, lean_object* v_inst_2118_, lean_object* v_inst_2119_, lean_object* v_____do__lift_2120_){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2121_ = lean_box(0);
v___x_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
lean_ctor_set(v___x_2122_, 1, v_stx_2116_);
v___x_2123_ = l_Lean_LocalContext_empty;
v___x_2124_ = 0;
v___x_2125_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2125_, 0, v___x_2122_);
lean_ctor_set(v___x_2125_, 1, v___x_2123_);
lean_ctor_set(v___x_2125_, 2, v_expectedType_x3f_2117_);
lean_ctor_set(v___x_2125_, 3, v_____do__lift_2120_);
lean_ctor_set_uint8(v___x_2125_, sizeof(void*)*4, v___x_2124_);
lean_ctor_set_uint8(v___x_2125_, sizeof(void*)*4 + 1, v___x_2124_);
v___x_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
v___x_2127_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2118_, v_inst_2119_, v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object* v_inst_2128_, lean_object* v_inst_2129_, lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v_stx_2132_, lean_object* v_n_2133_, lean_object* v_expectedType_x3f_2134_){
_start:
{
lean_object* v_toBind_2135_; lean_object* v___f_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v_toBind_2135_ = lean_ctor_get(v_inst_2128_, 1);
lean_inc(v_toBind_2135_);
lean_inc_ref(v_inst_2128_);
v___f_2136_ = lean_alloc_closure((void*)(l_Lean_Elab_addConstInfo___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2136_, 0, v_stx_2132_);
lean_closure_set(v___f_2136_, 1, v_expectedType_x3f_2134_);
lean_closure_set(v___f_2136_, 2, v_inst_2128_);
lean_closure_set(v___f_2136_, 3, v_inst_2129_);
v___x_2137_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_2128_, v_inst_2130_, v_inst_2131_, v_n_2133_);
v___x_2138_ = lean_apply_4(v_toBind_2135_, lean_box(0), lean_box(0), v___x_2137_, v___f_2136_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object* v_m_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_inst_2142_, lean_object* v_inst_2143_, lean_object* v_stx_2144_, lean_object* v_n_2145_, lean_object* v_expectedType_x3f_2146_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_Lean_Elab_addConstInfo___redArg(v_inst_2140_, v_inst_2141_, v_inst_2142_, v_inst_2143_, v_stx_2144_, v_n_2145_, v_expectedType_x3f_2146_);
return v___x_2147_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v___x_2151_; lean_object* v_infoState_2152_; uint8_t v_enabled_2153_; 
v___x_2151_ = lean_st_ref_get(v___y_2149_);
v_infoState_2152_ = lean_ctor_get(v___x_2151_, 8);
lean_inc_ref(v_infoState_2152_);
lean_dec(v___x_2151_);
v_enabled_2153_ = lean_ctor_get_uint8(v_infoState_2152_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2152_);
if (v_enabled_2153_ == 0)
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
lean_dec_ref(v_t_2148_);
v___x_2154_ = lean_box(0);
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
return v___x_2155_;
}
else
{
lean_object* v___x_2156_; lean_object* v_infoState_2157_; lean_object* v_env_2158_; lean_object* v_nextMacroScope_2159_; lean_object* v_ngen_2160_; lean_object* v_auxDeclNGen_2161_; lean_object* v_traceState_2162_; lean_object* v_cache_2163_; lean_object* v_recordedDeps_2164_; lean_object* v_messages_2165_; lean_object* v_snapshotTasks_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2188_; 
v___x_2156_ = lean_st_ref_take(v___y_2149_);
v_infoState_2157_ = lean_ctor_get(v___x_2156_, 8);
v_env_2158_ = lean_ctor_get(v___x_2156_, 0);
v_nextMacroScope_2159_ = lean_ctor_get(v___x_2156_, 1);
v_ngen_2160_ = lean_ctor_get(v___x_2156_, 2);
v_auxDeclNGen_2161_ = lean_ctor_get(v___x_2156_, 3);
v_traceState_2162_ = lean_ctor_get(v___x_2156_, 4);
v_cache_2163_ = lean_ctor_get(v___x_2156_, 5);
v_recordedDeps_2164_ = lean_ctor_get(v___x_2156_, 6);
v_messages_2165_ = lean_ctor_get(v___x_2156_, 7);
v_snapshotTasks_2166_ = lean_ctor_get(v___x_2156_, 9);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2168_ = v___x_2156_;
v_isShared_2169_ = v_isSharedCheck_2188_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_snapshotTasks_2166_);
lean_inc(v_infoState_2157_);
lean_inc(v_messages_2165_);
lean_inc(v_recordedDeps_2164_);
lean_inc(v_cache_2163_);
lean_inc(v_traceState_2162_);
lean_inc(v_auxDeclNGen_2161_);
lean_inc(v_ngen_2160_);
lean_inc(v_nextMacroScope_2159_);
lean_inc(v_env_2158_);
lean_dec(v___x_2156_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2188_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
uint8_t v_enabled_2170_; lean_object* v_assignment_2171_; lean_object* v_lazyAssignment_2172_; lean_object* v_trees_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2187_; 
v_enabled_2170_ = lean_ctor_get_uint8(v_infoState_2157_, sizeof(void*)*3);
v_assignment_2171_ = lean_ctor_get(v_infoState_2157_, 0);
v_lazyAssignment_2172_ = lean_ctor_get(v_infoState_2157_, 1);
v_trees_2173_ = lean_ctor_get(v_infoState_2157_, 2);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_infoState_2157_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2175_ = v_infoState_2157_;
v_isShared_2176_ = v_isSharedCheck_2187_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_trees_2173_);
lean_inc(v_lazyAssignment_2172_);
lean_inc(v_assignment_2171_);
lean_dec(v_infoState_2157_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2187_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2180_; 
v___x_2177_ = lean_box(0);
v___x_2178_ = l_Lean_PersistentArray_push___redArg(v_trees_2173_, v_t_2148_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 2, v___x_2178_);
v___x_2180_ = v___x_2175_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_assignment_2171_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_lazyAssignment_2172_);
lean_ctor_set(v_reuseFailAlloc_2186_, 2, v___x_2178_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, sizeof(void*)*3, v_enabled_2170_);
v___x_2180_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
lean_object* v___x_2182_; 
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 8, v___x_2180_);
v___x_2182_ = v___x_2168_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_env_2158_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_nextMacroScope_2159_);
lean_ctor_set(v_reuseFailAlloc_2185_, 2, v_ngen_2160_);
lean_ctor_set(v_reuseFailAlloc_2185_, 3, v_auxDeclNGen_2161_);
lean_ctor_set(v_reuseFailAlloc_2185_, 4, v_traceState_2162_);
lean_ctor_set(v_reuseFailAlloc_2185_, 5, v_cache_2163_);
lean_ctor_set(v_reuseFailAlloc_2185_, 6, v_recordedDeps_2164_);
lean_ctor_set(v_reuseFailAlloc_2185_, 7, v_messages_2165_);
lean_ctor_set(v_reuseFailAlloc_2185_, 8, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2185_, 9, v_snapshotTasks_2166_);
v___x_2182_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = lean_st_ref_put(v___y_2149_, v___x_2182_);
v___x_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2177_);
return v___x_2184_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2148_ = stack[0].m_obj;
lean_object* v___y_2149_ = stack[1].m_obj;
lean_object* v_res_2189_;
v_res_2189_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2148_, v___y_2149_);
stack->m_obj
 = v_res_2189_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2190_, v___y_2191_);
lean_dec(v___y_2191_);
return v_res_2193_;
}
}
lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object* v_t_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___x_2198_; lean_object* v_infoState_2199_; uint8_t v_enabled_2200_; 
v___x_2198_ = lean_st_ref_get(v___y_2196_);
v_infoState_2199_ = lean_ctor_get(v___x_2198_, 8);
lean_inc_ref(v_infoState_2199_);
lean_dec(v___x_2198_);
v_enabled_2200_ = lean_ctor_get_uint8(v_infoState_2199_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2199_);
if (v_enabled_2200_ == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec_ref(v_t_2194_);
v___x_2201_ = lean_box(0);
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2203_ = lean_unsigned_to_nat(32u);
v___x_2204_ = lean_mk_empty_array_with_capacity(v___x_2203_);
lean_dec_ref(v___x_2204_);
v___x_2205_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2206_, 0, v_t_2194_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
v___x_2207_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v___x_2206_, v___y_2196_);
return v___x_2207_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2194_ = stack[0].m_obj;
lean_object* v___y_2195_ = stack[1].m_obj;
lean_object* v___y_2196_ = stack[2].m_obj;
lean_object* v_res_2208_;
v_res_2208_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_2194_, v___y_2195_, v___y_2196_);
stack->m_obj
 = v_res_2208_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object* v_t_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_2209_, v___y_2210_, v___y_2211_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
return v_res_2213_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2214_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
return v___x_2215_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2216_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2217_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2218_ = lean_unsigned_to_nat(0u);
v___x_2219_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
lean_ctor_set(v___x_2219_, 2, v___x_2218_);
lean_ctor_set(v___x_2219_, 3, v___x_2218_);
lean_ctor_set(v___x_2219_, 4, v___x_2217_);
lean_ctor_set(v___x_2219_, 5, v___x_2217_);
lean_ctor_set(v___x_2219_, 6, v___x_2217_);
lean_ctor_set(v___x_2219_, 7, v___x_2217_);
lean_ctor_set(v___x_2219_, 8, v___x_2217_);
lean_ctor_set(v___x_2219_, 9, v___x_2217_);
lean_ctor_set(v___x_2219_, 10, v___x_2217_);
lean_ctor_set(v___x_2219_, 11, v___x_2216_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2220_ = lean_box(1);
v___x_2221_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_2222_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v___x_2221_);
lean_ctor_set(v___x_2223_, 2, v___x_2220_);
return v___x_2223_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3));
v___x_2226_ = l_Lean_stringToMessageData(v___x_2225_);
return v___x_2226_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5));
v___x_2229_ = l_Lean_stringToMessageData(v___x_2228_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7));
v___x_2232_ = l_Lean_stringToMessageData(v___x_2231_);
return v___x_2232_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9));
v___x_2235_ = l_Lean_stringToMessageData(v___x_2234_);
return v___x_2235_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11));
v___x_2238_ = l_Lean_stringToMessageData(v___x_2237_);
return v___x_2238_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13));
v___x_2241_ = l_Lean_stringToMessageData(v___x_2240_);
return v___x_2241_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15));
v___x_2244_ = l_Lean_stringToMessageData(v___x_2243_);
return v___x_2244_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18(void){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17));
v___x_2247_ = l_Lean_stringToMessageData(v___x_2246_);
return v___x_2247_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__20(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19));
v___x_2250_ = l_Lean_stringToMessageData(v___x_2249_);
return v___x_2250_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__22(void){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__21));
v___x_2253_ = l_Lean_stringToMessageData(v___x_2252_);
return v___x_2253_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__24(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__23));
v___x_2256_ = l_Lean_stringToMessageData(v___x_2255_);
return v___x_2256_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_2257_, lean_object* v_declHint_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v_env_2263_; uint8_t v___x_2264_; 
v___x_2261_ = lean_box(0);
v___x_2262_ = lean_st_ref_get(v___y_2259_);
v_env_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc_ref(v_env_2263_);
lean_dec(v___x_2262_);
v___x_2264_ = l_Lean_Name_isAnonymous(v_declHint_2258_);
if (v___x_2264_ == 0)
{
uint8_t v_isExporting_2265_; 
v_isExporting_2265_ = lean_ctor_get_uint8(v_env_2263_, sizeof(void*)*13);
if (v_isExporting_2265_ == 0)
{
lean_object* v___x_2266_; 
lean_dec_ref(v_env_2263_);
lean_dec(v_declHint_2258_);
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v_msg_2257_);
return v___x_2266_;
}
else
{
lean_object* v___x_2267_; uint8_t v___x_2268_; 
lean_inc_ref(v_env_2263_);
v___x_2267_ = l_Lean_Environment_setExporting(v_env_2263_, v___x_2264_);
lean_inc(v_declHint_2258_);
lean_inc_ref(v___x_2267_);
v___x_2268_ = l_Lean_Environment_contains(v___x_2267_, v_declHint_2258_, v_isExporting_2265_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; 
lean_dec_ref(v___x_2267_);
lean_dec_ref(v_env_2263_);
lean_dec(v_declHint_2258_);
v___x_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2269_, 0, v_msg_2257_);
return v___x_2269_;
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v_c_2275_; lean_object* v___x_2276_; 
v___x_2270_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2271_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_2272_ = l_Lean_Options_empty;
v___x_2273_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2267_);
lean_ctor_set(v___x_2273_, 1, v___x_2270_);
lean_ctor_set(v___x_2273_, 2, v___x_2271_);
lean_ctor_set(v___x_2273_, 3, v___x_2272_);
lean_inc(v_declHint_2258_);
v___x_2274_ = l_Lean_MessageData_ofConstName(v_declHint_2258_, v___x_2264_);
v_c_2275_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2275_, 0, v___x_2273_);
lean_ctor_set(v_c_2275_, 1, v___x_2274_);
v___x_2276_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2263_, v_declHint_2258_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
lean_dec_ref(v_env_2263_);
lean_dec(v_declHint_2258_);
v___x_2277_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v_c_2275_);
v___x_2279_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6);
v___x_2280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2278_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
v___x_2281_ = l_Lean_MessageData_note(v___x_2280_);
v___x_2282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2282_, 0, v_msg_2257_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
return v___x_2283_;
}
else
{
lean_object* v_val_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2340_; 
v_val_2284_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2286_ = v___x_2276_;
v_isShared_2287_ = v_isSharedCheck_2340_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_val_2284_);
lean_dec(v___x_2276_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2340_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2288_; lean_object* v_modules_2289_; lean_object* v_moduleNames_2290_; lean_object* v_mod_2291_; uint8_t v___y_2293_; uint8_t v___x_2323_; 
v___x_2288_ = l_Lean_Environment_header(v_env_2263_);
lean_dec_ref(v_env_2263_);
v_modules_2289_ = lean_ctor_get(v___x_2288_, 3);
lean_inc_ref(v_modules_2289_);
v_moduleNames_2290_ = lean_ctor_get(v___x_2288_, 4);
lean_inc_ref(v_moduleNames_2290_);
lean_dec_ref(v___x_2288_);
v_mod_2291_ = lean_array_get(v___x_2261_, v_moduleNames_2290_, v_val_2284_);
lean_dec_ref(v_moduleNames_2290_);
v___x_2323_ = l_Lean_isPrivateName(v_declHint_2258_);
lean_dec(v_declHint_2258_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; uint8_t v___x_2325_; 
v___x_2324_ = lean_array_get_size(v_modules_2289_);
v___x_2325_ = lean_nat_dec_lt(v_val_2284_, v___x_2324_);
if (v___x_2325_ == 0)
{
lean_dec_ref(v_modules_2289_);
lean_dec(v_val_2284_);
v___y_2293_ = v___x_2323_;
goto v___jp_2292_;
}
else
{
lean_object* v___x_2326_; lean_object* v_toImport_2327_; uint8_t v_isExported_2328_; 
v___x_2326_ = lean_array_fget(v_modules_2289_, v_val_2284_);
lean_dec(v_val_2284_);
lean_dec_ref(v_modules_2289_);
v_toImport_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc_ref(v_toImport_2327_);
lean_dec(v___x_2326_);
v_isExported_2328_ = lean_ctor_get_uint8(v_toImport_2327_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2327_);
v___y_2293_ = v_isExported_2328_;
goto v___jp_2292_;
}
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
lean_dec_ref(v_modules_2289_);
lean_del_object(v___x_2286_);
lean_dec(v_val_2284_);
v___x_2329_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2329_);
lean_ctor_set(v___x_2330_, 1, v_c_2275_);
v___x_2331_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__22);
v___x_2332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
v___x_2333_ = l_Lean_MessageData_ofName(v_mod_2291_);
v___x_2334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2332_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__24);
v___x_2336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = l_Lean_MessageData_note(v___x_2336_);
v___x_2338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2338_, 0, v_msg_2257_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
v___x_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
return v___x_2339_;
}
v___jp_2292_:
{
if (v___y_2293_ == 0)
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2305_; 
v___x_2294_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8);
v___x_2295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
lean_ctor_set(v___x_2295_, 1, v_c_2275_);
v___x_2296_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10);
v___x_2297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2295_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = l_Lean_MessageData_ofName(v_mod_2291_);
v___x_2299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2297_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v___x_2300_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12);
v___x_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2299_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = l_Lean_MessageData_note(v___x_2301_);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v_msg_2257_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set_tag(v___x_2286_, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2303_);
v___x_2305_ = v___x_2286_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
else
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2307_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14);
v___x_2308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
lean_ctor_set(v___x_2308_, 1, v_c_2275_);
v___x_2309_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16);
v___x_2310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2308_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
v___x_2311_ = l_Lean_MessageData_ofName(v_mod_2291_);
lean_inc_ref(v___x_2311_);
v___x_2312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2310_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
v___x_2313_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18);
v___x_2314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
lean_ctor_set(v___x_2315_, 1, v___x_2311_);
v___x_2316_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__20);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = l_Lean_MessageData_note(v___x_2317_);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v_msg_2257_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set_tag(v___x_2286_, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2319_);
v___x_2321_ = v___x_2286_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
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
lean_object* v___x_2341_; 
lean_dec_ref(v_env_2263_);
lean_dec(v_declHint_2258_);
v___x_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2341_, 0, v_msg_2257_);
return v___x_2341_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2257_ = stack[0].m_obj;
lean_object* v_declHint_2258_ = stack[1].m_obj;
lean_object* v___y_2259_ = stack[2].m_obj;
lean_object* v_res_2342_;
v_res_2342_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2257_, v_declHint_2258_, v___y_2259_);
stack->m_obj
 = v_res_2342_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_2343_, lean_object* v_declHint_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2343_, v_declHint_2344_, v___y_2345_);
lean_dec(v___y_2345_);
return v_res_2347_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_2348_, lean_object* v_declHint_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v___x_2353_; lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2363_; 
v___x_2353_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2348_, v_declHint_2349_, v___y_2351_);
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2356_ = v___x_2353_;
v_isShared_2357_ = v_isSharedCheck_2363_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2363_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2361_; 
v___x_2358_ = l_Lean_unknownIdentifierMessageTag;
v___x_2359_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
lean_ctor_set(v___x_2359_, 1, v_a_2354_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v___x_2359_);
v___x_2361_ = v___x_2356_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2348_ = stack[0].m_obj;
lean_object* v_declHint_2349_ = stack[1].m_obj;
lean_object* v___y_2350_ = stack[2].m_obj;
lean_object* v___y_2351_ = stack[3].m_obj;
lean_object* v_res_2364_;
v_res_2364_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2348_, v_declHint_2349_, v___y_2350_, v___y_2351_);
stack->m_obj
 = v_res_2364_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_2365_, lean_object* v_declHint_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2365_, v_declHint_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
return v_res_2370_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object* v_msgData_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v___x_2375_; lean_object* v_toCold_2376_; lean_object* v_env_2377_; lean_object* v_options_2378_; uint8_t v___x_2379_; lean_object* v_env_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2375_ = lean_st_ref_get(v___y_2373_);
v_toCold_2376_ = lean_ctor_get(v___y_2372_, 0);
v_env_2377_ = lean_ctor_get(v___x_2375_, 0);
lean_inc_ref(v_env_2377_);
lean_dec(v___x_2375_);
v_options_2378_ = lean_ctor_get(v_toCold_2376_, 2);
v___x_2379_ = 0;
v_env_2380_ = l_Lean_Environment_setRecordingDeps(v_env_2377_, v___x_2379_);
v___x_2381_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2382_ = lean_unsigned_to_nat(32u);
v___x_2383_ = lean_mk_empty_array_with_capacity(v___x_2382_);
lean_dec_ref(v___x_2383_);
v___x_2384_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
lean_inc_ref(v_options_2378_);
v___x_2385_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2385_, 0, v_env_2380_);
lean_ctor_set(v___x_2385_, 1, v___x_2381_);
lean_ctor_set(v___x_2385_, 2, v___x_2384_);
lean_ctor_set(v___x_2385_, 3, v_options_2378_);
v___x_2386_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
lean_ctor_set(v___x_2386_, 1, v_msgData_2371_);
v___x_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
return v___x_2387_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2371_ = stack[0].m_obj;
lean_object* v___y_2372_ = stack[1].m_obj;
lean_object* v___y_2373_ = stack[2].m_obj;
lean_object* v_res_2388_;
v_res_2388_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_2371_, v___y_2372_, v___y_2373_);
stack->m_obj
 = v_res_2388_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object* v_msgData_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_2389_, v___y_2390_, v___y_2391_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
return v_res_2393_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v_ref_2398_; lean_object* v___x_2399_; lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2408_; 
v_ref_2398_ = lean_ctor_get(v___y_2395_, 2);
v___x_2399_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_2394_, v___y_2395_, v___y_2396_);
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2402_ = v___x_2399_;
v_isShared_2403_ = v_isSharedCheck_2408_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2399_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2408_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v___x_2406_; 
lean_inc(v_ref_2398_);
v___x_2404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2404_, 0, v_ref_2398_);
lean_ctor_set(v___x_2404_, 1, v_a_2400_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set_tag(v___x_2402_, 1);
lean_ctor_set(v___x_2402_, 0, v___x_2404_);
v___x_2406_ = v___x_2402_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2394_ = stack[0].m_obj;
lean_object* v___y_2395_ = stack[1].m_obj;
lean_object* v___y_2396_ = stack[2].m_obj;
lean_object* v_res_2409_;
v_res_2409_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2394_, v___y_2395_, v___y_2396_);
stack->m_obj
 = v_res_2409_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
return v_res_2414_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_2415_, lean_object* v_msg_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v_toCold_2420_; lean_object* v_currRecDepth_2421_; lean_object* v_ref_2422_; uint16_t v_optionFlags_2423_; uint8_t v_suppressElabErrors_2424_; uint8_t v_isRecordingDeps_2425_; lean_object* v_ref_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v_toCold_2420_ = lean_ctor_get(v___y_2417_, 0);
v_currRecDepth_2421_ = lean_ctor_get(v___y_2417_, 1);
v_ref_2422_ = lean_ctor_get(v___y_2417_, 2);
v_optionFlags_2423_ = lean_ctor_get_uint16(v___y_2417_, sizeof(void*)*3);
v_suppressElabErrors_2424_ = lean_ctor_get_uint8(v___y_2417_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2425_ = lean_ctor_get_uint8(v___y_2417_, sizeof(void*)*3 + 3);
v_ref_2426_ = l_Lean_replaceRef(v_ref_2415_, v_ref_2422_);
lean_inc(v_currRecDepth_2421_);
lean_inc_ref(v_toCold_2420_);
v___x_2427_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2427_, 0, v_toCold_2420_);
lean_ctor_set(v___x_2427_, 1, v_currRecDepth_2421_);
lean_ctor_set(v___x_2427_, 2, v_ref_2426_);
lean_ctor_set_uint16(v___x_2427_, sizeof(void*)*3, v_optionFlags_2423_);
lean_ctor_set_uint8(v___x_2427_, sizeof(void*)*3 + 2, v_suppressElabErrors_2424_);
lean_ctor_set_uint8(v___x_2427_, sizeof(void*)*3 + 3, v_isRecordingDeps_2425_);
v___x_2428_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2416_, v___x_2427_, v___y_2418_);
lean_dec_ref_known(v___x_2427_, 3);
return v___x_2428_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2415_ = stack[0].m_obj;
lean_object* v_msg_2416_ = stack[1].m_obj;
lean_object* v___y_2417_ = stack[2].m_obj;
lean_object* v___y_2418_ = stack[3].m_obj;
lean_object* v_res_2429_;
v_res_2429_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2415_, v_msg_2416_, v___y_2417_, v___y_2418_);
stack->m_obj
 = v_res_2429_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_2430_, lean_object* v_msg_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2430_, v_msg_2431_, v___y_2432_, v___y_2433_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v_ref_2430_);
return v_res_2435_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_2436_, lean_object* v_msg_2437_, lean_object* v_declHint_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v___x_2442_; lean_object* v_a_2443_; lean_object* v___x_2444_; 
v___x_2442_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2437_, v_declHint_2438_, v___y_2439_, v___y_2440_);
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2443_);
lean_dec_ref(v___x_2442_);
v___x_2444_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2436_, v_a_2443_, v___y_2439_, v___y_2440_);
return v___x_2444_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2436_ = stack[0].m_obj;
lean_object* v_msg_2437_ = stack[1].m_obj;
lean_object* v_declHint_2438_ = stack[2].m_obj;
lean_object* v___y_2439_ = stack[3].m_obj;
lean_object* v___y_2440_ = stack[4].m_obj;
lean_object* v_res_2445_;
v_res_2445_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2436_, v_msg_2437_, v_declHint_2438_, v___y_2439_, v___y_2440_);
stack->m_obj
 = v_res_2445_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2446_, lean_object* v_msg_2447_, lean_object* v_declHint_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2446_, v_msg_2447_, v_declHint_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v_ref_2446_);
return v_res_2452_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_2455_ = l_Lean_stringToMessageData(v___x_2454_);
return v___x_2455_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2));
v___x_2458_ = l_Lean_stringToMessageData(v___x_2457_);
return v___x_2458_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_2459_, lean_object* v_constName_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v___x_2464_; uint8_t v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2464_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_2465_ = 0;
lean_inc(v_constName_2460_);
v___x_2466_ = l_Lean_MessageData_ofConstName(v_constName_2460_, v___x_2465_);
v___x_2467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2464_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_2469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2459_, v___x_2469_, v_constName_2460_, v___y_2461_, v___y_2462_);
return v___x_2470_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2459_ = stack[0].m_obj;
lean_object* v_constName_2460_ = stack[1].m_obj;
lean_object* v___y_2461_ = stack[2].m_obj;
lean_object* v___y_2462_ = stack[3].m_obj;
lean_object* v_res_2471_;
v_res_2471_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2459_, v_constName_2460_, v___y_2461_, v___y_2462_);
stack->m_obj
 = v_res_2471_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2472_, lean_object* v_constName_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2472_, v_constName_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v_ref_2472_);
return v_res_2477_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_ref_2482_; lean_object* v___x_2483_; 
v_ref_2482_ = lean_ctor_get(v___y_2479_, 2);
v___x_2483_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2482_, v_constName_2478_, v___y_2479_, v___y_2480_);
return v___x_2483_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2478_ = stack[0].m_obj;
lean_object* v___y_2479_ = stack[1].m_obj;
lean_object* v___y_2480_ = stack[2].m_obj;
lean_object* v_res_2484_;
v_res_2484_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2478_, v___y_2479_, v___y_2480_);
stack->m_obj
 = v_res_2484_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2485_, v___y_2486_, v___y_2487_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
return v_res_2489_;
}
}
lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object* v_constName_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v___x_2494_; lean_object* v_env_2495_; uint8_t v___x_2496_; lean_object* v___x_2497_; 
v___x_2494_ = lean_st_ref_get(v___y_2492_);
v_env_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc_ref(v_env_2495_);
lean_dec(v___x_2494_);
v___x_2496_ = 0;
lean_inc(v_constName_2490_);
v___x_2497_ = l_Lean_Environment_findConstVal_x3f(v_env_2495_, v_constName_2490_, v___x_2496_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2490_, v___y_2491_, v___y_2492_);
return v___x_2498_;
}
else
{
lean_object* v_val_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_dec(v_constName_2490_);
v_val_2499_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2497_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_val_2499_);
lean_dec(v___x_2497_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
lean_ctor_set_tag(v___x_2501_, 0);
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_val_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2490_ = stack[0].m_obj;
lean_object* v___y_2491_ = stack[1].m_obj;
lean_object* v___y_2492_ = stack[2].m_obj;
lean_object* v_res_2507_;
v_res_2507_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2490_, v___y_2491_, v___y_2492_);
stack->m_obj
 = v_res_2507_;
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2508_, v___y_2509_, v___y_2510_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object* v_a_2513_, lean_object* v_a_2514_){
_start:
{
if (lean_obj_tag(v_a_2513_) == 0)
{
lean_object* v___x_2515_; 
v___x_2515_ = l_List_reverse___redArg(v_a_2514_);
return v___x_2515_;
}
else
{
lean_object* v_head_2516_; lean_object* v_tail_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2526_; 
v_head_2516_ = lean_ctor_get(v_a_2513_, 0);
v_tail_2517_ = lean_ctor_get(v_a_2513_, 1);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_a_2513_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2519_ = v_a_2513_;
v_isShared_2520_ = v_isSharedCheck_2526_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_tail_2517_);
lean_inc(v_head_2516_);
lean_dec(v_a_2513_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2526_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2521_ = l_Lean_mkLevelParam(v_head_2516_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 1, v_a_2514_);
lean_ctor_set(v___x_2519_, 0, v___x_2521_);
v___x_2523_ = v___x_2519_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2521_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_a_2514_);
v___x_2523_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
v_a_2513_ = v_tail_2517_;
v_a_2514_ = v___x_2523_;
goto _start;
}
}
}
}
}
lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object* v_constName_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v___x_2531_; 
lean_inc(v_constName_2527_);
v___x_2531_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2527_, v___y_2528_, v___y_2529_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2543_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2543_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2543_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v_levelParams_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2541_; 
v_levelParams_2536_ = lean_ctor_get(v_a_2532_, 1);
lean_inc(v_levelParams_2536_);
lean_dec(v_a_2532_);
v___x_2537_ = lean_box(0);
v___x_2538_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_2536_, v___x_2537_);
v___x_2539_ = l_Lean_mkConst(v_constName_2527_, v___x_2538_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v___x_2539_);
v___x_2541_ = v___x_2534_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2539_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec(v_constName_2527_);
v_a_2544_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2531_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2531_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2527_ = stack[0].m_obj;
lean_object* v___y_2528_ = stack[1].m_obj;
lean_object* v___y_2529_ = stack[2].m_obj;
lean_object* v_res_2552_;
v_res_2552_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_2527_, v___y_2528_, v___y_2529_);
stack->m_obj
 = v_res_2552_;
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object* v_constName_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_2553_, v___y_2554_, v___y_2555_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
return v_res_2557_;
}
}
lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object* v_stx_2558_, lean_object* v_n_2559_, lean_object* v_expectedType_x3f_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_2559_, v___y_2561_, v___y_2562_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_a_2565_);
lean_dec_ref_known(v___x_2564_, 1);
v___x_2566_ = lean_box(0);
v___x_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
lean_ctor_set(v___x_2567_, 1, v_stx_2558_);
v___x_2568_ = l_Lean_LocalContext_empty;
v___x_2569_ = 0;
v___x_2570_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2570_, 0, v___x_2567_);
lean_ctor_set(v___x_2570_, 1, v___x_2568_);
lean_ctor_set(v___x_2570_, 2, v_expectedType_x3f_2560_);
lean_ctor_set(v___x_2570_, 3, v_a_2565_);
lean_ctor_set_uint8(v___x_2570_, sizeof(void*)*4, v___x_2569_);
lean_ctor_set_uint8(v___x_2570_, sizeof(void*)*4 + 1, v___x_2569_);
v___x_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
v___x_2572_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_2571_, v___y_2561_, v___y_2562_);
return v___x_2572_;
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
lean_dec(v_expectedType_x3f_2560_);
lean_dec(v_stx_2558_);
v_a_2573_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2564_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2564_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_2558_ = stack[0].m_obj;
lean_object* v_n_2559_ = stack[1].m_obj;
lean_object* v_expectedType_x3f_2560_ = stack[2].m_obj;
lean_object* v___y_2561_ = stack[3].m_obj;
lean_object* v___y_2562_ = stack[4].m_obj;
lean_object* v_res_2581_;
v_res_2581_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_2558_, v_n_2559_, v_expectedType_x3f_2560_, v___y_2561_, v___y_2562_);
stack->m_obj
 = v_res_2581_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object* v_stx_2582_, lean_object* v_n_2583_, lean_object* v_expectedType_x3f_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_2582_, v_n_2583_, v_expectedType_x3f_2584_, v___y_2585_, v___y_2586_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
return v_res_2588_;
}
}
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object* v_id_2589_, lean_object* v_expectedType_x3f_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v___x_2594_; 
lean_inc(v_id_2589_);
v___x_2594_ = l_Lean_realizeGlobalConstNoOverload(v_id_2589_, v_a_2591_, v_a_2592_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2622_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2597_ = v___x_2594_;
v_isShared_2598_ = v_isSharedCheck_2622_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2594_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2622_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; lean_object* v_infoState_2600_; uint8_t v_enabled_2601_; 
v___x_2599_ = lean_st_ref_get(v_a_2592_);
v_infoState_2600_ = lean_ctor_get(v___x_2599_, 8);
lean_inc_ref(v_infoState_2600_);
lean_dec(v___x_2599_);
v_enabled_2601_ = lean_ctor_get_uint8(v_infoState_2600_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2600_);
if (v_enabled_2601_ == 0)
{
lean_object* v___x_2603_; 
lean_dec(v_expectedType_x3f_2590_);
lean_dec(v_id_2589_);
if (v_isShared_2598_ == 0)
{
v___x_2603_ = v___x_2597_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2595_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
else
{
lean_object* v___x_2605_; 
lean_del_object(v___x_2597_);
lean_inc(v_a_2595_);
v___x_2605_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2589_, v_a_2595_, v_expectedType_x3f_2590_, v_a_2591_, v_a_2592_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2612_ == 0)
{
lean_object* v_unused_2613_; 
v_unused_2613_ = lean_ctor_get(v___x_2605_, 0);
lean_dec(v_unused_2613_);
v___x_2607_ = v___x_2605_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_dec(v___x_2605_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v_a_2595_);
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2595_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec(v_a_2595_);
v_a_2614_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2605_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2605_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2590_);
lean_dec(v_id_2589_);
return v___x_2594_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_2589_ = stack[0].m_obj;
lean_object* v_expectedType_x3f_2590_ = stack[1].m_obj;
lean_object* v_a_2591_ = stack[2].m_obj;
lean_object* v_a_2592_ = stack[3].m_obj;
lean_object* v_res_2623_;
v_res_2623_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_2589_, v_expectedType_x3f_2590_, v_a_2591_, v_a_2592_);
stack->m_obj
 = v_res_2623_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object* v_id_2624_, lean_object* v_expectedType_x3f_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_2624_, v_expectedType_x3f_2625_, v_a_2626_, v_a_2627_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
return v_res_2629_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object* v_t_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2630_, v___y_2632_);
return v___x_2634_;
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2630_ = stack[0].m_obj;
lean_object* v___y_2631_ = stack[1].m_obj;
lean_object* v___y_2632_ = stack[2].m_obj;
lean_object* v_res_2635_;
v_res_2635_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_2630_, v___y_2631_, v___y_2632_);
stack->m_obj
 = v_res_2635_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_2636_, v___y_2637_, v___y_2638_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
return v_res_2640_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2641_, lean_object* v_constName_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2642_, v___y_2643_, v___y_2644_);
return v___x_2646_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2642_ = stack[1].m_obj;
lean_object* v___y_2643_ = stack[2].m_obj;
lean_object* v___y_2644_ = stack[3].m_obj;
lean_object* v_res_2647_;
v_res_2647_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_box(0), v_constName_2642_, v___y_2643_, v___y_2644_);
stack->m_obj
 = v_res_2647_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2648_, lean_object* v_constName_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2648_, v_constName_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
return v_res_2653_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2654_, lean_object* v_ref_2655_, lean_object* v_constName_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2655_, v_constName_2656_, v___y_2657_, v___y_2658_);
return v___x_2660_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2655_ = stack[1].m_obj;
lean_object* v_constName_2656_ = stack[2].m_obj;
lean_object* v___y_2657_ = stack[3].m_obj;
lean_object* v___y_2658_ = stack[4].m_obj;
lean_object* v_res_2661_;
v_res_2661_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_box(0), v_ref_2655_, v_constName_2656_, v___y_2657_, v___y_2658_);
stack->m_obj
 = v_res_2661_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2662_, lean_object* v_ref_2663_, lean_object* v_constName_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_2662_, v_ref_2663_, v_constName_2664_, v___y_2665_, v___y_2666_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v_ref_2663_);
return v_res_2668_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2669_, lean_object* v_ref_2670_, lean_object* v_msg_2671_, lean_object* v_declHint_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2670_, v_msg_2671_, v_declHint_2672_, v___y_2673_, v___y_2674_);
return v___x_2676_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2670_ = stack[1].m_obj;
lean_object* v_msg_2671_ = stack[2].m_obj;
lean_object* v_declHint_2672_ = stack[3].m_obj;
lean_object* v___y_2673_ = stack[4].m_obj;
lean_object* v___y_2674_ = stack[5].m_obj;
lean_object* v_res_2677_;
v_res_2677_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_box(0), v_ref_2670_, v_msg_2671_, v_declHint_2672_, v___y_2673_, v___y_2674_);
stack->m_obj
 = v_res_2677_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2678_, lean_object* v_ref_2679_, lean_object* v_msg_2680_, lean_object* v_declHint_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_2678_, v_ref_2679_, v_msg_2680_, v_declHint_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v_ref_2679_);
return v_res_2685_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_2686_, lean_object* v_declHint_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2686_, v_declHint_2687_, v___y_2689_);
return v___x_2691_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2686_ = stack[0].m_obj;
lean_object* v_declHint_2687_ = stack[1].m_obj;
lean_object* v___y_2688_ = stack[2].m_obj;
lean_object* v___y_2689_ = stack[3].m_obj;
lean_object* v_res_2692_;
v_res_2692_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2686_, v_declHint_2687_, v___y_2688_, v___y_2689_);
stack->m_obj
 = v_res_2692_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2693_, lean_object* v_declHint_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2693_, v_declHint_2694_, v___y_2695_, v___y_2696_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
return v_res_2698_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_2699_, lean_object* v_ref_2700_, lean_object* v_msg_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2700_, v_msg_2701_, v___y_2702_, v___y_2703_);
return v___x_2705_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2700_ = stack[1].m_obj;
lean_object* v_msg_2701_ = stack[2].m_obj;
lean_object* v___y_2702_ = stack[3].m_obj;
lean_object* v___y_2703_ = stack[4].m_obj;
lean_object* v_res_2706_;
v_res_2706_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_box(0), v_ref_2700_, v_msg_2701_, v___y_2702_, v___y_2703_);
stack->m_obj
 = v_res_2706_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2707_, lean_object* v_ref_2708_, lean_object* v_msg_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_2707_, v_ref_2708_, v_msg_2709_, v___y_2710_, v___y_2711_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v_ref_2708_);
return v_res_2713_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_2714_, lean_object* v_msg_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2715_, v___y_2716_, v___y_2717_);
return v___x_2719_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2715_ = stack[1].m_obj;
lean_object* v___y_2716_ = stack[2].m_obj;
lean_object* v___y_2717_ = stack[3].m_obj;
lean_object* v_res_2720_;
v_res_2720_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_box(0), v_msg_2715_, v___y_2716_, v___y_2717_);
stack->m_obj
 = v_res_2720_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_2721_, lean_object* v_msg_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_2721_, v_msg_2722_, v___y_2723_, v___y_2724_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
return v_res_2726_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object* v_id_2727_, lean_object* v_expectedType_x3f_2728_, lean_object* v_as_x27_2729_, lean_object* v_b_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
if (lean_obj_tag(v_as_x27_2729_) == 0)
{
lean_object* v___x_2734_; 
lean_dec(v_expectedType_x3f_2728_);
lean_dec(v_id_2727_);
v___x_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2734_, 0, v_b_2730_);
return v___x_2734_;
}
else
{
lean_object* v_head_2735_; lean_object* v_tail_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v_head_2735_ = lean_ctor_get(v_as_x27_2729_, 0);
v_tail_2736_ = lean_ctor_get(v_as_x27_2729_, 1);
v___x_2737_ = lean_box(0);
lean_inc(v_expectedType_x3f_2728_);
lean_inc(v_head_2735_);
lean_inc(v_id_2727_);
v___x_2738_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2727_, v_head_2735_, v_expectedType_x3f_2728_, v___y_2731_, v___y_2732_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_dec_ref_known(v___x_2738_, 1);
v_as_x27_2729_ = v_tail_2736_;
v_b_2730_ = v___x_2737_;
goto _start;
}
else
{
lean_dec(v_expectedType_x3f_2728_);
lean_dec(v_id_2727_);
return v___x_2738_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_2727_ = stack[0].m_obj;
lean_object* v_expectedType_x3f_2728_ = stack[1].m_obj;
lean_object* v_as_x27_2729_ = stack[2].m_obj;
lean_object* v_b_2730_ = stack[3].m_obj;
lean_object* v___y_2731_ = stack[4].m_obj;
lean_object* v___y_2732_ = stack[5].m_obj;
lean_object* v_res_2740_;
v_res_2740_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2727_, v_expectedType_x3f_2728_, v_as_x27_2729_, v_b_2730_, v___y_2731_, v___y_2732_);
stack->m_obj
 = v_res_2740_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object* v_id_2741_, lean_object* v_expectedType_x3f_2742_, lean_object* v_as_x27_2743_, lean_object* v_b_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2741_, v_expectedType_x3f_2742_, v_as_x27_2743_, v_b_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v_as_x27_2743_);
return v_res_2748_;
}
}
lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object* v_id_2749_, lean_object* v_expectedType_x3f_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v___x_2754_; 
lean_inc(v_id_2749_);
v___x_2754_ = l_Lean_realizeGlobalConst(v_id_2749_, v_a_2751_, v_a_2752_);
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
lean_dec(v_expectedType_x3f_2750_);
lean_dec(v_id_2749_);
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
v___x_2766_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2749_, v_expectedType_x3f_2750_, v_a_2755_, v___x_2765_, v_a_2751_, v_a_2752_);
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
lean_dec(v_expectedType_x3f_2750_);
lean_dec(v_id_2749_);
return v___x_2754_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_realizeGlobalConstWithInfos_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_2749_ = stack[0].m_obj;
lean_object* v_expectedType_x3f_2750_ = stack[1].m_obj;
lean_object* v_a_2751_ = stack[2].m_obj;
lean_object* v_a_2752_ = stack[3].m_obj;
lean_object* v_res_2784_;
v_res_2784_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_2749_, v_expectedType_x3f_2750_, v_a_2751_, v_a_2752_);
stack->m_obj
 = v_res_2784_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object* v_id_2785_, lean_object* v_expectedType_x3f_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_2785_, v_expectedType_x3f_2786_, v_a_2787_, v_a_2788_);
lean_dec(v_a_2788_);
lean_dec_ref(v_a_2787_);
return v_res_2790_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object* v_id_2791_, lean_object* v_expectedType_x3f_2792_, lean_object* v_as_2793_, lean_object* v_as_x27_2794_, lean_object* v_b_2795_, lean_object* v_a_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2791_, v_expectedType_x3f_2792_, v_as_x27_2794_, v_b_2795_, v___y_2797_, v___y_2798_);
return v___x_2800_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_2791_ = stack[0].m_obj;
lean_object* v_expectedType_x3f_2792_ = stack[1].m_obj;
lean_object* v_as_2793_ = stack[2].m_obj;
lean_object* v_as_x27_2794_ = stack[3].m_obj;
lean_object* v_b_2795_ = stack[4].m_obj;
lean_object* v___y_2797_ = stack[6].m_obj;
lean_object* v___y_2798_ = stack[7].m_obj;
lean_object* v_res_2801_;
v_res_2801_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_2791_, v_expectedType_x3f_2792_, v_as_2793_, v_as_x27_2794_, v_b_2795_, lean_box(0), v___y_2797_, v___y_2798_);
stack->m_obj
 = v_res_2801_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object* v_id_2802_, lean_object* v_expectedType_x3f_2803_, lean_object* v_as_2804_, lean_object* v_as_x27_2805_, lean_object* v_b_2806_, lean_object* v_a_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_2802_, v_expectedType_x3f_2803_, v_as_2804_, v_as_x27_2805_, v_b_2806_, v_a_2807_, v___y_2808_, v___y_2809_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v_as_x27_2805_);
lean_dec(v_as_2804_);
return v_res_2811_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object* v_ref_2812_, lean_object* v_as_x27_2813_, lean_object* v_b_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
if (lean_obj_tag(v_as_x27_2813_) == 0)
{
lean_object* v___x_2818_; 
lean_dec(v_ref_2812_);
v___x_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2818_, 0, v_b_2814_);
return v___x_2818_;
}
else
{
lean_object* v_head_2819_; lean_object* v_tail_2820_; lean_object* v_fst_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v_head_2819_ = lean_ctor_get(v_as_x27_2813_, 0);
v_tail_2820_ = lean_ctor_get(v_as_x27_2813_, 1);
v_fst_2821_ = lean_ctor_get(v_head_2819_, 0);
v___x_2822_ = lean_box(0);
v___x_2823_ = lean_box(0);
lean_inc(v_fst_2821_);
lean_inc(v_ref_2812_);
v___x_2824_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_2812_, v_fst_2821_, v___x_2823_, v___y_2815_, v___y_2816_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_dec_ref_known(v___x_2824_, 1);
v_as_x27_2813_ = v_tail_2820_;
v_b_2814_ = v___x_2822_;
goto _start;
}
else
{
lean_dec(v_ref_2812_);
return v___x_2824_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2812_ = stack[0].m_obj;
lean_object* v_as_x27_2813_ = stack[1].m_obj;
lean_object* v_b_2814_ = stack[2].m_obj;
lean_object* v___y_2815_ = stack[3].m_obj;
lean_object* v___y_2816_ = stack[4].m_obj;
lean_object* v_res_2826_;
v_res_2826_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2812_, v_as_x27_2813_, v_b_2814_, v___y_2815_, v___y_2816_);
stack->m_obj
 = v_res_2826_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object* v_ref_2827_, lean_object* v_as_x27_2828_, lean_object* v_b_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2827_, v_as_x27_2828_, v_b_2829_, v___y_2830_, v___y_2831_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v_as_x27_2828_);
return v_res_2833_;
}
}
lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object* v_ref_2834_, lean_object* v_id_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_realizeGlobalName(v_id_2835_, v_a_2836_, v_a_2837_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2868_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2868_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2868_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2844_; lean_object* v_infoState_2845_; uint8_t v_enabled_2846_; 
v___x_2844_ = lean_st_ref_get(v_a_2837_);
v_infoState_2845_ = lean_ctor_get(v___x_2844_, 8);
lean_inc_ref(v_infoState_2845_);
lean_dec(v___x_2844_);
v_enabled_2846_ = lean_ctor_get_uint8(v_infoState_2845_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2845_);
if (v_enabled_2846_ == 0)
{
lean_object* v___x_2848_; 
lean_dec(v_ref_2834_);
if (v_isShared_2843_ == 0)
{
v___x_2848_ = v___x_2842_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2840_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
else
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
lean_del_object(v___x_2842_);
v___x_2850_ = lean_box(0);
v___x_2851_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2834_, v_a_2840_, v___x_2850_, v_a_2836_, v_a_2837_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2858_ == 0)
{
lean_object* v_unused_2859_; 
v_unused_2859_ = lean_ctor_get(v___x_2851_, 0);
lean_dec(v_unused_2859_);
v___x_2853_ = v___x_2851_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_dec(v___x_2851_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v_a_2840_);
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2840_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec(v_a_2840_);
v_a_2860_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2851_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2851_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
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
else
{
lean_dec(v_ref_2834_);
return v___x_2839_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_realizeGlobalNameWithInfos_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2834_ = stack[0].m_obj;
lean_object* v_id_2835_ = stack[1].m_obj;
lean_object* v_a_2836_ = stack[2].m_obj;
lean_object* v_a_2837_ = stack[3].m_obj;
lean_object* v_res_2869_;
v_res_2869_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_2834_, v_id_2835_, v_a_2836_, v_a_2837_);
stack->m_obj
 = v_res_2869_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object* v_ref_2870_, lean_object* v_id_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_2870_, v_id_2871_, v_a_2872_, v_a_2873_);
lean_dec(v_a_2873_);
lean_dec_ref(v_a_2872_);
return v_res_2875_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object* v_ref_2876_, lean_object* v_as_2877_, lean_object* v_as_x27_2878_, lean_object* v_b_2879_, lean_object* v_a_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2876_, v_as_x27_2878_, v_b_2879_, v___y_2881_, v___y_2882_);
return v___x_2884_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2876_ = stack[0].m_obj;
lean_object* v_as_2877_ = stack[1].m_obj;
lean_object* v_as_x27_2878_ = stack[2].m_obj;
lean_object* v_b_2879_ = stack[3].m_obj;
lean_object* v___y_2881_ = stack[5].m_obj;
lean_object* v___y_2882_ = stack[6].m_obj;
lean_object* v_res_2885_;
v_res_2885_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_2876_, v_as_2877_, v_as_x27_2878_, v_b_2879_, lean_box(0), v___y_2881_, v___y_2882_);
stack->m_obj
 = v_res_2885_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object* v_ref_2886_, lean_object* v_as_2887_, lean_object* v_as_x27_2888_, lean_object* v_b_2889_, lean_object* v_a_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_2886_, v_as_2887_, v_as_x27_2888_, v_b_2889_, v_a_2890_, v___y_2891_, v___y_2892_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v_as_x27_2888_);
lean_dec(v_as_2887_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object* v_self_2895_){
_start:
{
lean_object* v_fst_2896_; 
v_fst_2896_ = lean_ctor_get(v_self_2895_, 0);
lean_inc(v_fst_2896_);
return v_fst_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object* v_self_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_2897_);
lean_dec_ref(v_self_2897_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object* v_info_2899_, lean_object* v_treesSaved_2900_, lean_object* v_s_2901_){
_start:
{
if (lean_obj_tag(v_info_2899_) == 0)
{
uint8_t v_enabled_2902_; lean_object* v_assignment_2903_; lean_object* v_lazyAssignment_2904_; lean_object* v_trees_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2915_; 
v_enabled_2902_ = lean_ctor_get_uint8(v_s_2901_, sizeof(void*)*3);
v_assignment_2903_ = lean_ctor_get(v_s_2901_, 0);
v_lazyAssignment_2904_ = lean_ctor_get(v_s_2901_, 1);
v_trees_2905_ = lean_ctor_get(v_s_2901_, 2);
v_isSharedCheck_2915_ = !lean_is_exclusive(v_s_2901_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2907_ = v_s_2901_;
v_isShared_2908_ = v_isSharedCheck_2915_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_trees_2905_);
lean_inc(v_lazyAssignment_2904_);
lean_inc(v_assignment_2903_);
lean_dec(v_s_2901_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2915_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v_val_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2913_; 
v_val_2909_ = lean_ctor_get(v_info_2899_, 0);
lean_inc(v_val_2909_);
lean_dec_ref_known(v_info_2899_, 1);
v___x_2910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2910_, 0, v_val_2909_);
lean_ctor_set(v___x_2910_, 1, v_trees_2905_);
v___x_2911_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2900_, v___x_2910_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 2, v___x_2911_);
v___x_2913_ = v___x_2907_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_assignment_2903_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v_lazyAssignment_2904_);
lean_ctor_set(v_reuseFailAlloc_2914_, 2, v___x_2911_);
lean_ctor_set_uint8(v_reuseFailAlloc_2914_, sizeof(void*)*3, v_enabled_2902_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
else
{
uint8_t v_enabled_2916_; lean_object* v_assignment_2917_; lean_object* v_lazyAssignment_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2934_; 
v_enabled_2916_ = lean_ctor_get_uint8(v_s_2901_, sizeof(void*)*3);
v_assignment_2917_ = lean_ctor_get(v_s_2901_, 0);
v_lazyAssignment_2918_ = lean_ctor_get(v_s_2901_, 1);
v_isSharedCheck_2934_ = !lean_is_exclusive(v_s_2901_);
if (v_isSharedCheck_2934_ == 0)
{
lean_object* v_unused_2935_; 
v_unused_2935_ = lean_ctor_get(v_s_2901_, 2);
lean_dec(v_unused_2935_);
v___x_2920_ = v_s_2901_;
v_isShared_2921_ = v_isSharedCheck_2934_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_lazyAssignment_2918_);
lean_inc(v_assignment_2917_);
lean_dec(v_s_2901_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2934_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v_val_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2933_; 
v_val_2922_ = lean_ctor_get(v_info_2899_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_info_2899_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2924_ = v_info_2899_;
v_isShared_2925_ = v_isSharedCheck_2933_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_val_2922_);
lean_dec(v_info_2899_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2933_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
lean_ctor_set_tag(v___x_2924_, 2);
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_val_2922_);
v___x_2927_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
lean_object* v___x_2928_; lean_object* v___x_2930_; 
v___x_2928_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2900_, v___x_2927_);
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 2, v___x_2928_);
v___x_2930_ = v___x_2920_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_assignment_2917_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_lazyAssignment_2918_);
lean_ctor_set(v_reuseFailAlloc_2931_, 2, v___x_2928_);
lean_ctor_set_uint8(v_reuseFailAlloc_2931_, sizeof(void*)*3, v_enabled_2916_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object* v_treesSaved_2936_, lean_object* v_modifyInfoState_2937_, lean_object* v_info_2938_){
_start:
{
lean_object* v___f_2939_; lean_object* v___x_2940_; 
v___f_2939_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2939_, 0, v_info_2938_);
lean_closure_set(v___f_2939_, 1, v_treesSaved_2936_);
v___x_2940_ = lean_apply_1(v_modifyInfoState_2937_, v___f_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object* v___f_2941_, lean_object* v_info_2942_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = lean_apply_1(v___f_2941_, v_info_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object* v_toPure_2944_, lean_object* v_toBind_2945_, lean_object* v___f_2946_, lean_object* v_____do__lift_2947_){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2948_, 0, v_____do__lift_2947_);
v___x_2949_ = lean_apply_2(v_toPure_2944_, lean_box(0), v___x_2948_);
v___x_2950_ = lean_apply_4(v_toBind_2945_, lean_box(0), lean_box(0), v___x_2949_, v___f_2946_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object* v_toBind_2951_, lean_object* v_mkInfoOnError_2952_, lean_object* v___f_2953_, lean_object* v_mkInfo_2954_, lean_object* v___f_2955_, lean_object* v_a_x3f_2956_){
_start:
{
if (lean_obj_tag(v_a_x3f_2956_) == 0)
{
lean_object* v___x_2957_; 
lean_dec(v___f_2955_);
lean_dec(v_mkInfo_2954_);
v___x_2957_ = lean_apply_4(v_toBind_2951_, lean_box(0), lean_box(0), v_mkInfoOnError_2952_, v___f_2953_);
return v___x_2957_;
}
else
{
lean_object* v_val_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
lean_dec(v___f_2953_);
lean_dec(v_mkInfoOnError_2952_);
v_val_2958_ = lean_ctor_get(v_a_x3f_2956_, 0);
lean_inc(v_val_2958_);
lean_dec_ref_known(v_a_x3f_2956_, 1);
v___x_2959_ = lean_apply_1(v_mkInfo_2954_, v_val_2958_);
v___x_2960_ = lean_apply_4(v_toBind_2951_, lean_box(0), lean_box(0), v___x_2959_, v___f_2955_);
return v___x_2960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object* v_toFunctor_2961_, lean_object* v_modifyInfoState_2962_, lean_object* v_toPure_2963_, lean_object* v_toBind_2964_, lean_object* v_mkInfoOnError_2965_, lean_object* v_mkInfo_2966_, lean_object* v_inst_2967_, lean_object* v_x_2968_, lean_object* v___f_2969_, lean_object* v_treesSaved_2970_){
_start:
{
lean_object* v_map_2971_; lean_object* v___f_2972_; lean_object* v___f_2973_; lean_object* v___f_2974_; lean_object* v___f_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v_map_2971_ = lean_ctor_get(v_toFunctor_2961_, 0);
lean_inc(v_map_2971_);
lean_dec_ref(v_toFunctor_2961_);
v___f_2972_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2972_, 0, v_treesSaved_2970_);
lean_closure_set(v___f_2972_, 1, v_modifyInfoState_2962_);
v___f_2973_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2973_, 0, v___f_2972_);
lean_inc_ref(v___f_2973_);
lean_inc(v_toBind_2964_);
v___f_2974_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_2974_, 0, v_toPure_2963_);
lean_closure_set(v___f_2974_, 1, v_toBind_2964_);
lean_closure_set(v___f_2974_, 2, v___f_2973_);
v___f_2975_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__6), 6, 5);
lean_closure_set(v___f_2975_, 0, v_toBind_2964_);
lean_closure_set(v___f_2975_, 1, v_mkInfoOnError_2965_);
lean_closure_set(v___f_2975_, 2, v___f_2974_);
lean_closure_set(v___f_2975_, 3, v_mkInfo_2966_);
lean_closure_set(v___f_2975_, 4, v___f_2973_);
v___x_2976_ = lean_apply_4(v_inst_2967_, lean_box(0), lean_box(0), v_x_2968_, v___f_2975_);
v___x_2977_ = lean_apply_4(v_map_2971_, lean_box(0), lean_box(0), v___f_2969_, v___x_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object* v_x_2978_, lean_object* v_inst_2979_, lean_object* v_inst_2980_, lean_object* v_toBind_2981_, lean_object* v___f_2982_, lean_object* v_____do__lift_2983_){
_start:
{
uint8_t v_enabled_2984_; 
v_enabled_2984_ = lean_ctor_get_uint8(v_____do__lift_2983_, sizeof(void*)*3);
if (v_enabled_2984_ == 0)
{
lean_dec(v___f_2982_);
lean_dec(v_toBind_2981_);
lean_dec_ref(v_inst_2980_);
lean_dec_ref(v_inst_2979_);
lean_inc(v_x_2978_);
return v_x_2978_;
}
else
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2979_, v_inst_2980_);
v___x_2986_ = lean_apply_4(v_toBind_2981_, lean_box(0), lean_box(0), v___x_2985_, v___f_2982_);
return v___x_2986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object* v_x_2987_, lean_object* v_inst_2988_, lean_object* v_inst_2989_, lean_object* v_toBind_2990_, lean_object* v___f_2991_, lean_object* v_____do__lift_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__7(v_x_2987_, v_inst_2988_, v_inst_2989_, v_toBind_2990_, v___f_2991_, v_____do__lift_2992_);
lean_dec_ref(v_____do__lift_2992_);
lean_dec(v_x_2987_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object* v_inst_2995_, lean_object* v_inst_2996_, lean_object* v_inst_2997_, lean_object* v_x_2998_, lean_object* v_mkInfo_2999_, lean_object* v_mkInfoOnError_3000_){
_start:
{
lean_object* v_toApplicative_3001_; lean_object* v_toBind_3002_; lean_object* v_getInfoState_3003_; lean_object* v_modifyInfoState_3004_; lean_object* v_toFunctor_3005_; lean_object* v_toPure_3006_; lean_object* v___f_3007_; lean_object* v___f_3008_; lean_object* v___f_3009_; lean_object* v___x_3010_; 
v_toApplicative_3001_ = lean_ctor_get(v_inst_2995_, 0);
v_toBind_3002_ = lean_ctor_get(v_inst_2995_, 1);
lean_inc_n(v_toBind_3002_, 3);
v_getInfoState_3003_ = lean_ctor_get(v_inst_2996_, 0);
lean_inc(v_getInfoState_3003_);
v_modifyInfoState_3004_ = lean_ctor_get(v_inst_2996_, 1);
v_toFunctor_3005_ = lean_ctor_get(v_toApplicative_3001_, 0);
v_toPure_3006_ = lean_ctor_get(v_toApplicative_3001_, 1);
v___f_3007_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2998_);
lean_inc(v_toPure_3006_);
lean_inc(v_modifyInfoState_3004_);
lean_inc_ref(v_toFunctor_3005_);
v___f_3008_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__5), 10, 9);
lean_closure_set(v___f_3008_, 0, v_toFunctor_3005_);
lean_closure_set(v___f_3008_, 1, v_modifyInfoState_3004_);
lean_closure_set(v___f_3008_, 2, v_toPure_3006_);
lean_closure_set(v___f_3008_, 3, v_toBind_3002_);
lean_closure_set(v___f_3008_, 4, v_mkInfoOnError_3000_);
lean_closure_set(v___f_3008_, 5, v_mkInfo_2999_);
lean_closure_set(v___f_3008_, 6, v_inst_2997_);
lean_closure_set(v___f_3008_, 7, v_x_2998_);
lean_closure_set(v___f_3008_, 8, v___f_3007_);
v___f_3009_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3009_, 0, v_x_2998_);
lean_closure_set(v___f_3009_, 1, v_inst_2995_);
lean_closure_set(v___f_3009_, 2, v_inst_2996_);
lean_closure_set(v___f_3009_, 3, v_toBind_3002_);
lean_closure_set(v___f_3009_, 4, v___f_3008_);
v___x_3010_ = lean_apply_4(v_toBind_3002_, lean_box(0), lean_box(0), v_getInfoState_3003_, v___f_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* v_m_3011_, lean_object* v_inst_3012_, lean_object* v_inst_3013_, lean_object* v_00_u03b1_3014_, lean_object* v_inst_3015_, lean_object* v_x_3016_, lean_object* v_mkInfo_3017_, lean_object* v_mkInfoOnError_3018_){
_start:
{
lean_object* v___x_3019_; 
v___x_3019_ = l_Lean_Elab_withInfoContext_x27___redArg(v_inst_3012_, v_inst_3013_, v_inst_3015_, v_x_3016_, v_mkInfo_3017_, v_mkInfoOnError_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object* v_treesSaved_3020_, lean_object* v_tree_3021_, lean_object* v_s_3022_){
_start:
{
uint8_t v_enabled_3023_; lean_object* v_assignment_3024_; lean_object* v_lazyAssignment_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3033_; 
v_enabled_3023_ = lean_ctor_get_uint8(v_s_3022_, sizeof(void*)*3);
v_assignment_3024_ = lean_ctor_get(v_s_3022_, 0);
v_lazyAssignment_3025_ = lean_ctor_get(v_s_3022_, 1);
v_isSharedCheck_3033_ = !lean_is_exclusive(v_s_3022_);
if (v_isSharedCheck_3033_ == 0)
{
lean_object* v_unused_3034_; 
v_unused_3034_ = lean_ctor_get(v_s_3022_, 2);
lean_dec(v_unused_3034_);
v___x_3027_ = v_s_3022_;
v_isShared_3028_ = v_isSharedCheck_3033_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_lazyAssignment_3025_);
lean_inc(v_assignment_3024_);
lean_dec(v_s_3022_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3033_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3029_; lean_object* v___x_3031_; 
v___x_3029_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_3020_, v_tree_3021_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 2, v___x_3029_);
v___x_3031_ = v___x_3027_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_assignment_3024_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v_lazyAssignment_3025_);
lean_ctor_set(v_reuseFailAlloc_3032_, 2, v___x_3029_);
lean_ctor_set_uint8(v_reuseFailAlloc_3032_, sizeof(void*)*3, v_enabled_3023_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object* v_treesSaved_3035_, lean_object* v_modifyInfoState_3036_, lean_object* v_tree_3037_){
_start:
{
lean_object* v___f_3038_; lean_object* v___x_3039_; 
v___f_3038_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3038_, 0, v_treesSaved_3035_);
lean_closure_set(v___f_3038_, 1, v_tree_3037_);
v___x_3039_ = lean_apply_1(v_modifyInfoState_3036_, v___f_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object* v_mkInfoTree_3040_, lean_object* v_toBind_3041_, lean_object* v___f_3042_, lean_object* v_st_3043_){
_start:
{
lean_object* v_trees_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v_trees_3044_ = lean_ctor_get(v_st_3043_, 2);
lean_inc_ref(v_trees_3044_);
lean_dec_ref(v_st_3043_);
v___x_3045_ = lean_apply_1(v_mkInfoTree_3040_, v_trees_3044_);
v___x_3046_ = lean_apply_4(v_toBind_3041_, lean_box(0), lean_box(0), v___x_3045_, v___f_3042_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object* v_toBind_3047_, lean_object* v_getInfoState_3048_, lean_object* v___f_3049_, lean_object* v_x_3050_){
_start:
{
lean_object* v___x_3051_; 
v___x_3051_ = lean_apply_4(v_toBind_3047_, lean_box(0), lean_box(0), v_getInfoState_3048_, v___f_3049_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object* v_toBind_3052_, lean_object* v_getInfoState_3053_, lean_object* v___f_3054_, lean_object* v_x_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(v_toBind_3052_, v_getInfoState_3053_, v___f_3054_, v_x_3055_);
lean_dec(v_x_3055_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object* v_toFunctor_3057_, lean_object* v_modifyInfoState_3058_, lean_object* v_mkInfoTree_3059_, lean_object* v_toBind_3060_, lean_object* v_getInfoState_3061_, lean_object* v_inst_3062_, lean_object* v_x_3063_, lean_object* v___f_3064_, lean_object* v_treesSaved_3065_){
_start:
{
lean_object* v_map_3066_; lean_object* v___f_3067_; lean_object* v___f_3068_; lean_object* v___f_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v_map_3066_ = lean_ctor_get(v_toFunctor_3057_, 0);
lean_inc(v_map_3066_);
lean_dec_ref(v_toFunctor_3057_);
v___f_3067_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3067_, 0, v_treesSaved_3065_);
lean_closure_set(v___f_3067_, 1, v_modifyInfoState_3058_);
lean_inc(v_toBind_3060_);
v___f_3068_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__2), 4, 3);
lean_closure_set(v___f_3068_, 0, v_mkInfoTree_3059_);
lean_closure_set(v___f_3068_, 1, v_toBind_3060_);
lean_closure_set(v___f_3068_, 2, v___f_3067_);
v___f_3069_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3069_, 0, v_toBind_3060_);
lean_closure_set(v___f_3069_, 1, v_getInfoState_3061_);
lean_closure_set(v___f_3069_, 2, v___f_3068_);
v___x_3070_ = lean_apply_4(v_inst_3062_, lean_box(0), lean_box(0), v_x_3063_, v___f_3069_);
v___x_3071_ = lean_apply_4(v_map_3066_, lean_box(0), lean_box(0), v___f_3064_, v___x_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object* v_inst_3072_, lean_object* v_inst_3073_, lean_object* v_inst_3074_, lean_object* v_x_3075_, lean_object* v_mkInfoTree_3076_){
_start:
{
lean_object* v_toApplicative_3077_; lean_object* v_toBind_3078_; lean_object* v_getInfoState_3079_; lean_object* v_modifyInfoState_3080_; lean_object* v_toFunctor_3081_; lean_object* v___f_3082_; lean_object* v___f_3083_; lean_object* v___f_3084_; lean_object* v___x_3085_; 
v_toApplicative_3077_ = lean_ctor_get(v_inst_3072_, 0);
v_toBind_3078_ = lean_ctor_get(v_inst_3072_, 1);
lean_inc_n(v_toBind_3078_, 3);
v_getInfoState_3079_ = lean_ctor_get(v_inst_3073_, 0);
lean_inc_n(v_getInfoState_3079_, 2);
v_modifyInfoState_3080_ = lean_ctor_get(v_inst_3073_, 1);
v_toFunctor_3081_ = lean_ctor_get(v_toApplicative_3077_, 0);
v___f_3082_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3075_);
lean_inc(v_modifyInfoState_3080_);
lean_inc_ref(v_toFunctor_3081_);
v___f_3083_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__4), 9, 8);
lean_closure_set(v___f_3083_, 0, v_toFunctor_3081_);
lean_closure_set(v___f_3083_, 1, v_modifyInfoState_3080_);
lean_closure_set(v___f_3083_, 2, v_mkInfoTree_3076_);
lean_closure_set(v___f_3083_, 3, v_toBind_3078_);
lean_closure_set(v___f_3083_, 4, v_getInfoState_3079_);
lean_closure_set(v___f_3083_, 5, v_inst_3074_);
lean_closure_set(v___f_3083_, 6, v_x_3075_);
lean_closure_set(v___f_3083_, 7, v___f_3082_);
v___f_3084_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3084_, 0, v_x_3075_);
lean_closure_set(v___f_3084_, 1, v_inst_3072_);
lean_closure_set(v___f_3084_, 2, v_inst_3073_);
lean_closure_set(v___f_3084_, 3, v_toBind_3078_);
lean_closure_set(v___f_3084_, 4, v___f_3083_);
v___x_3085_ = lean_apply_4(v_toBind_3078_, lean_box(0), lean_box(0), v_getInfoState_3079_, v___f_3084_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object* v_m_3086_, lean_object* v_inst_3087_, lean_object* v_inst_3088_, lean_object* v_00_u03b1_3089_, lean_object* v_inst_3090_, lean_object* v_x_3091_, lean_object* v_mkInfoTree_3092_){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3087_, v_inst_3088_, v_inst_3090_, v_x_3091_, v_mkInfoTree_3092_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object* v_trees_3094_, lean_object* v_toPure_3095_, lean_object* v_____do__lift_3096_){
_start:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3097_, 0, v_____do__lift_3096_);
lean_ctor_set(v___x_3097_, 1, v_trees_3094_);
v___x_3098_ = lean_apply_2(v_toPure_3095_, lean_box(0), v___x_3097_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object* v_toPure_3099_, lean_object* v_toBind_3100_, lean_object* v_mkInfo_3101_, lean_object* v_trees_3102_){
_start:
{
lean_object* v___f_3103_; lean_object* v___x_3104_; 
v___f_3103_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3103_, 0, v_trees_3102_);
lean_closure_set(v___f_3103_, 1, v_toPure_3099_);
v___x_3104_ = lean_apply_4(v_toBind_3100_, lean_box(0), lean_box(0), v_mkInfo_3101_, v___f_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object* v_inst_3105_, lean_object* v_inst_3106_, lean_object* v_inst_3107_, lean_object* v_x_3108_, lean_object* v_mkInfo_3109_){
_start:
{
lean_object* v_toApplicative_3110_; lean_object* v_toBind_3111_; lean_object* v_toPure_3112_; lean_object* v___f_3113_; lean_object* v___x_3114_; 
v_toApplicative_3110_ = lean_ctor_get(v_inst_3105_, 0);
v_toBind_3111_ = lean_ctor_get(v_inst_3105_, 1);
v_toPure_3112_ = lean_ctor_get(v_toApplicative_3110_, 1);
lean_inc(v_toBind_3111_);
lean_inc(v_toPure_3112_);
v___f_3113_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3113_, 0, v_toPure_3112_);
lean_closure_set(v___f_3113_, 1, v_toBind_3111_);
lean_closure_set(v___f_3113_, 2, v_mkInfo_3109_);
v___x_3114_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3105_, v_inst_3106_, v_inst_3107_, v_x_3108_, v___f_3113_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object* v_m_3115_, lean_object* v_inst_3116_, lean_object* v_inst_3117_, lean_object* v_00_u03b1_3118_, lean_object* v_inst_3119_, lean_object* v_x_3120_, lean_object* v_mkInfo_3121_){
_start:
{
lean_object* v_toApplicative_3122_; lean_object* v_toBind_3123_; lean_object* v_toPure_3124_; lean_object* v___f_3125_; lean_object* v___x_3126_; 
v_toApplicative_3122_ = lean_ctor_get(v_inst_3116_, 0);
v_toBind_3123_ = lean_ctor_get(v_inst_3116_, 1);
v_toPure_3124_ = lean_ctor_get(v_toApplicative_3122_, 1);
lean_inc(v_toBind_3123_);
lean_inc(v_toPure_3124_);
v___f_3125_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3125_, 0, v_toPure_3124_);
lean_closure_set(v___f_3125_, 1, v_toBind_3123_);
lean_closure_set(v___f_3125_, 2, v_mkInfo_3121_);
v___x_3126_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3116_, v_inst_3117_, v_inst_3119_, v_x_3120_, v___f_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object* v_treesSaved_3127_, lean_object* v_trees_3128_, lean_object* v_s_3129_){
_start:
{
uint8_t v_enabled_3130_; lean_object* v_assignment_3131_; lean_object* v_lazyAssignment_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3140_; 
v_enabled_3130_ = lean_ctor_get_uint8(v_s_3129_, sizeof(void*)*3);
v_assignment_3131_ = lean_ctor_get(v_s_3129_, 0);
v_lazyAssignment_3132_ = lean_ctor_get(v_s_3129_, 1);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_s_3129_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; 
v_unused_3141_ = lean_ctor_get(v_s_3129_, 2);
lean_dec(v_unused_3141_);
v___x_3134_ = v_s_3129_;
v_isShared_3135_ = v_isSharedCheck_3140_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_lazyAssignment_3132_);
lean_inc(v_assignment_3131_);
lean_dec(v_s_3129_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3140_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; lean_object* v___x_3138_; 
v___x_3136_ = l_Lean_PersistentArray_append___redArg(v_treesSaved_3127_, v_trees_3128_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 2, v___x_3136_);
v___x_3138_ = v___x_3134_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_assignment_3131_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v_lazyAssignment_3132_);
lean_ctor_set(v_reuseFailAlloc_3139_, 2, v___x_3136_);
lean_ctor_set_uint8(v_reuseFailAlloc_3139_, sizeof(void*)*3, v_enabled_3130_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object* v_treesSaved_3142_, lean_object* v_trees_3143_, lean_object* v_s_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_3142_, v_trees_3143_, v_s_3144_);
lean_dec_ref(v_trees_3143_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object* v_treesSaved_3146_, lean_object* v_modifyInfoState_3147_, lean_object* v_trees_3148_){
_start:
{
lean_object* v___f_3149_; lean_object* v___x_3150_; 
v___f_3149_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3149_, 0, v_treesSaved_3146_);
lean_closure_set(v___f_3149_, 1, v_trees_3148_);
v___x_3150_ = lean_apply_1(v_modifyInfoState_3147_, v___f_3149_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object* v_toPure_3151_, lean_object* v_tree_3152_, lean_object* v_____do__lift_3153_){
_start:
{
if (lean_obj_tag(v_____do__lift_3153_) == 0)
{
lean_object* v___x_3154_; 
v___x_3154_ = lean_apply_2(v_toPure_3151_, lean_box(0), v_tree_3152_);
return v___x_3154_;
}
else
{
lean_object* v_val_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v_val_3155_ = lean_ctor_get(v_____do__lift_3153_, 0);
lean_inc(v_val_3155_);
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v_val_3155_);
lean_ctor_set(v___x_3156_, 1, v_tree_3152_);
v___x_3157_ = lean_apply_2(v_toPure_3151_, lean_box(0), v___x_3156_);
return v___x_3157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object* v_toPure_3158_, lean_object* v_tree_3159_, lean_object* v_____do__lift_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_3158_, v_tree_3159_, v_____do__lift_3160_);
lean_dec(v_____do__lift_3160_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object* v_assignment_3162_, lean_object* v_toPure_3163_, lean_object* v_toBind_3164_, lean_object* v_ctx_x3f_3165_, lean_object* v_tree_3166_){
_start:
{
lean_object* v_tree_3167_; lean_object* v___f_3168_; lean_object* v___x_3169_; 
v_tree_3167_ = l_Lean_Elab_InfoTree_substitute(v_tree_3166_, v_assignment_3162_);
v___f_3168_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3168_, 0, v_toPure_3163_);
lean_closure_set(v___f_3168_, 1, v_tree_3167_);
v___x_3169_ = lean_apply_4(v_toBind_3164_, lean_box(0), lean_box(0), v_ctx_x3f_3165_, v___f_3168_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object* v_assignment_3170_, lean_object* v_toPure_3171_, lean_object* v_toBind_3172_, lean_object* v_ctx_x3f_3173_, lean_object* v_tree_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(v_assignment_3170_, v_toPure_3171_, v_toBind_3172_, v_ctx_x3f_3173_, v_tree_3174_);
lean_dec_ref(v_assignment_3170_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object* v_toPure_3176_, lean_object* v_toBind_3177_, lean_object* v_ctx_x3f_3178_, lean_object* v_inst_3179_, lean_object* v___f_3180_, lean_object* v_st_3181_){
_start:
{
lean_object* v_assignment_3182_; lean_object* v_trees_3183_; lean_object* v___f_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v_assignment_3182_ = lean_ctor_get(v_st_3181_, 0);
lean_inc_ref(v_assignment_3182_);
v_trees_3183_ = lean_ctor_get(v_st_3181_, 2);
lean_inc_ref(v_trees_3183_);
lean_dec_ref(v_st_3181_);
lean_inc(v_toBind_3177_);
v___f_3184_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_3184_, 0, v_assignment_3182_);
lean_closure_set(v___f_3184_, 1, v_toPure_3176_);
lean_closure_set(v___f_3184_, 2, v_toBind_3177_);
lean_closure_set(v___f_3184_, 3, v_ctx_x3f_3178_);
v___x_3185_ = l_Lean_PersistentArray_mapM___redArg(v_inst_3179_, v___f_3184_, v_trees_3183_);
v___x_3186_ = lean_apply_4(v_toBind_3177_, lean_box(0), lean_box(0), v___x_3185_, v___f_3180_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object* v_toFunctor_3187_, lean_object* v_modifyInfoState_3188_, lean_object* v_toPure_3189_, lean_object* v_toBind_3190_, lean_object* v_ctx_x3f_3191_, lean_object* v_inst_3192_, lean_object* v_getInfoState_3193_, lean_object* v_inst_3194_, lean_object* v_x_3195_, lean_object* v___f_3196_, lean_object* v_treesSaved_3197_){
_start:
{
lean_object* v_map_3198_; lean_object* v___f_3199_; lean_object* v___f_3200_; lean_object* v___f_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v_map_3198_ = lean_ctor_get(v_toFunctor_3187_, 0);
lean_inc(v_map_3198_);
lean_dec_ref(v_toFunctor_3187_);
v___f_3199_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3199_, 0, v_treesSaved_3197_);
lean_closure_set(v___f_3199_, 1, v_modifyInfoState_3188_);
lean_inc(v_toBind_3190_);
v___f_3200_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4), 6, 5);
lean_closure_set(v___f_3200_, 0, v_toPure_3189_);
lean_closure_set(v___f_3200_, 1, v_toBind_3190_);
lean_closure_set(v___f_3200_, 2, v_ctx_x3f_3191_);
lean_closure_set(v___f_3200_, 3, v_inst_3192_);
lean_closure_set(v___f_3200_, 4, v___f_3199_);
v___f_3201_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3201_, 0, v_toBind_3190_);
lean_closure_set(v___f_3201_, 1, v_getInfoState_3193_);
lean_closure_set(v___f_3201_, 2, v___f_3200_);
v___x_3202_ = lean_apply_4(v_inst_3194_, lean_box(0), lean_box(0), v_x_3195_, v___f_3201_);
v___x_3203_ = lean_apply_4(v_map_3198_, lean_box(0), lean_box(0), v___f_3196_, v___x_3202_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object* v_inst_3204_, lean_object* v_inst_3205_, lean_object* v_inst_3206_, lean_object* v_x_3207_, lean_object* v_ctx_x3f_3208_){
_start:
{
lean_object* v_toApplicative_3209_; lean_object* v_toBind_3210_; lean_object* v_getInfoState_3211_; lean_object* v_modifyInfoState_3212_; lean_object* v_toFunctor_3213_; lean_object* v_toPure_3214_; lean_object* v___f_3215_; lean_object* v___f_3216_; lean_object* v___f_3217_; lean_object* v___x_3218_; 
v_toApplicative_3209_ = lean_ctor_get(v_inst_3204_, 0);
v_toBind_3210_ = lean_ctor_get(v_inst_3204_, 1);
lean_inc_n(v_toBind_3210_, 3);
v_getInfoState_3211_ = lean_ctor_get(v_inst_3205_, 0);
lean_inc_n(v_getInfoState_3211_, 2);
v_modifyInfoState_3212_ = lean_ctor_get(v_inst_3205_, 1);
v_toFunctor_3213_ = lean_ctor_get(v_toApplicative_3209_, 0);
v_toPure_3214_ = lean_ctor_get(v_toApplicative_3209_, 1);
v___f_3215_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3207_);
lean_inc_ref(v_inst_3204_);
lean_inc(v_toPure_3214_);
lean_inc(v_modifyInfoState_3212_);
lean_inc_ref(v_toFunctor_3213_);
v___f_3216_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6), 11, 10);
lean_closure_set(v___f_3216_, 0, v_toFunctor_3213_);
lean_closure_set(v___f_3216_, 1, v_modifyInfoState_3212_);
lean_closure_set(v___f_3216_, 2, v_toPure_3214_);
lean_closure_set(v___f_3216_, 3, v_toBind_3210_);
lean_closure_set(v___f_3216_, 4, v_ctx_x3f_3208_);
lean_closure_set(v___f_3216_, 5, v_inst_3204_);
lean_closure_set(v___f_3216_, 6, v_getInfoState_3211_);
lean_closure_set(v___f_3216_, 7, v_inst_3206_);
lean_closure_set(v___f_3216_, 8, v_x_3207_);
lean_closure_set(v___f_3216_, 9, v___f_3215_);
v___f_3217_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3217_, 0, v_x_3207_);
lean_closure_set(v___f_3217_, 1, v_inst_3204_);
lean_closure_set(v___f_3217_, 2, v_inst_3205_);
lean_closure_set(v___f_3217_, 3, v_toBind_3210_);
lean_closure_set(v___f_3217_, 4, v___f_3216_);
v___x_3218_ = lean_apply_4(v_toBind_3210_, lean_box(0), lean_box(0), v_getInfoState_3211_, v___f_3217_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object* v_m_3219_, lean_object* v_inst_3220_, lean_object* v_inst_3221_, lean_object* v_00_u03b1_3222_, lean_object* v_inst_3223_, lean_object* v_x_3224_, lean_object* v_ctx_x3f_3225_){
_start:
{
lean_object* v___x_3226_; 
v___x_3226_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3220_, v_inst_3221_, v_inst_3223_, v_x_3224_, v_ctx_x3f_3225_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object* v_toPure_3227_, lean_object* v_____do__lift_3228_){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3229_, 0, v_____do__lift_3228_);
v___x_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
v___x_3231_ = lean_apply_2(v_toPure_3227_, lean_box(0), v___x_3230_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object* v_inst_3232_, lean_object* v_inst_3233_, lean_object* v_inst_3234_, lean_object* v_inst_3235_, lean_object* v_inst_3236_, lean_object* v_inst_3237_, lean_object* v_inst_3238_, lean_object* v_inst_3239_, lean_object* v_inst_3240_, lean_object* v_x_3241_){
_start:
{
lean_object* v_toApplicative_3242_; lean_object* v_toBind_3243_; lean_object* v_toPure_3244_; lean_object* v___x_3245_; lean_object* v___f_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v_toApplicative_3242_ = lean_ctor_get(v_inst_3232_, 0);
v_toBind_3243_ = lean_ctor_get(v_inst_3232_, 1);
v_toPure_3244_ = lean_ctor_get(v_toApplicative_3242_, 1);
lean_inc_ref(v_inst_3232_);
v___x_3245_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_3232_, v_inst_3236_, v_inst_3238_, v_inst_3237_, v_inst_3239_, v_inst_3234_, v_inst_3240_);
lean_inc(v_toPure_3244_);
v___f_3246_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3246_, 0, v_toPure_3244_);
lean_inc(v_toBind_3243_);
v___x_3247_ = lean_apply_4(v_toBind_3243_, lean_box(0), lean_box(0), v___x_3245_, v___f_3246_);
v___x_3248_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3232_, v_inst_3233_, v_inst_3235_, v_x_3241_, v___x_3247_);
return v___x_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object* v_m_3249_, lean_object* v_inst_3250_, lean_object* v_inst_3251_, lean_object* v_00_u03b1_3252_, lean_object* v_inst_3253_, lean_object* v_inst_3254_, lean_object* v_inst_3255_, lean_object* v_inst_3256_, lean_object* v_inst_3257_, lean_object* v_inst_3258_, lean_object* v_inst_3259_, lean_object* v_x_3260_){
_start:
{
lean_object* v___x_3261_; 
v___x_3261_ = l_Lean_Elab_withSaveInfoContext___redArg(v_inst_3250_, v_inst_3251_, v_inst_3253_, v_inst_3254_, v_inst_3255_, v_inst_3256_, v_inst_3257_, v_inst_3258_, v_inst_3259_, v_x_3260_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object* v_toPure_3262_, lean_object* v_____x_3263_){
_start:
{
if (lean_obj_tag(v_____x_3263_) == 1)
{
lean_object* v_val_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3273_; 
v_val_3264_ = lean_ctor_get(v_____x_3263_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v_____x_3263_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3266_ = v_____x_3263_;
v_isShared_3267_ = v_isSharedCheck_3273_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_val_3264_);
lean_dec(v_____x_3263_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3273_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3268_; lean_object* v___x_3270_; 
v___x_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3268_, 0, v_val_3264_);
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 0, v___x_3268_);
v___x_3270_ = v___x_3266_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3268_);
v___x_3270_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
lean_object* v___x_3271_; 
v___x_3271_ = lean_apply_2(v_toPure_3262_, lean_box(0), v___x_3270_);
return v___x_3271_;
}
}
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
lean_dec(v_____x_3263_);
v___x_3274_ = lean_box(0);
v___x_3275_ = lean_apply_2(v_toPure_3262_, lean_box(0), v___x_3274_);
return v___x_3275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object* v_inst_3276_, lean_object* v_inst_3277_, lean_object* v_inst_3278_, lean_object* v_inst_3279_, lean_object* v_x_3280_){
_start:
{
lean_object* v_toApplicative_3281_; lean_object* v_toBind_3282_; lean_object* v_toPure_3283_; lean_object* v___f_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v_toApplicative_3281_ = lean_ctor_get(v_inst_3276_, 0);
v_toBind_3282_ = lean_ctor_get(v_inst_3276_, 1);
v_toPure_3283_ = lean_ctor_get(v_toApplicative_3281_, 1);
lean_inc(v_toPure_3283_);
v___f_3284_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3284_, 0, v_toPure_3283_);
lean_inc(v_toBind_3282_);
v___x_3285_ = lean_apply_4(v_toBind_3282_, lean_box(0), lean_box(0), v_inst_3279_, v___f_3284_);
v___x_3286_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3276_, v_inst_3277_, v_inst_3278_, v_x_3280_, v___x_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object* v_m_3287_, lean_object* v_inst_3288_, lean_object* v_inst_3289_, lean_object* v_00_u03b1_3290_, lean_object* v_inst_3291_, lean_object* v_inst_3292_, lean_object* v_x_3293_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(v_inst_3288_, v_inst_3289_, v_inst_3291_, v_inst_3292_, v_x_3293_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object* v_toPure_3295_, lean_object* v_autoImplicits_3296_){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3297_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3297_, 0, v_autoImplicits_3296_);
v___x_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
v___x_3299_ = lean_apply_2(v_toPure_3295_, lean_box(0), v___x_3298_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object* v_inst_3300_, lean_object* v_inst_3301_, lean_object* v_inst_3302_, lean_object* v_inst_3303_, lean_object* v_x_3304_){
_start:
{
lean_object* v_toApplicative_3305_; lean_object* v_toBind_3306_; lean_object* v_toPure_3307_; lean_object* v___f_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v_toApplicative_3305_ = lean_ctor_get(v_inst_3300_, 0);
v_toBind_3306_ = lean_ctor_get(v_inst_3300_, 1);
v_toPure_3307_ = lean_ctor_get(v_toApplicative_3305_, 1);
lean_inc(v_toPure_3307_);
v___f_3308_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3308_, 0, v_toPure_3307_);
lean_inc(v_toBind_3306_);
v___x_3309_ = lean_apply_4(v_toBind_3306_, lean_box(0), lean_box(0), v_inst_3303_, v___f_3308_);
v___x_3310_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3300_, v_inst_3301_, v_inst_3302_, v_x_3304_, v___x_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object* v_m_3311_, lean_object* v_inst_3312_, lean_object* v_inst_3313_, lean_object* v_00_u03b1_3314_, lean_object* v_inst_3315_, lean_object* v_inst_3316_, lean_object* v_x_3317_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(v_inst_3312_, v_inst_3313_, v_inst_3315_, v_inst_3316_, v_x_3317_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object* v___x_3319_, lean_object* v___x_3320_, lean_object* v_mvarId_3321_, lean_object* v_toPure_3322_, lean_object* v_____do__lift_3323_){
_start:
{
lean_object* v_assignment_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v_assignment_3324_ = lean_ctor_get(v_____do__lift_3323_, 0);
v___x_3325_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_3319_, v___x_3320_, v_assignment_3324_, v_mvarId_3321_);
v___x_3326_ = lean_apply_2(v_toPure_3322_, lean_box(0), v___x_3325_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object* v___x_3327_, lean_object* v___x_3328_, lean_object* v_mvarId_3329_, lean_object* v_toPure_3330_, lean_object* v_____do__lift_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(v___x_3327_, v___x_3328_, v_mvarId_3329_, v_toPure_3330_, v_____do__lift_3331_);
lean_dec_ref(v_____do__lift_3331_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object* v_inst_3335_, lean_object* v_inst_3336_, lean_object* v_mvarId_3337_){
_start:
{
lean_object* v_toApplicative_3338_; lean_object* v_toBind_3339_; lean_object* v_getInfoState_3340_; lean_object* v_toPure_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___f_3344_; lean_object* v___x_3345_; 
v_toApplicative_3338_ = lean_ctor_get(v_inst_3335_, 0);
lean_inc_ref(v_toApplicative_3338_);
v_toBind_3339_ = lean_ctor_get(v_inst_3335_, 1);
lean_inc(v_toBind_3339_);
lean_dec_ref(v_inst_3335_);
v_getInfoState_3340_ = lean_ctor_get(v_inst_3336_, 0);
lean_inc(v_getInfoState_3340_);
lean_dec_ref(v_inst_3336_);
v_toPure_3341_ = lean_ctor_get(v_toApplicative_3338_, 1);
lean_inc(v_toPure_3341_);
lean_dec_ref(v_toApplicative_3338_);
v___x_3342_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3343_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___f_3344_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3344_, 0, v___x_3342_);
lean_closure_set(v___f_3344_, 1, v___x_3343_);
lean_closure_set(v___f_3344_, 2, v_mvarId_3337_);
lean_closure_set(v___f_3344_, 3, v_toPure_3341_);
v___x_3345_ = lean_apply_4(v_toBind_3339_, lean_box(0), lean_box(0), v_getInfoState_3340_, v___f_3344_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* v_m_3346_, lean_object* v_inst_3347_, lean_object* v_inst_3348_, lean_object* v_mvarId_3349_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3347_, v_inst_3348_, v_mvarId_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object* v___x_3351_, lean_object* v___x_3352_, lean_object* v_mvarId_3353_, lean_object* v_infoTree_3354_, lean_object* v_s_3355_){
_start:
{
uint8_t v_enabled_3356_; lean_object* v_assignment_3357_; lean_object* v_lazyAssignment_3358_; lean_object* v_trees_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3367_; 
v_enabled_3356_ = lean_ctor_get_uint8(v_s_3355_, sizeof(void*)*3);
v_assignment_3357_ = lean_ctor_get(v_s_3355_, 0);
v_lazyAssignment_3358_ = lean_ctor_get(v_s_3355_, 1);
v_trees_3359_ = lean_ctor_get(v_s_3355_, 2);
v_isSharedCheck_3367_ = !lean_is_exclusive(v_s_3355_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3361_ = v_s_3355_;
v_isShared_3362_ = v_isSharedCheck_3367_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_trees_3359_);
lean_inc(v_lazyAssignment_3358_);
lean_inc(v_assignment_3357_);
lean_dec(v_s_3355_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3367_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3363_; lean_object* v___x_3365_; 
v___x_3363_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3351_, v___x_3352_, v_assignment_3357_, v_mvarId_3353_, v_infoTree_3354_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 0, v___x_3363_);
v___x_3365_ = v___x_3361_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v_lazyAssignment_3358_);
lean_ctor_set(v_reuseFailAlloc_3366_, 2, v_trees_3359_);
lean_ctor_set_uint8(v_reuseFailAlloc_3366_, sizeof(void*)*3, v_enabled_3356_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3371_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2));
v___x_3372_ = lean_unsigned_to_nat(2u);
v___x_3373_ = lean_unsigned_to_nat(384u);
v___x_3374_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1));
v___x_3375_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0));
v___x_3376_ = l_mkPanicMessageWithDecl(v___x_3375_, v___x_3374_, v___x_3373_, v___x_3372_, v___x_3371_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object* v_inst_3377_, lean_object* v___f_3378_, lean_object* v___x_3379_, lean_object* v_____do__lift_3380_){
_start:
{
if (lean_obj_tag(v_____do__lift_3380_) == 0)
{
lean_object* v_modifyInfoState_3381_; lean_object* v___x_3382_; 
v_modifyInfoState_3381_ = lean_ctor_get(v_inst_3377_, 1);
lean_inc(v_modifyInfoState_3381_);
lean_dec_ref(v_inst_3377_);
v___x_3382_ = lean_apply_1(v_modifyInfoState_3381_, v___f_3378_);
return v___x_3382_;
}
else
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
lean_dec_ref(v___f_3378_);
lean_dec_ref(v_inst_3377_);
v___x_3383_ = lean_obj_once(&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3, &l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3_once, _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3);
v___x_3384_ = l_panic___redArg(v___x_3379_, v___x_3383_);
return v___x_3384_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object* v_inst_3385_, lean_object* v___f_3386_, lean_object* v___x_3387_, lean_object* v_____do__lift_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(v_inst_3385_, v___f_3386_, v___x_3387_, v_____do__lift_3388_);
lean_dec(v_____do__lift_3388_);
lean_dec(v___x_3387_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object* v_inst_3390_, lean_object* v_inst_3391_, lean_object* v_mvarId_3392_, lean_object* v_infoTree_3393_){
_start:
{
lean_object* v_toBind_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___f_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___f_3401_; lean_object* v___x_3402_; 
v_toBind_3394_ = lean_ctor_get(v_inst_3390_, 1);
lean_inc(v_toBind_3394_);
v___x_3395_ = lean_box(0);
v___x_3396_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3397_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
lean_inc(v_mvarId_3392_);
v___f_3398_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__0), 5, 4);
lean_closure_set(v___f_3398_, 0, v___x_3396_);
lean_closure_set(v___f_3398_, 1, v___x_3397_);
lean_closure_set(v___f_3398_, 2, v_mvarId_3392_);
lean_closure_set(v___f_3398_, 3, v_infoTree_3393_);
lean_inc_ref(v_inst_3391_);
lean_inc_ref(v_inst_3390_);
v___x_3399_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3390_, v_inst_3391_, v_mvarId_3392_);
v___x_3400_ = l_instInhabitedOfMonad___redArg(v_inst_3390_, v___x_3395_);
v___f_3401_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3401_, 0, v_inst_3391_);
lean_closure_set(v___f_3401_, 1, v___f_3398_);
lean_closure_set(v___f_3401_, 2, v___x_3400_);
v___x_3402_ = lean_apply_4(v_toBind_3394_, lean_box(0), lean_box(0), v___x_3399_, v___f_3401_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* v_m_3403_, lean_object* v_inst_3404_, lean_object* v_inst_3405_, lean_object* v_mvarId_3406_, lean_object* v_infoTree_3407_){
_start:
{
lean_object* v___x_3408_; 
v___x_3408_ = l_Lean_Elab_assignInfoHoleId___redArg(v_inst_3404_, v_inst_3405_, v_mvarId_3406_, v_infoTree_3407_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object* v_stx_3409_, lean_object* v_output_3410_, lean_object* v_toPure_3411_, lean_object* v_____do__lift_3412_){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3413_, 0, v_____do__lift_3412_);
lean_ctor_set(v___x_3413_, 1, v_stx_3409_);
lean_ctor_set(v___x_3413_, 2, v_output_3410_);
v___x_3414_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
v___x_3415_ = lean_apply_2(v_toPure_3411_, lean_box(0), v___x_3414_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object* v_inst_3416_, lean_object* v_inst_3417_, lean_object* v_inst_3418_, lean_object* v_inst_3419_, lean_object* v_stx_3420_, lean_object* v_output_3421_, lean_object* v_x_3422_){
_start:
{
lean_object* v_toApplicative_3423_; lean_object* v_toBind_3424_; lean_object* v_toPure_3425_; lean_object* v___f_3426_; lean_object* v_mkInfo_3427_; lean_object* v___f_3428_; lean_object* v___x_3429_; 
v_toApplicative_3423_ = lean_ctor_get(v_inst_3417_, 0);
v_toBind_3424_ = lean_ctor_get(v_inst_3417_, 1);
v_toPure_3425_ = lean_ctor_get(v_toApplicative_3423_, 1);
lean_inc_n(v_toPure_3425_, 2);
v___f_3426_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3426_, 0, v_stx_3420_);
lean_closure_set(v___f_3426_, 1, v_output_3421_);
lean_closure_set(v___f_3426_, 2, v_toPure_3425_);
lean_inc_n(v_toBind_3424_, 2);
v_mkInfo_3427_ = lean_apply_4(v_toBind_3424_, lean_box(0), lean_box(0), v_inst_3419_, v___f_3426_);
v___f_3428_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3428_, 0, v_toPure_3425_);
lean_closure_set(v___f_3428_, 1, v_toBind_3424_);
lean_closure_set(v___f_3428_, 2, v_mkInfo_3427_);
v___x_3429_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3417_, v_inst_3418_, v_inst_3416_, v_x_3422_, v___f_3428_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* v_m_3430_, lean_object* v_00_u03b1_3431_, lean_object* v_inst_3432_, lean_object* v_inst_3433_, lean_object* v_inst_3434_, lean_object* v_inst_3435_, lean_object* v_stx_3436_, lean_object* v_output_3437_, lean_object* v_x_3438_){
_start:
{
lean_object* v___x_3439_; 
v___x_3439_ = l_Lean_Elab_withMacroExpansionInfo___redArg(v_inst_3432_, v_inst_3433_, v_inst_3434_, v_inst_3435_, v_stx_3436_, v_output_3437_, v_x_3438_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object* v_treesSaved_3440_, lean_object* v___x_3441_, lean_object* v___x_3442_, lean_object* v___x_3443_, lean_object* v_mvarId_3444_, lean_object* v_s_3445_){
_start:
{
lean_object* v_trees_3446_; uint8_t v_enabled_3447_; lean_object* v_assignment_3448_; lean_object* v_lazyAssignment_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3466_; 
v_trees_3446_ = lean_ctor_get(v_s_3445_, 2);
v_enabled_3447_ = lean_ctor_get_uint8(v_s_3445_, sizeof(void*)*3);
v_assignment_3448_ = lean_ctor_get(v_s_3445_, 0);
v_lazyAssignment_3449_ = lean_ctor_get(v_s_3445_, 1);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_s_3445_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3451_ = v_s_3445_;
v_isShared_3452_ = v_isSharedCheck_3466_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_trees_3446_);
lean_inc(v_lazyAssignment_3449_);
lean_inc(v_assignment_3448_);
lean_dec(v_s_3445_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3466_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v_size_3453_; lean_object* v___x_3454_; uint8_t v___x_3455_; 
v_size_3453_ = lean_ctor_get(v_trees_3446_, 2);
v___x_3454_ = lean_unsigned_to_nat(0u);
v___x_3455_ = lean_nat_dec_lt(v___x_3454_, v_size_3453_);
if (v___x_3455_ == 0)
{
lean_object* v___x_3457_; 
lean_dec_ref(v_trees_3446_);
lean_dec(v_mvarId_3444_);
lean_dec_ref(v___x_3443_);
lean_dec_ref(v___x_3442_);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 2, v_treesSaved_3440_);
v___x_3457_ = v___x_3451_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_assignment_3448_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_lazyAssignment_3449_);
lean_ctor_set(v_reuseFailAlloc_3458_, 2, v_treesSaved_3440_);
lean_ctor_set_uint8(v_reuseFailAlloc_3458_, sizeof(void*)*3, v_enabled_3447_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3464_; 
v___x_3459_ = lean_unsigned_to_nat(1u);
v___x_3460_ = lean_nat_sub(v_size_3453_, v___x_3459_);
v___x_3461_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3441_, v_trees_3446_, v___x_3460_);
lean_dec(v___x_3460_);
lean_dec_ref(v_trees_3446_);
v___x_3462_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3442_, v___x_3443_, v_assignment_3448_, v_mvarId_3444_, v___x_3461_);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 2, v_treesSaved_3440_);
lean_ctor_set(v___x_3451_, 0, v___x_3462_);
v___x_3464_ = v___x_3451_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3462_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_lazyAssignment_3449_);
lean_ctor_set(v_reuseFailAlloc_3465_, 2, v_treesSaved_3440_);
lean_ctor_set_uint8(v_reuseFailAlloc_3465_, sizeof(void*)*3, v_enabled_3447_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1___boxed(lean_object* v_treesSaved_3467_, lean_object* v___x_3468_, lean_object* v___x_3469_, lean_object* v___x_3470_, lean_object* v_mvarId_3471_, lean_object* v_s_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l_Lean_Elab_withInfoHole___redArg___lam__1(v_treesSaved_3467_, v___x_3468_, v___x_3469_, v___x_3470_, v_mvarId_3471_, v_s_3472_);
lean_dec_ref(v___x_3468_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object* v_modifyInfoState_3474_, lean_object* v___f_3475_, lean_object* v_x_3476_){
_start:
{
lean_object* v___x_3477_; 
v___x_3477_ = lean_apply_1(v_modifyInfoState_3474_, v___f_3475_);
return v___x_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object* v_modifyInfoState_3478_, lean_object* v___f_3479_, lean_object* v_x_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_3478_, v___f_3479_, v_x_3480_);
lean_dec(v_x_3480_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object* v_toFunctor_3482_, lean_object* v___x_3483_, lean_object* v___x_3484_, lean_object* v___x_3485_, lean_object* v_mvarId_3486_, lean_object* v_modifyInfoState_3487_, lean_object* v_inst_3488_, lean_object* v_x_3489_, lean_object* v___f_3490_, lean_object* v_treesSaved_3491_){
_start:
{
lean_object* v_map_3492_; lean_object* v___f_3493_; lean_object* v___f_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v_map_3492_ = lean_ctor_get(v_toFunctor_3482_, 0);
lean_inc(v_map_3492_);
lean_dec_ref(v_toFunctor_3482_);
v___f_3493_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_3493_, 0, v_treesSaved_3491_);
lean_closure_set(v___f_3493_, 1, v___x_3483_);
lean_closure_set(v___f_3493_, 2, v___x_3484_);
lean_closure_set(v___f_3493_, 3, v___x_3485_);
lean_closure_set(v___f_3493_, 4, v_mvarId_3486_);
v___f_3494_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3494_, 0, v_modifyInfoState_3487_);
lean_closure_set(v___f_3494_, 1, v___f_3493_);
v___x_3495_ = lean_apply_4(v_inst_3488_, lean_box(0), lean_box(0), v_x_3489_, v___f_3494_);
v___x_3496_ = lean_apply_4(v_map_3492_, lean_box(0), lean_box(0), v___f_3490_, v___x_3495_);
return v___x_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object* v_inst_3497_, lean_object* v_inst_3498_, lean_object* v_inst_3499_, lean_object* v_mvarId_3500_, lean_object* v_x_3501_){
_start:
{
lean_object* v_toApplicative_3502_; lean_object* v_toBind_3503_; lean_object* v_getInfoState_3504_; lean_object* v_modifyInfoState_3505_; lean_object* v_toFunctor_3506_; lean_object* v___f_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___f_3511_; lean_object* v___f_3512_; lean_object* v___x_3513_; 
v_toApplicative_3502_ = lean_ctor_get(v_inst_3498_, 0);
v_toBind_3503_ = lean_ctor_get(v_inst_3498_, 1);
lean_inc_n(v_toBind_3503_, 2);
v_getInfoState_3504_ = lean_ctor_get(v_inst_3499_, 0);
lean_inc(v_getInfoState_3504_);
v_modifyInfoState_3505_ = lean_ctor_get(v_inst_3499_, 1);
v_toFunctor_3506_ = lean_ctor_get(v_toApplicative_3502_, 0);
v___f_3507_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
v___x_3508_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3509_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3510_ = l_Lean_Elab_instInhabitedInfoTree_default;
lean_inc(v_x_3501_);
lean_inc(v_modifyInfoState_3505_);
lean_inc_ref(v_toFunctor_3506_);
v___f_3511_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3511_, 0, v_toFunctor_3506_);
lean_closure_set(v___f_3511_, 1, v___x_3510_);
lean_closure_set(v___f_3511_, 2, v___x_3508_);
lean_closure_set(v___f_3511_, 3, v___x_3509_);
lean_closure_set(v___f_3511_, 4, v_mvarId_3500_);
lean_closure_set(v___f_3511_, 5, v_modifyInfoState_3505_);
lean_closure_set(v___f_3511_, 6, v_inst_3497_);
lean_closure_set(v___f_3511_, 7, v_x_3501_);
lean_closure_set(v___f_3511_, 8, v___f_3507_);
v___f_3512_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3512_, 0, v_x_3501_);
lean_closure_set(v___f_3512_, 1, v_inst_3498_);
lean_closure_set(v___f_3512_, 2, v_inst_3499_);
lean_closure_set(v___f_3512_, 3, v_toBind_3503_);
lean_closure_set(v___f_3512_, 4, v___f_3511_);
v___x_3513_ = lean_apply_4(v_toBind_3503_, lean_box(0), lean_box(0), v_getInfoState_3504_, v___f_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object* v_m_3514_, lean_object* v_00_u03b1_3515_, lean_object* v_inst_3516_, lean_object* v_inst_3517_, lean_object* v_inst_3518_, lean_object* v_mvarId_3519_, lean_object* v_x_3520_){
_start:
{
lean_object* v_toApplicative_3521_; lean_object* v_toBind_3522_; lean_object* v_getInfoState_3523_; lean_object* v_modifyInfoState_3524_; lean_object* v_toFunctor_3525_; lean_object* v___f_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___f_3530_; lean_object* v___f_3531_; lean_object* v___x_3532_; 
v_toApplicative_3521_ = lean_ctor_get(v_inst_3517_, 0);
v_toBind_3522_ = lean_ctor_get(v_inst_3517_, 1);
lean_inc_n(v_toBind_3522_, 2);
v_getInfoState_3523_ = lean_ctor_get(v_inst_3518_, 0);
lean_inc(v_getInfoState_3523_);
v_modifyInfoState_3524_ = lean_ctor_get(v_inst_3518_, 1);
v_toFunctor_3525_ = lean_ctor_get(v_toApplicative_3521_, 0);
v___f_3526_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
v___x_3527_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3528_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3529_ = l_Lean_Elab_instInhabitedInfoTree_default;
lean_inc(v_x_3520_);
lean_inc(v_modifyInfoState_3524_);
lean_inc_ref(v_toFunctor_3525_);
v___f_3530_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3530_, 0, v_toFunctor_3525_);
lean_closure_set(v___f_3530_, 1, v___x_3529_);
lean_closure_set(v___f_3530_, 2, v___x_3527_);
lean_closure_set(v___f_3530_, 3, v___x_3528_);
lean_closure_set(v___f_3530_, 4, v_mvarId_3519_);
lean_closure_set(v___f_3530_, 5, v_modifyInfoState_3524_);
lean_closure_set(v___f_3530_, 6, v_inst_3516_);
lean_closure_set(v___f_3530_, 7, v_x_3520_);
lean_closure_set(v___f_3530_, 8, v___f_3526_);
v___f_3531_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3531_, 0, v_x_3520_);
lean_closure_set(v___f_3531_, 1, v_inst_3517_);
lean_closure_set(v___f_3531_, 2, v_inst_3518_);
lean_closure_set(v___f_3531_, 3, v_toBind_3522_);
lean_closure_set(v___f_3531_, 4, v___f_3530_);
v___x_3532_ = lean_apply_4(v_toBind_3522_, lean_box(0), lean_box(0), v_getInfoState_3523_, v___f_3531_);
return v___x_3532_;
}
}
lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t v_flag_3533_, lean_object* v_s_3534_){
_start:
{
lean_object* v_assignment_3535_; lean_object* v_lazyAssignment_3536_; lean_object* v_trees_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
v_assignment_3535_ = lean_ctor_get(v_s_3534_, 0);
v_lazyAssignment_3536_ = lean_ctor_get(v_s_3534_, 1);
v_trees_3537_ = lean_ctor_get(v_s_3534_, 2);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_s_3534_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v_s_3534_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_trees_3537_);
lean_inc(v_lazyAssignment_3536_);
lean_inc(v_assignment_3535_);
lean_dec(v_s_3534_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_assignment_3535_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v_lazyAssignment_3536_);
lean_ctor_set(v_reuseFailAlloc_3543_, 2, v_trees_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
lean_ctor_set_uint8(v___x_3542_, sizeof(void*)*3, v_flag_3533_);
return v___x_3542_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_enableInfoTree___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_flag_3533_ = stack[0].m_num;
lean_object* v_s_3534_ = stack[1].m_obj;
lean_object* v_res_3545_;
v_res_3545_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_3533_, v_s_3534_);
stack->m_obj
 = v_res_3545_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object* v_flag_3546_, lean_object* v_s_3547_){
_start:
{
uint8_t v_flag_boxed_3548_; lean_object* v_res_3549_; 
v_flag_boxed_3548_ = lean_unbox(v_flag_3546_);
v_res_3549_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_3548_, v_s_3547_);
return v_res_3549_;
}
}
lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object* v_inst_3550_, uint8_t v_flag_3551_){
_start:
{
lean_object* v_modifyInfoState_3552_; lean_object* v___x_3553_; lean_object* v___f_3554_; lean_object* v___x_3555_; 
v_modifyInfoState_3552_ = lean_ctor_get(v_inst_3550_, 1);
lean_inc(v_modifyInfoState_3552_);
lean_dec_ref(v_inst_3550_);
v___x_3553_ = lean_box(v_flag_3551_);
v___f_3554_ = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3554_, 0, v___x_3553_);
v___x_3555_ = lean_apply_1(v_modifyInfoState_3552_, v___f_3554_);
return v___x_3555_;
}
}
LEAN_EXPORT void l_Lean_Elab_enableInfoTree___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3550_ = stack[0].m_obj;
uint8_t v_flag_3551_ = stack[1].m_num;
lean_object* v_res_3556_;
v_res_3556_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3550_, v_flag_3551_);
stack->m_obj
 = v_res_3556_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object* v_inst_3557_, lean_object* v_flag_3558_){
_start:
{
uint8_t v_flag_boxed_3559_; lean_object* v_res_3560_; 
v_flag_boxed_3559_ = lean_unbox(v_flag_3558_);
v_res_3560_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3557_, v_flag_boxed_3559_);
return v_res_3560_;
}
}
lean_object* l_Lean_Elab_enableInfoTree(lean_object* v_m_3561_, lean_object* v_inst_3562_, uint8_t v_flag_3563_){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3562_, v_flag_3563_);
return v___x_3564_;
}
}
LEAN_EXPORT void l_Lean_Elab_enableInfoTree_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3562_ = stack[1].m_obj;
uint8_t v_flag_3563_ = stack[2].m_num;
lean_object* v_res_3565_;
v_res_3565_ = l_Lean_Elab_enableInfoTree(lean_box(0), v_inst_3562_, v_flag_3563_);
stack->m_obj
 = v_res_3565_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object* v_m_3566_, lean_object* v_inst_3567_, lean_object* v_flag_3568_){
_start:
{
uint8_t v_flag_boxed_3569_; lean_object* v_res_3570_; 
v_flag_boxed_3569_ = lean_unbox(v_flag_3568_);
v_res_3570_ = l_Lean_Elab_enableInfoTree(v_m_3566_, v_inst_3567_, v_flag_boxed_3569_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object* v_x_3571_){
_start:
{
lean_object* v_fst_3572_; 
v_fst_3572_ = lean_ctor_get(v_x_3571_, 0);
lean_inc(v_fst_3572_);
return v_fst_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object* v_x_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_3573_);
lean_dec_ref(v_x_3573_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object* v_x_3575_, lean_object* v_____r_3576_){
_start:
{
lean_inc(v_x_3575_);
return v_x_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object* v_x_3577_, lean_object* v_____r_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_3577_, v_____r_3578_);
lean_dec(v_x_3577_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object* v___x_3580_, lean_object* v_x_3581_){
_start:
{
lean_inc(v___x_3580_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object* v___x_3582_, lean_object* v_x_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_3582_, v_x_3583_);
lean_dec(v_x_3583_);
lean_dec(v___x_3582_);
return v_res_3584_;
}
}
lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object* v_toFunctor_3585_, lean_object* v_inst_3586_, uint8_t v_flag_3587_, lean_object* v_toBind_3588_, lean_object* v___f_3589_, lean_object* v_inst_3590_, lean_object* v___f_3591_, lean_object* v_____do__lift_3592_){
_start:
{
uint8_t v_enabled_3593_; lean_object* v_map_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___f_3598_; lean_object* v_y_3599_; lean_object* v___x_3600_; 
v_enabled_3593_ = lean_ctor_get_uint8(v_____do__lift_3592_, sizeof(void*)*3);
v_map_3594_ = lean_ctor_get(v_toFunctor_3585_, 0);
lean_inc(v_map_3594_);
lean_dec_ref(v_toFunctor_3585_);
lean_inc_ref(v_inst_3586_);
v___x_3595_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3586_, v_flag_3587_);
v___x_3596_ = lean_apply_4(v_toBind_3588_, lean_box(0), lean_box(0), v___x_3595_, v___f_3589_);
v___x_3597_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3586_, v_enabled_3593_);
v___f_3598_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_3598_, 0, v___x_3597_);
v_y_3599_ = lean_apply_4(v_inst_3590_, lean_box(0), lean_box(0), v___x_3596_, v___f_3598_);
v___x_3600_ = lean_apply_4(v_map_3594_, lean_box(0), lean_box(0), v___f_3591_, v_y_3599_);
return v___x_3600_;
}
}
LEAN_EXPORT void l_Lean_Elab_withEnableInfoTree___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_toFunctor_3585_ = stack[0].m_obj;
lean_object* v_inst_3586_ = stack[1].m_obj;
uint8_t v_flag_3587_ = stack[2].m_num;
lean_object* v_toBind_3588_ = stack[3].m_obj;
lean_object* v___f_3589_ = stack[4].m_obj;
lean_object* v_inst_3590_ = stack[5].m_obj;
lean_object* v___f_3591_ = stack[6].m_obj;
lean_object* v_____do__lift_3592_ = stack[7].m_obj;
lean_object* v_res_3601_;
v_res_3601_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_3585_, v_inst_3586_, v_flag_3587_, v_toBind_3588_, v___f_3589_, v_inst_3590_, v___f_3591_, v_____do__lift_3592_);
stack->m_obj
 = v_res_3601_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object* v_toFunctor_3602_, lean_object* v_inst_3603_, lean_object* v_flag_3604_, lean_object* v_toBind_3605_, lean_object* v___f_3606_, lean_object* v_inst_3607_, lean_object* v___f_3608_, lean_object* v_____do__lift_3609_){
_start:
{
uint8_t v_flag_boxed_3610_; lean_object* v_res_3611_; 
v_flag_boxed_3610_ = lean_unbox(v_flag_3604_);
v_res_3611_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_3602_, v_inst_3603_, v_flag_boxed_3610_, v_toBind_3605_, v___f_3606_, v_inst_3607_, v___f_3608_, v_____do__lift_3609_);
lean_dec_ref(v_____do__lift_3609_);
return v_res_3611_;
}
}
lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object* v_inst_3613_, lean_object* v_inst_3614_, lean_object* v_inst_3615_, uint8_t v_flag_3616_, lean_object* v_x_3617_){
_start:
{
lean_object* v_toApplicative_3618_; lean_object* v_toBind_3619_; lean_object* v_getInfoState_3620_; lean_object* v_toFunctor_3621_; lean_object* v___f_3622_; lean_object* v___f_3623_; lean_object* v___x_3624_; lean_object* v___f_3625_; lean_object* v___x_3626_; 
v_toApplicative_3618_ = lean_ctor_get(v_inst_3613_, 0);
lean_inc_ref(v_toApplicative_3618_);
v_toBind_3619_ = lean_ctor_get(v_inst_3613_, 1);
lean_inc_n(v_toBind_3619_, 2);
lean_dec_ref(v_inst_3613_);
v_getInfoState_3620_ = lean_ctor_get(v_inst_3614_, 0);
lean_inc(v_getInfoState_3620_);
v_toFunctor_3621_ = lean_ctor_get(v_toApplicative_3618_, 0);
lean_inc_ref(v_toFunctor_3621_);
lean_dec_ref(v_toApplicative_3618_);
v___f_3622_ = ((lean_object*)(l_Lean_Elab_withEnableInfoTree___redArg___closed__0));
v___f_3623_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3623_, 0, v_x_3617_);
v___x_3624_ = lean_box(v_flag_3616_);
v___f_3625_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_3625_, 0, v_toFunctor_3621_);
lean_closure_set(v___f_3625_, 1, v_inst_3614_);
lean_closure_set(v___f_3625_, 2, v___x_3624_);
lean_closure_set(v___f_3625_, 3, v_toBind_3619_);
lean_closure_set(v___f_3625_, 4, v___f_3623_);
lean_closure_set(v___f_3625_, 5, v_inst_3615_);
lean_closure_set(v___f_3625_, 6, v___f_3622_);
v___x_3626_ = lean_apply_4(v_toBind_3619_, lean_box(0), lean_box(0), v_getInfoState_3620_, v___f_3625_);
return v___x_3626_;
}
}
LEAN_EXPORT void l_Lean_Elab_withEnableInfoTree___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3613_ = stack[0].m_obj;
lean_object* v_inst_3614_ = stack[1].m_obj;
lean_object* v_inst_3615_ = stack[2].m_obj;
uint8_t v_flag_3616_ = stack[3].m_num;
lean_object* v_x_3617_ = stack[4].m_obj;
lean_object* v_res_3627_;
v_res_3627_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3613_, v_inst_3614_, v_inst_3615_, v_flag_3616_, v_x_3617_);
stack->m_obj
 = v_res_3627_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object* v_inst_3628_, lean_object* v_inst_3629_, lean_object* v_inst_3630_, lean_object* v_flag_3631_, lean_object* v_x_3632_){
_start:
{
uint8_t v_flag_boxed_3633_; lean_object* v_res_3634_; 
v_flag_boxed_3633_ = lean_unbox(v_flag_3631_);
v_res_3634_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3628_, v_inst_3629_, v_inst_3630_, v_flag_boxed_3633_, v_x_3632_);
return v_res_3634_;
}
}
lean_object* l_Lean_Elab_withEnableInfoTree(lean_object* v_m_3635_, lean_object* v_00_u03b1_3636_, lean_object* v_inst_3637_, lean_object* v_inst_3638_, lean_object* v_inst_3639_, uint8_t v_flag_3640_, lean_object* v_x_3641_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3637_, v_inst_3638_, v_inst_3639_, v_flag_3640_, v_x_3641_);
return v___x_3642_;
}
}
LEAN_EXPORT void l_Lean_Elab_withEnableInfoTree_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3637_ = stack[2].m_obj;
lean_object* v_inst_3638_ = stack[3].m_obj;
lean_object* v_inst_3639_ = stack[4].m_obj;
uint8_t v_flag_3640_ = stack[5].m_num;
lean_object* v_x_3641_ = stack[6].m_obj;
lean_object* v_res_3643_;
v_res_3643_ = l_Lean_Elab_withEnableInfoTree(lean_box(0), lean_box(0), v_inst_3637_, v_inst_3638_, v_inst_3639_, v_flag_3640_, v_x_3641_);
stack->m_obj
 = v_res_3643_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object* v_m_3644_, lean_object* v_00_u03b1_3645_, lean_object* v_inst_3646_, lean_object* v_inst_3647_, lean_object* v_inst_3648_, lean_object* v_flag_3649_, lean_object* v_x_3650_){
_start:
{
uint8_t v_flag_boxed_3651_; lean_object* v_res_3652_; 
v_flag_boxed_3651_ = lean_unbox(v_flag_3649_);
v_res_3652_ = l_Lean_Elab_withEnableInfoTree(v_m_3644_, v_00_u03b1_3645_, v_inst_3646_, v_inst_3647_, v_inst_3648_, v_flag_boxed_3651_, v_x_3650_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object* v_toPure_3653_, lean_object* v_____do__lift_3654_){
_start:
{
lean_object* v_trees_3655_; lean_object* v___x_3656_; 
v_trees_3655_ = lean_ctor_get(v_____do__lift_3654_, 2);
lean_inc_ref(v_trees_3655_);
lean_dec_ref(v_____do__lift_3654_);
v___x_3656_ = lean_apply_2(v_toPure_3653_, lean_box(0), v_trees_3655_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object* v_inst_3657_, lean_object* v_inst_3658_){
_start:
{
lean_object* v_toApplicative_3659_; lean_object* v_toBind_3660_; lean_object* v_getInfoState_3661_; lean_object* v_toPure_3662_; lean_object* v___f_3663_; lean_object* v___x_3664_; 
v_toApplicative_3659_ = lean_ctor_get(v_inst_3658_, 0);
lean_inc_ref(v_toApplicative_3659_);
v_toBind_3660_ = lean_ctor_get(v_inst_3658_, 1);
lean_inc(v_toBind_3660_);
lean_dec_ref(v_inst_3658_);
v_getInfoState_3661_ = lean_ctor_get(v_inst_3657_, 0);
lean_inc(v_getInfoState_3661_);
lean_dec_ref(v_inst_3657_);
v_toPure_3662_ = lean_ctor_get(v_toApplicative_3659_, 1);
lean_inc(v_toPure_3662_);
lean_dec_ref(v_toApplicative_3659_);
v___f_3663_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3663_, 0, v_toPure_3662_);
v___x_3664_ = lean_apply_4(v_toBind_3660_, lean_box(0), lean_box(0), v_getInfoState_3661_, v___f_3663_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object* v_m_3665_, lean_object* v_inst_3666_, lean_object* v_inst_3667_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_3666_, v_inst_3667_);
return v___x_3668_;
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
