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
lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v_a_727_; lean_object* v___y_737_; uint8_t v___y_738_; lean_object* v___y_741_; lean_object* v_a_742_; lean_object* v___x_745_; 
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
lean_inc_ref(v_expr_705_);
v___x_745_ = lean_infer_type(v_expr_705_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v___x_747_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
lean_dec_ref_known(v___x_745_, 1);
v___x_747_ = l_Lean_Meta_ppExpr(v_a_746_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
v_a_727_ = v_a_748_;
goto v___jp_726_;
}
else
{
lean_object* v_a_749_; 
v_a_749_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_749_);
v___y_741_ = v___x_747_;
v_a_742_ = v_a_749_;
goto v___jp_740_;
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
v___y_741_ = v___x_755_;
v_a_742_ = v_a_750_;
goto v___jp_740_;
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
lean_ctor_set(v___x_717_, 0, v___y_714_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v___y_713_);
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
v___y_713_ = v_a_727_;
v___y_714_ = v___x_733_;
v___y_715_ = v___x_734_;
goto v___jp_712_;
}
else
{
lean_object* v___x_735_; 
v___x_735_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__7));
v___y_713_ = v_a_727_;
v___y_714_ = v___x_733_;
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
if (v___y_738_ == 0)
{
lean_object* v___x_739_; 
lean_dec_ref(v___y_737_);
v___x_739_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__9));
v_a_727_ = v___x_739_;
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
v___jp_740_:
{
uint8_t v___x_743_; 
v___x_743_ = l_Lean_Exception_isInterrupt(v_a_742_);
if (v___x_743_ == 0)
{
uint8_t v___x_744_; 
v___x_744_ = l_Lean_Exception_isRuntime(v_a_742_);
v___y_737_ = v___y_741_;
v___y_738_ = v___x_744_;
goto v___jp_736_;
}
else
{
lean_dec_ref(v_a_742_);
v___y_737_ = v___y_741_;
v___y_738_ = v___x_743_;
goto v___jp_736_;
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17));
v___x_2218_ = l_Lean_stringToMessageData(v___x_2217_);
return v___x_2218_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__20(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__19));
v___x_2221_ = l_Lean_stringToMessageData(v___x_2220_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__22(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__21));
v___x_2224_ = l_Lean_stringToMessageData(v___x_2223_);
return v___x_2224_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__24(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__23));
v___x_2227_ = l_Lean_stringToMessageData(v___x_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_2228_, lean_object* v_declHint_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v_env_2234_; uint8_t v___x_2235_; 
v___x_2232_ = lean_box(0);
v___x_2233_ = lean_st_ref_get(v___y_2230_);
v_env_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc_ref(v_env_2234_);
lean_dec(v___x_2233_);
v___x_2235_ = l_Lean_Name_isAnonymous(v_declHint_2229_);
if (v___x_2235_ == 0)
{
uint8_t v_isExporting_2236_; 
v_isExporting_2236_ = lean_ctor_get_uint8(v_env_2234_, sizeof(void*)*13);
if (v_isExporting_2236_ == 0)
{
lean_object* v___x_2237_; 
lean_dec_ref(v_env_2234_);
lean_dec(v_declHint_2229_);
v___x_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2237_, 0, v_msg_2228_);
return v___x_2237_;
}
else
{
lean_object* v___x_2238_; uint8_t v___x_2239_; 
lean_inc_ref(v_env_2234_);
v___x_2238_ = l_Lean_Environment_setExporting(v_env_2234_, v___x_2235_);
lean_inc(v_declHint_2229_);
lean_inc_ref(v___x_2238_);
v___x_2239_ = l_Lean_Environment_contains(v___x_2238_, v_declHint_2229_, v_isExporting_2236_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; 
lean_dec_ref(v___x_2238_);
lean_dec_ref(v_env_2234_);
lean_dec(v_declHint_2229_);
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v_msg_2228_);
return v___x_2240_;
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v_c_2246_; lean_object* v___x_2247_; 
v___x_2241_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2242_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_2243_ = l_Lean_Options_empty;
v___x_2244_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2238_);
lean_ctor_set(v___x_2244_, 1, v___x_2241_);
lean_ctor_set(v___x_2244_, 2, v___x_2242_);
lean_ctor_set(v___x_2244_, 3, v___x_2243_);
lean_inc(v_declHint_2229_);
v___x_2245_ = l_Lean_MessageData_ofConstName(v_declHint_2229_, v___x_2235_);
v_c_2246_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2246_, 0, v___x_2244_);
lean_ctor_set(v_c_2246_, 1, v___x_2245_);
v___x_2247_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2234_, v_declHint_2229_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
lean_dec_ref(v_env_2234_);
lean_dec(v_declHint_2229_);
v___x_2248_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
lean_ctor_set(v___x_2249_, 1, v_c_2246_);
v___x_2250_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6);
v___x_2251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2249_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
v___x_2252_ = l_Lean_MessageData_note(v___x_2251_);
v___x_2253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2253_, 0, v_msg_2228_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
return v___x_2254_;
}
else
{
lean_object* v_val_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2311_; 
v_val_2255_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2257_ = v___x_2247_;
v_isShared_2258_ = v_isSharedCheck_2311_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_val_2255_);
lean_dec(v___x_2247_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2311_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2259_; lean_object* v_modules_2260_; lean_object* v_moduleNames_2261_; lean_object* v_mod_2262_; uint8_t v___y_2264_; uint8_t v___x_2294_; 
v___x_2259_ = l_Lean_Environment_header(v_env_2234_);
lean_dec_ref(v_env_2234_);
v_modules_2260_ = lean_ctor_get(v___x_2259_, 3);
lean_inc_ref(v_modules_2260_);
v_moduleNames_2261_ = lean_ctor_get(v___x_2259_, 4);
lean_inc_ref(v_moduleNames_2261_);
lean_dec_ref(v___x_2259_);
v_mod_2262_ = lean_array_get(v___x_2232_, v_moduleNames_2261_, v_val_2255_);
lean_dec_ref(v_moduleNames_2261_);
v___x_2294_ = l_Lean_isPrivateName(v_declHint_2229_);
lean_dec(v_declHint_2229_);
if (v___x_2294_ == 0)
{
lean_object* v___x_2295_; uint8_t v___x_2296_; 
v___x_2295_ = lean_array_get_size(v_modules_2260_);
v___x_2296_ = lean_nat_dec_lt(v_val_2255_, v___x_2295_);
if (v___x_2296_ == 0)
{
lean_dec_ref(v_modules_2260_);
lean_dec(v_val_2255_);
v___y_2264_ = v___x_2294_;
goto v___jp_2263_;
}
else
{
lean_object* v___x_2297_; lean_object* v_toImport_2298_; uint8_t v_isExported_2299_; 
v___x_2297_ = lean_array_fget(v_modules_2260_, v_val_2255_);
lean_dec(v_val_2255_);
lean_dec_ref(v_modules_2260_);
v_toImport_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc_ref(v_toImport_2298_);
lean_dec(v___x_2297_);
v_isExported_2299_ = lean_ctor_get_uint8(v_toImport_2298_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2298_);
v___y_2264_ = v_isExported_2299_;
goto v___jp_2263_;
}
}
else
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
lean_dec_ref(v_modules_2260_);
lean_del_object(v___x_2257_);
lean_dec(v_val_2255_);
v___x_2300_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
lean_ctor_set(v___x_2301_, 1, v_c_2246_);
v___x_2302_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__22);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = l_Lean_MessageData_ofName(v_mod_2262_);
v___x_2305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2303_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__24);
v___x_2307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2305_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = l_Lean_MessageData_note(v___x_2307_);
v___x_2309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2309_, 0, v_msg_2228_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
v___x_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
return v___x_2310_;
}
v___jp_2263_:
{
if (v___y_2264_ == 0)
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2265_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8);
v___x_2266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
lean_ctor_set(v___x_2266_, 1, v_c_2246_);
v___x_2267_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10);
v___x_2268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2266_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
v___x_2269_ = l_Lean_MessageData_ofName(v_mod_2262_);
v___x_2270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12);
v___x_2272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2270_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
v___x_2273_ = l_Lean_MessageData_note(v___x_2272_);
v___x_2274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2274_, 0, v_msg_2228_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
if (v_isShared_2258_ == 0)
{
lean_ctor_set_tag(v___x_2257_, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2274_);
v___x_2276_ = v___x_2257_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
else
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2292_; 
v___x_2278_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14);
v___x_2279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
lean_ctor_set(v___x_2279_, 1, v_c_2246_);
v___x_2280_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16);
v___x_2281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2279_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = l_Lean_MessageData_ofName(v_mod_2262_);
lean_inc_ref(v___x_2282_);
v___x_2283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2281_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__18);
v___x_2285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2283_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
lean_ctor_set(v___x_2286_, 1, v___x_2282_);
v___x_2287_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__20);
v___x_2288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2286_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = l_Lean_MessageData_note(v___x_2288_);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v_msg_2228_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
if (v_isShared_2258_ == 0)
{
lean_ctor_set_tag(v___x_2257_, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2290_);
v___x_2292_ = v___x_2257_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2290_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
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
lean_object* v___x_2312_; 
lean_dec_ref(v_env_2234_);
lean_dec(v_declHint_2229_);
v___x_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2312_, 0, v_msg_2228_);
return v___x_2312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_2313_, lean_object* v_declHint_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2313_, v_declHint_2314_, v___y_2315_);
lean_dec(v___y_2315_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_2318_, lean_object* v_declHint_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v___x_2323_; lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2333_; 
v___x_2323_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2318_, v_declHint_2319_, v___y_2321_);
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2326_ = v___x_2323_;
v_isShared_2327_ = v_isSharedCheck_2333_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2333_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2328_ = l_Lean_unknownIdentifierMessageTag;
v___x_2329_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
lean_ctor_set(v___x_2329_, 1, v_a_2324_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2329_);
v___x_2331_ = v___x_2326_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_2334_, lean_object* v_declHint_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2334_, v_declHint_2335_, v___y_2336_, v___y_2337_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object* v_msgData_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v___x_2344_; lean_object* v_toCold_2345_; lean_object* v_env_2346_; lean_object* v_options_2347_; uint8_t v___x_2348_; lean_object* v_env_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2344_ = lean_st_ref_get(v___y_2342_);
v_toCold_2345_ = lean_ctor_get(v___y_2341_, 0);
v_env_2346_ = lean_ctor_get(v___x_2344_, 0);
lean_inc_ref(v_env_2346_);
lean_dec(v___x_2344_);
v_options_2347_ = lean_ctor_get(v_toCold_2345_, 2);
v___x_2348_ = 0;
v_env_2349_ = l_Lean_Environment_setRecordingDeps(v_env_2346_, v___x_2348_);
v___x_2350_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2351_ = lean_unsigned_to_nat(32u);
v___x_2352_ = lean_mk_empty_array_with_capacity(v___x_2351_);
lean_dec_ref(v___x_2352_);
v___x_2353_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
lean_inc_ref(v_options_2347_);
v___x_2354_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2354_, 0, v_env_2349_);
lean_ctor_set(v___x_2354_, 1, v___x_2350_);
lean_ctor_set(v___x_2354_, 2, v___x_2353_);
lean_ctor_set(v___x_2354_, 3, v_options_2347_);
v___x_2355_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
lean_ctor_set(v___x_2355_, 1, v_msgData_2340_);
v___x_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object* v_msgData_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_2357_, v___y_2358_, v___y_2359_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_ref_2366_; lean_object* v___x_2367_; lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2376_; 
v_ref_2366_ = lean_ctor_get(v___y_2363_, 2);
v___x_2367_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_2362_, v___y_2363_, v___y_2364_);
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2370_ = v___x_2367_;
v_isShared_2371_ = v_isSharedCheck_2376_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2367_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2376_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; lean_object* v___x_2374_; 
lean_inc(v_ref_2366_);
v___x_2372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2372_, 0, v_ref_2366_);
lean_ctor_set(v___x_2372_, 1, v_a_2368_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set_tag(v___x_2370_, 1);
lean_ctor_set(v___x_2370_, 0, v___x_2372_);
v___x_2374_ = v___x_2370_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_2382_, lean_object* v_msg_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_toCold_2387_; lean_object* v_currRecDepth_2388_; lean_object* v_ref_2389_; uint16_t v_optionFlags_2390_; uint8_t v_suppressElabErrors_2391_; uint8_t v_isRecordingDeps_2392_; lean_object* v_ref_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v_toCold_2387_ = lean_ctor_get(v___y_2384_, 0);
v_currRecDepth_2388_ = lean_ctor_get(v___y_2384_, 1);
v_ref_2389_ = lean_ctor_get(v___y_2384_, 2);
v_optionFlags_2390_ = lean_ctor_get_uint16(v___y_2384_, sizeof(void*)*3);
v_suppressElabErrors_2391_ = lean_ctor_get_uint8(v___y_2384_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2392_ = lean_ctor_get_uint8(v___y_2384_, sizeof(void*)*3 + 3);
v_ref_2393_ = l_Lean_replaceRef(v_ref_2382_, v_ref_2389_);
lean_inc(v_currRecDepth_2388_);
lean_inc_ref(v_toCold_2387_);
v___x_2394_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2394_, 0, v_toCold_2387_);
lean_ctor_set(v___x_2394_, 1, v_currRecDepth_2388_);
lean_ctor_set(v___x_2394_, 2, v_ref_2393_);
lean_ctor_set_uint16(v___x_2394_, sizeof(void*)*3, v_optionFlags_2390_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*3 + 2, v_suppressElabErrors_2391_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*3 + 3, v_isRecordingDeps_2392_);
v___x_2395_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2383_, v___x_2394_, v___y_2385_);
lean_dec_ref_known(v___x_2394_, 3);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_2396_, lean_object* v_msg_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2396_, v_msg_2397_, v___y_2398_, v___y_2399_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v_ref_2396_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_2402_, lean_object* v_msg_2403_, lean_object* v_declHint_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v___x_2408_; lean_object* v_a_2409_; lean_object* v___x_2410_; 
v___x_2408_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2403_, v_declHint_2404_, v___y_2405_, v___y_2406_);
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2409_);
lean_dec_ref(v___x_2408_);
v___x_2410_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2402_, v_a_2409_, v___y_2405_, v___y_2406_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2411_, lean_object* v_msg_2412_, lean_object* v_declHint_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2411_, v_msg_2412_, v_declHint_2413_, v___y_2414_, v___y_2415_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v_ref_2411_);
return v_res_2417_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_2420_ = l_Lean_stringToMessageData(v___x_2419_);
return v___x_2420_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2));
v___x_2423_ = l_Lean_stringToMessageData(v___x_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_2424_, lean_object* v_constName_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v___x_2429_; uint8_t v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2429_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_2430_ = 0;
lean_inc(v_constName_2425_);
v___x_2431_ = l_Lean_MessageData_ofConstName(v_constName_2425_, v___x_2430_);
v___x_2432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2429_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
v___x_2433_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_2434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2432_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2424_, v___x_2434_, v_constName_2425_, v___y_2426_, v___y_2427_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2436_, lean_object* v_constName_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2436_, v_constName_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v_ref_2436_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v_ref_2446_; lean_object* v___x_2447_; 
v_ref_2446_ = lean_ctor_get(v___y_2443_, 2);
v___x_2447_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2446_, v_constName_2442_, v___y_2443_, v___y_2444_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object* v_constName_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v___x_2457_; lean_object* v_env_2458_; uint8_t v___x_2459_; lean_object* v___x_2460_; 
v___x_2457_ = lean_st_ref_get(v___y_2455_);
v_env_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc_ref(v_env_2458_);
lean_dec(v___x_2457_);
v___x_2459_ = 0;
lean_inc(v_constName_2453_);
v___x_2460_ = l_Lean_Environment_findConstVal_x3f(v_env_2458_, v_constName_2453_, v___x_2459_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2453_, v___y_2454_, v___y_2455_);
return v___x_2461_;
}
else
{
lean_object* v_val_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec(v_constName_2453_);
v_val_2462_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2460_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_val_2462_);
lean_dec(v___x_2460_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
lean_ctor_set_tag(v___x_2464_, 0);
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_val_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2470_, v___y_2471_, v___y_2472_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
if (lean_obj_tag(v_a_2475_) == 0)
{
lean_object* v___x_2477_; 
v___x_2477_ = l_List_reverse___redArg(v_a_2476_);
return v___x_2477_;
}
else
{
lean_object* v_head_2478_; lean_object* v_tail_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2488_; 
v_head_2478_ = lean_ctor_get(v_a_2475_, 0);
v_tail_2479_ = lean_ctor_get(v_a_2475_, 1);
v_isSharedCheck_2488_ = !lean_is_exclusive(v_a_2475_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2481_ = v_a_2475_;
v_isShared_2482_ = v_isSharedCheck_2488_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_tail_2479_);
lean_inc(v_head_2478_);
lean_dec(v_a_2475_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2488_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2483_; lean_object* v___x_2485_; 
v___x_2483_ = l_Lean_mkLevelParam(v_head_2478_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 1, v_a_2476_);
lean_ctor_set(v___x_2481_, 0, v___x_2483_);
v___x_2485_ = v___x_2481_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v_a_2476_);
v___x_2485_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
v_a_2475_ = v_tail_2479_;
v_a_2476_ = v___x_2485_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object* v_constName_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v___x_2493_; 
lean_inc(v_constName_2489_);
v___x_2493_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2489_, v___y_2490_, v___y_2491_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2505_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2496_ = v___x_2493_;
v_isShared_2497_ = v_isSharedCheck_2505_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2493_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2505_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v_levelParams_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2503_; 
v_levelParams_2498_ = lean_ctor_get(v_a_2494_, 1);
lean_inc(v_levelParams_2498_);
lean_dec(v_a_2494_);
v___x_2499_ = lean_box(0);
v___x_2500_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_2498_, v___x_2499_);
v___x_2501_ = l_Lean_mkConst(v_constName_2489_, v___x_2500_);
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 0, v___x_2501_);
v___x_2503_ = v___x_2496_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2501_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v_constName_2489_);
v_a_2506_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2493_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2493_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object* v_constName_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_2514_, v___y_2515_, v___y_2516_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object* v_stx_2519_, lean_object* v_n_2520_, lean_object* v_expectedType_x3f_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v___x_2525_; 
v___x_2525_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_2520_, v___y_2522_, v___y_2523_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2525_, 1);
v___x_2527_ = lean_box(0);
v___x_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
lean_ctor_set(v___x_2528_, 1, v_stx_2519_);
v___x_2529_ = l_Lean_LocalContext_empty;
v___x_2530_ = 0;
v___x_2531_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2531_, 0, v___x_2528_);
lean_ctor_set(v___x_2531_, 1, v___x_2529_);
lean_ctor_set(v___x_2531_, 2, v_expectedType_x3f_2521_);
lean_ctor_set(v___x_2531_, 3, v_a_2526_);
lean_ctor_set_uint8(v___x_2531_, sizeof(void*)*4, v___x_2530_);
lean_ctor_set_uint8(v___x_2531_, sizeof(void*)*4 + 1, v___x_2530_);
v___x_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
v___x_2533_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_2532_, v___y_2522_, v___y_2523_);
return v___x_2533_;
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_dec(v_expectedType_x3f_2521_);
lean_dec(v_stx_2519_);
v_a_2534_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2525_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2525_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object* v_stx_2542_, lean_object* v_n_2543_, lean_object* v_expectedType_x3f_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_2542_, v_n_2543_, v_expectedType_x3f_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object* v_id_2549_, lean_object* v_expectedType_x3f_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v___x_2554_; 
lean_inc(v_id_2549_);
v___x_2554_ = l_Lean_realizeGlobalConstNoOverload(v_id_2549_, v_a_2551_, v_a_2552_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2582_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2582_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2582_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2559_; lean_object* v_infoState_2560_; uint8_t v_enabled_2561_; 
v___x_2559_ = lean_st_ref_get(v_a_2552_);
v_infoState_2560_ = lean_ctor_get(v___x_2559_, 8);
lean_inc_ref(v_infoState_2560_);
lean_dec(v___x_2559_);
v_enabled_2561_ = lean_ctor_get_uint8(v_infoState_2560_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2560_);
if (v_enabled_2561_ == 0)
{
lean_object* v___x_2563_; 
lean_dec(v_expectedType_x3f_2550_);
lean_dec(v_id_2549_);
if (v_isShared_2558_ == 0)
{
v___x_2563_ = v___x_2557_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2555_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
else
{
lean_object* v___x_2565_; 
lean_del_object(v___x_2557_);
lean_inc(v_a_2555_);
v___x_2565_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2549_, v_a_2555_, v_expectedType_x3f_2550_, v_a_2551_, v_a_2552_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2572_ == 0)
{
lean_object* v_unused_2573_; 
v_unused_2573_ = lean_ctor_get(v___x_2565_, 0);
lean_dec(v_unused_2573_);
v___x_2567_ = v___x_2565_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_dec(v___x_2565_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v_a_2555_);
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2555_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec(v_a_2555_);
v_a_2574_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2565_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2565_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2550_);
lean_dec(v_id_2549_);
return v___x_2554_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object* v_id_2583_, lean_object* v_expectedType_x3f_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_2583_, v_expectedType_x3f_2584_, v_a_2585_, v_a_2586_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object* v_t_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2589_, v___y_2591_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_2594_, v___y_2595_, v___y_2596_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2599_, lean_object* v_constName_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v___x_2604_; 
v___x_2604_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2600_, v___y_2601_, v___y_2602_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2605_, lean_object* v_constName_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2605_, v_constName_2606_, v___y_2607_, v___y_2608_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2611_, lean_object* v_ref_2612_, lean_object* v_constName_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2612_, v_constName_2613_, v___y_2614_, v___y_2615_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2618_, lean_object* v_ref_2619_, lean_object* v_constName_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_2618_, v_ref_2619_, v_constName_2620_, v___y_2621_, v___y_2622_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v_ref_2619_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2625_, lean_object* v_ref_2626_, lean_object* v_msg_2627_, lean_object* v_declHint_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2626_, v_msg_2627_, v_declHint_2628_, v___y_2629_, v___y_2630_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2633_, lean_object* v_ref_2634_, lean_object* v_msg_2635_, lean_object* v_declHint_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_2633_, v_ref_2634_, v_msg_2635_, v_declHint_2636_, v___y_2637_, v___y_2638_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v_ref_2634_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_2641_, lean_object* v_declHint_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2641_, v_declHint_2642_, v___y_2644_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2647_, lean_object* v_declHint_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2647_, v_declHint_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_2653_, lean_object* v_ref_2654_, lean_object* v_msg_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2654_, v_msg_2655_, v___y_2656_, v___y_2657_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2660_, lean_object* v_ref_2661_, lean_object* v_msg_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_2660_, v_ref_2661_, v_msg_2662_, v___y_2663_, v___y_2664_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v_ref_2661_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_2667_, lean_object* v_msg_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2668_, v___y_2669_, v___y_2670_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_2673_, lean_object* v_msg_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_2673_, v_msg_2674_, v___y_2675_, v___y_2676_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object* v_id_2679_, lean_object* v_expectedType_x3f_2680_, lean_object* v_as_x27_2681_, lean_object* v_b_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
if (lean_obj_tag(v_as_x27_2681_) == 0)
{
lean_object* v___x_2686_; 
lean_dec(v_expectedType_x3f_2680_);
lean_dec(v_id_2679_);
v___x_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2686_, 0, v_b_2682_);
return v___x_2686_;
}
else
{
lean_object* v_head_2687_; lean_object* v_tail_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_head_2687_ = lean_ctor_get(v_as_x27_2681_, 0);
v_tail_2688_ = lean_ctor_get(v_as_x27_2681_, 1);
v___x_2689_ = lean_box(0);
lean_inc(v_expectedType_x3f_2680_);
lean_inc(v_head_2687_);
lean_inc(v_id_2679_);
v___x_2690_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2679_, v_head_2687_, v_expectedType_x3f_2680_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_dec_ref_known(v___x_2690_, 1);
v_as_x27_2681_ = v_tail_2688_;
v_b_2682_ = v___x_2689_;
goto _start;
}
else
{
lean_dec(v_expectedType_x3f_2680_);
lean_dec(v_id_2679_);
return v___x_2690_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object* v_id_2692_, lean_object* v_expectedType_x3f_2693_, lean_object* v_as_x27_2694_, lean_object* v_b_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2692_, v_expectedType_x3f_2693_, v_as_x27_2694_, v_b_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v_as_x27_2694_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object* v_id_2700_, lean_object* v_expectedType_x3f_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_){
_start:
{
lean_object* v___x_2705_; 
lean_inc(v_id_2700_);
v___x_2705_ = l_Lean_realizeGlobalConst(v_id_2700_, v_a_2702_, v_a_2703_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2734_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2708_ = v___x_2705_;
v_isShared_2709_ = v_isSharedCheck_2734_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2705_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2734_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2710_; lean_object* v_infoState_2711_; uint8_t v_enabled_2712_; 
v___x_2710_ = lean_st_ref_get(v_a_2703_);
v_infoState_2711_ = lean_ctor_get(v___x_2710_, 8);
lean_inc_ref(v_infoState_2711_);
lean_dec(v___x_2710_);
v_enabled_2712_ = lean_ctor_get_uint8(v_infoState_2711_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2711_);
if (v_enabled_2712_ == 0)
{
lean_object* v___x_2714_; 
lean_dec(v_expectedType_x3f_2701_);
lean_dec(v_id_2700_);
if (v_isShared_2709_ == 0)
{
v___x_2714_ = v___x_2708_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2706_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
else
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
lean_del_object(v___x_2708_);
v___x_2716_ = lean_box(0);
v___x_2717_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2700_, v_expectedType_x3f_2701_, v_a_2706_, v___x_2716_, v_a_2702_, v_a_2703_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2724_ == 0)
{
lean_object* v_unused_2725_; 
v_unused_2725_ = lean_ctor_get(v___x_2717_, 0);
lean_dec(v_unused_2725_);
v___x_2719_ = v___x_2717_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_dec(v___x_2717_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v_a_2706_);
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2706_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec(v_a_2706_);
v_a_2726_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2717_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2717_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2701_);
lean_dec(v_id_2700_);
return v___x_2705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object* v_id_2735_, lean_object* v_expectedType_x3f_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_2735_, v_expectedType_x3f_2736_, v_a_2737_, v_a_2738_);
lean_dec(v_a_2738_);
lean_dec_ref(v_a_2737_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object* v_id_2741_, lean_object* v_expectedType_x3f_2742_, lean_object* v_as_2743_, lean_object* v_as_x27_2744_, lean_object* v_b_2745_, lean_object* v_a_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2741_, v_expectedType_x3f_2742_, v_as_x27_2744_, v_b_2745_, v___y_2747_, v___y_2748_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object* v_id_2751_, lean_object* v_expectedType_x3f_2752_, lean_object* v_as_2753_, lean_object* v_as_x27_2754_, lean_object* v_b_2755_, lean_object* v_a_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_2751_, v_expectedType_x3f_2752_, v_as_2753_, v_as_x27_2754_, v_b_2755_, v_a_2756_, v___y_2757_, v___y_2758_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v_as_x27_2754_);
lean_dec(v_as_2753_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object* v_ref_2761_, lean_object* v_as_x27_2762_, lean_object* v_b_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
if (lean_obj_tag(v_as_x27_2762_) == 0)
{
lean_object* v___x_2767_; 
lean_dec(v_ref_2761_);
v___x_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2767_, 0, v_b_2763_);
return v___x_2767_;
}
else
{
lean_object* v_head_2768_; lean_object* v_tail_2769_; lean_object* v_fst_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v_head_2768_ = lean_ctor_get(v_as_x27_2762_, 0);
v_tail_2769_ = lean_ctor_get(v_as_x27_2762_, 1);
v_fst_2770_ = lean_ctor_get(v_head_2768_, 0);
v___x_2771_ = lean_box(0);
v___x_2772_ = lean_box(0);
lean_inc(v_fst_2770_);
lean_inc(v_ref_2761_);
v___x_2773_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_2761_, v_fst_2770_, v___x_2772_, v___y_2764_, v___y_2765_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_dec_ref_known(v___x_2773_, 1);
v_as_x27_2762_ = v_tail_2769_;
v_b_2763_ = v___x_2771_;
goto _start;
}
else
{
lean_dec(v_ref_2761_);
return v___x_2773_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object* v_ref_2775_, lean_object* v_as_x27_2776_, lean_object* v_b_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2775_, v_as_x27_2776_, v_b_2777_, v___y_2778_, v___y_2779_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v_as_x27_2776_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object* v_ref_2782_, lean_object* v_id_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v___x_2787_; 
v___x_2787_ = l_Lean_realizeGlobalName(v_id_2783_, v_a_2784_, v_a_2785_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2816_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2790_ = v___x_2787_;
v_isShared_2791_ = v_isSharedCheck_2816_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2787_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2816_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2792_; lean_object* v_infoState_2793_; uint8_t v_enabled_2794_; 
v___x_2792_ = lean_st_ref_get(v_a_2785_);
v_infoState_2793_ = lean_ctor_get(v___x_2792_, 8);
lean_inc_ref(v_infoState_2793_);
lean_dec(v___x_2792_);
v_enabled_2794_ = lean_ctor_get_uint8(v_infoState_2793_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2793_);
if (v_enabled_2794_ == 0)
{
lean_object* v___x_2796_; 
lean_dec(v_ref_2782_);
if (v_isShared_2791_ == 0)
{
v___x_2796_ = v___x_2790_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2788_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
else
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
lean_del_object(v___x_2790_);
v___x_2798_ = lean_box(0);
v___x_2799_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2782_, v_a_2788_, v___x_2798_, v_a_2784_, v_a_2785_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2806_ == 0)
{
lean_object* v_unused_2807_; 
v_unused_2807_ = lean_ctor_get(v___x_2799_, 0);
lean_dec(v_unused_2807_);
v___x_2801_ = v___x_2799_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_dec(v___x_2799_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 0, v_a_2788_);
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2788_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec(v_a_2788_);
v_a_2808_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2799_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2799_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
}
}
else
{
lean_dec(v_ref_2782_);
return v___x_2787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object* v_ref_2817_, lean_object* v_id_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_2817_, v_id_2818_, v_a_2819_, v_a_2820_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object* v_ref_2823_, lean_object* v_as_2824_, lean_object* v_as_x27_2825_, lean_object* v_b_2826_, lean_object* v_a_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2823_, v_as_x27_2825_, v_b_2826_, v___y_2828_, v___y_2829_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object* v_ref_2832_, lean_object* v_as_2833_, lean_object* v_as_x27_2834_, lean_object* v_b_2835_, lean_object* v_a_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_2832_, v_as_2833_, v_as_x27_2834_, v_b_2835_, v_a_2836_, v___y_2837_, v___y_2838_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v_as_x27_2834_);
lean_dec(v_as_2833_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object* v_self_2841_){
_start:
{
lean_object* v_fst_2842_; 
v_fst_2842_ = lean_ctor_get(v_self_2841_, 0);
lean_inc(v_fst_2842_);
return v_fst_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object* v_self_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_2843_);
lean_dec_ref(v_self_2843_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object* v_info_2845_, lean_object* v_treesSaved_2846_, lean_object* v_s_2847_){
_start:
{
if (lean_obj_tag(v_info_2845_) == 0)
{
uint8_t v_enabled_2848_; lean_object* v_assignment_2849_; lean_object* v_lazyAssignment_2850_; lean_object* v_trees_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2861_; 
v_enabled_2848_ = lean_ctor_get_uint8(v_s_2847_, sizeof(void*)*3);
v_assignment_2849_ = lean_ctor_get(v_s_2847_, 0);
v_lazyAssignment_2850_ = lean_ctor_get(v_s_2847_, 1);
v_trees_2851_ = lean_ctor_get(v_s_2847_, 2);
v_isSharedCheck_2861_ = !lean_is_exclusive(v_s_2847_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2853_ = v_s_2847_;
v_isShared_2854_ = v_isSharedCheck_2861_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_trees_2851_);
lean_inc(v_lazyAssignment_2850_);
lean_inc(v_assignment_2849_);
lean_dec(v_s_2847_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2861_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v_val_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2859_; 
v_val_2855_ = lean_ctor_get(v_info_2845_, 0);
lean_inc(v_val_2855_);
lean_dec_ref_known(v_info_2845_, 1);
v___x_2856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2856_, 0, v_val_2855_);
lean_ctor_set(v___x_2856_, 1, v_trees_2851_);
v___x_2857_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2846_, v___x_2856_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 2, v___x_2857_);
v___x_2859_ = v___x_2853_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_assignment_2849_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v_lazyAssignment_2850_);
lean_ctor_set(v_reuseFailAlloc_2860_, 2, v___x_2857_);
lean_ctor_set_uint8(v_reuseFailAlloc_2860_, sizeof(void*)*3, v_enabled_2848_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
else
{
uint8_t v_enabled_2862_; lean_object* v_assignment_2863_; lean_object* v_lazyAssignment_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2880_; 
v_enabled_2862_ = lean_ctor_get_uint8(v_s_2847_, sizeof(void*)*3);
v_assignment_2863_ = lean_ctor_get(v_s_2847_, 0);
v_lazyAssignment_2864_ = lean_ctor_get(v_s_2847_, 1);
v_isSharedCheck_2880_ = !lean_is_exclusive(v_s_2847_);
if (v_isSharedCheck_2880_ == 0)
{
lean_object* v_unused_2881_; 
v_unused_2881_ = lean_ctor_get(v_s_2847_, 2);
lean_dec(v_unused_2881_);
v___x_2866_ = v_s_2847_;
v_isShared_2867_ = v_isSharedCheck_2880_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_lazyAssignment_2864_);
lean_inc(v_assignment_2863_);
lean_dec(v_s_2847_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2880_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v_val_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2879_; 
v_val_2868_ = lean_ctor_get(v_info_2845_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v_info_2845_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2870_ = v_info_2845_;
v_isShared_2871_ = v_isSharedCheck_2879_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_val_2868_);
lean_dec(v_info_2845_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2879_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
lean_ctor_set_tag(v___x_2870_, 2);
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_val_2868_);
v___x_2873_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2874_; lean_object* v___x_2876_; 
v___x_2874_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2846_, v___x_2873_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 2, v___x_2874_);
v___x_2876_ = v___x_2866_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_assignment_2863_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_lazyAssignment_2864_);
lean_ctor_set(v_reuseFailAlloc_2877_, 2, v___x_2874_);
lean_ctor_set_uint8(v_reuseFailAlloc_2877_, sizeof(void*)*3, v_enabled_2862_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object* v_treesSaved_2882_, lean_object* v_modifyInfoState_2883_, lean_object* v_info_2884_){
_start:
{
lean_object* v___f_2885_; lean_object* v___x_2886_; 
v___f_2885_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2885_, 0, v_info_2884_);
lean_closure_set(v___f_2885_, 1, v_treesSaved_2882_);
v___x_2886_ = lean_apply_1(v_modifyInfoState_2883_, v___f_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object* v___f_2887_, lean_object* v_info_2888_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = lean_apply_1(v___f_2887_, v_info_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object* v_toPure_2890_, lean_object* v_toBind_2891_, lean_object* v___f_2892_, lean_object* v_____do__lift_2893_){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2894_, 0, v_____do__lift_2893_);
v___x_2895_ = lean_apply_2(v_toPure_2890_, lean_box(0), v___x_2894_);
v___x_2896_ = lean_apply_4(v_toBind_2891_, lean_box(0), lean_box(0), v___x_2895_, v___f_2892_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object* v_toBind_2897_, lean_object* v_mkInfoOnError_2898_, lean_object* v___f_2899_, lean_object* v_mkInfo_2900_, lean_object* v___f_2901_, lean_object* v_a_x3f_2902_){
_start:
{
if (lean_obj_tag(v_a_x3f_2902_) == 0)
{
lean_object* v___x_2903_; 
lean_dec(v___f_2901_);
lean_dec(v_mkInfo_2900_);
v___x_2903_ = lean_apply_4(v_toBind_2897_, lean_box(0), lean_box(0), v_mkInfoOnError_2898_, v___f_2899_);
return v___x_2903_;
}
else
{
lean_object* v_val_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
lean_dec(v___f_2899_);
lean_dec(v_mkInfoOnError_2898_);
v_val_2904_ = lean_ctor_get(v_a_x3f_2902_, 0);
lean_inc(v_val_2904_);
lean_dec_ref_known(v_a_x3f_2902_, 1);
v___x_2905_ = lean_apply_1(v_mkInfo_2900_, v_val_2904_);
v___x_2906_ = lean_apply_4(v_toBind_2897_, lean_box(0), lean_box(0), v___x_2905_, v___f_2901_);
return v___x_2906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object* v_toFunctor_2907_, lean_object* v_modifyInfoState_2908_, lean_object* v_toPure_2909_, lean_object* v_toBind_2910_, lean_object* v_mkInfoOnError_2911_, lean_object* v_mkInfo_2912_, lean_object* v_inst_2913_, lean_object* v_x_2914_, lean_object* v___f_2915_, lean_object* v_treesSaved_2916_){
_start:
{
lean_object* v_map_2917_; lean_object* v___f_2918_; lean_object* v___f_2919_; lean_object* v___f_2920_; lean_object* v___f_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v_map_2917_ = lean_ctor_get(v_toFunctor_2907_, 0);
lean_inc(v_map_2917_);
lean_dec_ref(v_toFunctor_2907_);
v___f_2918_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2918_, 0, v_treesSaved_2916_);
lean_closure_set(v___f_2918_, 1, v_modifyInfoState_2908_);
v___f_2919_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2919_, 0, v___f_2918_);
lean_inc_ref(v___f_2919_);
lean_inc(v_toBind_2910_);
v___f_2920_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_2920_, 0, v_toPure_2909_);
lean_closure_set(v___f_2920_, 1, v_toBind_2910_);
lean_closure_set(v___f_2920_, 2, v___f_2919_);
v___f_2921_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__6), 6, 5);
lean_closure_set(v___f_2921_, 0, v_toBind_2910_);
lean_closure_set(v___f_2921_, 1, v_mkInfoOnError_2911_);
lean_closure_set(v___f_2921_, 2, v___f_2920_);
lean_closure_set(v___f_2921_, 3, v_mkInfo_2912_);
lean_closure_set(v___f_2921_, 4, v___f_2919_);
v___x_2922_ = lean_apply_4(v_inst_2913_, lean_box(0), lean_box(0), v_x_2914_, v___f_2921_);
v___x_2923_ = lean_apply_4(v_map_2917_, lean_box(0), lean_box(0), v___f_2915_, v___x_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object* v_x_2924_, lean_object* v_inst_2925_, lean_object* v_inst_2926_, lean_object* v_toBind_2927_, lean_object* v___f_2928_, lean_object* v_____do__lift_2929_){
_start:
{
uint8_t v_enabled_2930_; 
v_enabled_2930_ = lean_ctor_get_uint8(v_____do__lift_2929_, sizeof(void*)*3);
if (v_enabled_2930_ == 0)
{
lean_dec(v___f_2928_);
lean_dec(v_toBind_2927_);
lean_dec_ref(v_inst_2926_);
lean_dec_ref(v_inst_2925_);
lean_inc(v_x_2924_);
return v_x_2924_;
}
else
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2925_, v_inst_2926_);
v___x_2932_ = lean_apply_4(v_toBind_2927_, lean_box(0), lean_box(0), v___x_2931_, v___f_2928_);
return v___x_2932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object* v_x_2933_, lean_object* v_inst_2934_, lean_object* v_inst_2935_, lean_object* v_toBind_2936_, lean_object* v___f_2937_, lean_object* v_____do__lift_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__7(v_x_2933_, v_inst_2934_, v_inst_2935_, v_toBind_2936_, v___f_2937_, v_____do__lift_2938_);
lean_dec_ref(v_____do__lift_2938_);
lean_dec(v_x_2933_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object* v_inst_2941_, lean_object* v_inst_2942_, lean_object* v_inst_2943_, lean_object* v_x_2944_, lean_object* v_mkInfo_2945_, lean_object* v_mkInfoOnError_2946_){
_start:
{
lean_object* v_toApplicative_2947_; lean_object* v_toBind_2948_; lean_object* v_getInfoState_2949_; lean_object* v_modifyInfoState_2950_; lean_object* v_toFunctor_2951_; lean_object* v_toPure_2952_; lean_object* v___f_2953_; lean_object* v___f_2954_; lean_object* v___f_2955_; lean_object* v___x_2956_; 
v_toApplicative_2947_ = lean_ctor_get(v_inst_2941_, 0);
v_toBind_2948_ = lean_ctor_get(v_inst_2941_, 1);
lean_inc_n(v_toBind_2948_, 3);
v_getInfoState_2949_ = lean_ctor_get(v_inst_2942_, 0);
lean_inc(v_getInfoState_2949_);
v_modifyInfoState_2950_ = lean_ctor_get(v_inst_2942_, 1);
v_toFunctor_2951_ = lean_ctor_get(v_toApplicative_2947_, 0);
v_toPure_2952_ = lean_ctor_get(v_toApplicative_2947_, 1);
v___f_2953_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2944_);
lean_inc(v_toPure_2952_);
lean_inc(v_modifyInfoState_2950_);
lean_inc_ref(v_toFunctor_2951_);
v___f_2954_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__5), 10, 9);
lean_closure_set(v___f_2954_, 0, v_toFunctor_2951_);
lean_closure_set(v___f_2954_, 1, v_modifyInfoState_2950_);
lean_closure_set(v___f_2954_, 2, v_toPure_2952_);
lean_closure_set(v___f_2954_, 3, v_toBind_2948_);
lean_closure_set(v___f_2954_, 4, v_mkInfoOnError_2946_);
lean_closure_set(v___f_2954_, 5, v_mkInfo_2945_);
lean_closure_set(v___f_2954_, 6, v_inst_2943_);
lean_closure_set(v___f_2954_, 7, v_x_2944_);
lean_closure_set(v___f_2954_, 8, v___f_2953_);
v___f_2955_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2955_, 0, v_x_2944_);
lean_closure_set(v___f_2955_, 1, v_inst_2941_);
lean_closure_set(v___f_2955_, 2, v_inst_2942_);
lean_closure_set(v___f_2955_, 3, v_toBind_2948_);
lean_closure_set(v___f_2955_, 4, v___f_2954_);
v___x_2956_ = lean_apply_4(v_toBind_2948_, lean_box(0), lean_box(0), v_getInfoState_2949_, v___f_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* v_m_2957_, lean_object* v_inst_2958_, lean_object* v_inst_2959_, lean_object* v_00_u03b1_2960_, lean_object* v_inst_2961_, lean_object* v_x_2962_, lean_object* v_mkInfo_2963_, lean_object* v_mkInfoOnError_2964_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_Lean_Elab_withInfoContext_x27___redArg(v_inst_2958_, v_inst_2959_, v_inst_2961_, v_x_2962_, v_mkInfo_2963_, v_mkInfoOnError_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object* v_treesSaved_2966_, lean_object* v_tree_2967_, lean_object* v_s_2968_){
_start:
{
uint8_t v_enabled_2969_; lean_object* v_assignment_2970_; lean_object* v_lazyAssignment_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2979_; 
v_enabled_2969_ = lean_ctor_get_uint8(v_s_2968_, sizeof(void*)*3);
v_assignment_2970_ = lean_ctor_get(v_s_2968_, 0);
v_lazyAssignment_2971_ = lean_ctor_get(v_s_2968_, 1);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_s_2968_);
if (v_isSharedCheck_2979_ == 0)
{
lean_object* v_unused_2980_; 
v_unused_2980_ = lean_ctor_get(v_s_2968_, 2);
lean_dec(v_unused_2980_);
v___x_2973_ = v_s_2968_;
v_isShared_2974_ = v_isSharedCheck_2979_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_lazyAssignment_2971_);
lean_inc(v_assignment_2970_);
lean_dec(v_s_2968_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2979_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2975_; lean_object* v___x_2977_; 
v___x_2975_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2966_, v_tree_2967_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 2, v___x_2975_);
v___x_2977_ = v___x_2973_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_assignment_2970_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v_lazyAssignment_2971_);
lean_ctor_set(v_reuseFailAlloc_2978_, 2, v___x_2975_);
lean_ctor_set_uint8(v_reuseFailAlloc_2978_, sizeof(void*)*3, v_enabled_2969_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object* v_treesSaved_2981_, lean_object* v_modifyInfoState_2982_, lean_object* v_tree_2983_){
_start:
{
lean_object* v___f_2984_; lean_object* v___x_2985_; 
v___f_2984_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2984_, 0, v_treesSaved_2981_);
lean_closure_set(v___f_2984_, 1, v_tree_2983_);
v___x_2985_ = lean_apply_1(v_modifyInfoState_2982_, v___f_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object* v_mkInfoTree_2986_, lean_object* v_toBind_2987_, lean_object* v___f_2988_, lean_object* v_st_2989_){
_start:
{
lean_object* v_trees_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v_trees_2990_ = lean_ctor_get(v_st_2989_, 2);
lean_inc_ref(v_trees_2990_);
lean_dec_ref(v_st_2989_);
v___x_2991_ = lean_apply_1(v_mkInfoTree_2986_, v_trees_2990_);
v___x_2992_ = lean_apply_4(v_toBind_2987_, lean_box(0), lean_box(0), v___x_2991_, v___f_2988_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object* v_toBind_2993_, lean_object* v_getInfoState_2994_, lean_object* v___f_2995_, lean_object* v_x_2996_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = lean_apply_4(v_toBind_2993_, lean_box(0), lean_box(0), v_getInfoState_2994_, v___f_2995_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object* v_toBind_2998_, lean_object* v_getInfoState_2999_, lean_object* v___f_3000_, lean_object* v_x_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(v_toBind_2998_, v_getInfoState_2999_, v___f_3000_, v_x_3001_);
lean_dec(v_x_3001_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object* v_toFunctor_3003_, lean_object* v_modifyInfoState_3004_, lean_object* v_mkInfoTree_3005_, lean_object* v_toBind_3006_, lean_object* v_getInfoState_3007_, lean_object* v_inst_3008_, lean_object* v_x_3009_, lean_object* v___f_3010_, lean_object* v_treesSaved_3011_){
_start:
{
lean_object* v_map_3012_; lean_object* v___f_3013_; lean_object* v___f_3014_; lean_object* v___f_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v_map_3012_ = lean_ctor_get(v_toFunctor_3003_, 0);
lean_inc(v_map_3012_);
lean_dec_ref(v_toFunctor_3003_);
v___f_3013_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3013_, 0, v_treesSaved_3011_);
lean_closure_set(v___f_3013_, 1, v_modifyInfoState_3004_);
lean_inc(v_toBind_3006_);
v___f_3014_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__2), 4, 3);
lean_closure_set(v___f_3014_, 0, v_mkInfoTree_3005_);
lean_closure_set(v___f_3014_, 1, v_toBind_3006_);
lean_closure_set(v___f_3014_, 2, v___f_3013_);
v___f_3015_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3015_, 0, v_toBind_3006_);
lean_closure_set(v___f_3015_, 1, v_getInfoState_3007_);
lean_closure_set(v___f_3015_, 2, v___f_3014_);
v___x_3016_ = lean_apply_4(v_inst_3008_, lean_box(0), lean_box(0), v_x_3009_, v___f_3015_);
v___x_3017_ = lean_apply_4(v_map_3012_, lean_box(0), lean_box(0), v___f_3010_, v___x_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object* v_inst_3018_, lean_object* v_inst_3019_, lean_object* v_inst_3020_, lean_object* v_x_3021_, lean_object* v_mkInfoTree_3022_){
_start:
{
lean_object* v_toApplicative_3023_; lean_object* v_toBind_3024_; lean_object* v_getInfoState_3025_; lean_object* v_modifyInfoState_3026_; lean_object* v_toFunctor_3027_; lean_object* v___f_3028_; lean_object* v___f_3029_; lean_object* v___f_3030_; lean_object* v___x_3031_; 
v_toApplicative_3023_ = lean_ctor_get(v_inst_3018_, 0);
v_toBind_3024_ = lean_ctor_get(v_inst_3018_, 1);
lean_inc_n(v_toBind_3024_, 3);
v_getInfoState_3025_ = lean_ctor_get(v_inst_3019_, 0);
lean_inc_n(v_getInfoState_3025_, 2);
v_modifyInfoState_3026_ = lean_ctor_get(v_inst_3019_, 1);
v_toFunctor_3027_ = lean_ctor_get(v_toApplicative_3023_, 0);
v___f_3028_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3021_);
lean_inc(v_modifyInfoState_3026_);
lean_inc_ref(v_toFunctor_3027_);
v___f_3029_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__4), 9, 8);
lean_closure_set(v___f_3029_, 0, v_toFunctor_3027_);
lean_closure_set(v___f_3029_, 1, v_modifyInfoState_3026_);
lean_closure_set(v___f_3029_, 2, v_mkInfoTree_3022_);
lean_closure_set(v___f_3029_, 3, v_toBind_3024_);
lean_closure_set(v___f_3029_, 4, v_getInfoState_3025_);
lean_closure_set(v___f_3029_, 5, v_inst_3020_);
lean_closure_set(v___f_3029_, 6, v_x_3021_);
lean_closure_set(v___f_3029_, 7, v___f_3028_);
v___f_3030_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3030_, 0, v_x_3021_);
lean_closure_set(v___f_3030_, 1, v_inst_3018_);
lean_closure_set(v___f_3030_, 2, v_inst_3019_);
lean_closure_set(v___f_3030_, 3, v_toBind_3024_);
lean_closure_set(v___f_3030_, 4, v___f_3029_);
v___x_3031_ = lean_apply_4(v_toBind_3024_, lean_box(0), lean_box(0), v_getInfoState_3025_, v___f_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object* v_m_3032_, lean_object* v_inst_3033_, lean_object* v_inst_3034_, lean_object* v_00_u03b1_3035_, lean_object* v_inst_3036_, lean_object* v_x_3037_, lean_object* v_mkInfoTree_3038_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3033_, v_inst_3034_, v_inst_3036_, v_x_3037_, v_mkInfoTree_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object* v_trees_3040_, lean_object* v_toPure_3041_, lean_object* v_____do__lift_3042_){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3043_, 0, v_____do__lift_3042_);
lean_ctor_set(v___x_3043_, 1, v_trees_3040_);
v___x_3044_ = lean_apply_2(v_toPure_3041_, lean_box(0), v___x_3043_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object* v_toPure_3045_, lean_object* v_toBind_3046_, lean_object* v_mkInfo_3047_, lean_object* v_trees_3048_){
_start:
{
lean_object* v___f_3049_; lean_object* v___x_3050_; 
v___f_3049_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3049_, 0, v_trees_3048_);
lean_closure_set(v___f_3049_, 1, v_toPure_3045_);
v___x_3050_ = lean_apply_4(v_toBind_3046_, lean_box(0), lean_box(0), v_mkInfo_3047_, v___f_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object* v_inst_3051_, lean_object* v_inst_3052_, lean_object* v_inst_3053_, lean_object* v_x_3054_, lean_object* v_mkInfo_3055_){
_start:
{
lean_object* v_toApplicative_3056_; lean_object* v_toBind_3057_; lean_object* v_toPure_3058_; lean_object* v___f_3059_; lean_object* v___x_3060_; 
v_toApplicative_3056_ = lean_ctor_get(v_inst_3051_, 0);
v_toBind_3057_ = lean_ctor_get(v_inst_3051_, 1);
v_toPure_3058_ = lean_ctor_get(v_toApplicative_3056_, 1);
lean_inc(v_toBind_3057_);
lean_inc(v_toPure_3058_);
v___f_3059_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3059_, 0, v_toPure_3058_);
lean_closure_set(v___f_3059_, 1, v_toBind_3057_);
lean_closure_set(v___f_3059_, 2, v_mkInfo_3055_);
v___x_3060_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3051_, v_inst_3052_, v_inst_3053_, v_x_3054_, v___f_3059_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object* v_m_3061_, lean_object* v_inst_3062_, lean_object* v_inst_3063_, lean_object* v_00_u03b1_3064_, lean_object* v_inst_3065_, lean_object* v_x_3066_, lean_object* v_mkInfo_3067_){
_start:
{
lean_object* v_toApplicative_3068_; lean_object* v_toBind_3069_; lean_object* v_toPure_3070_; lean_object* v___f_3071_; lean_object* v___x_3072_; 
v_toApplicative_3068_ = lean_ctor_get(v_inst_3062_, 0);
v_toBind_3069_ = lean_ctor_get(v_inst_3062_, 1);
v_toPure_3070_ = lean_ctor_get(v_toApplicative_3068_, 1);
lean_inc(v_toBind_3069_);
lean_inc(v_toPure_3070_);
v___f_3071_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3071_, 0, v_toPure_3070_);
lean_closure_set(v___f_3071_, 1, v_toBind_3069_);
lean_closure_set(v___f_3071_, 2, v_mkInfo_3067_);
v___x_3072_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3062_, v_inst_3063_, v_inst_3065_, v_x_3066_, v___f_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object* v_treesSaved_3073_, lean_object* v_trees_3074_, lean_object* v_s_3075_){
_start:
{
uint8_t v_enabled_3076_; lean_object* v_assignment_3077_; lean_object* v_lazyAssignment_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3086_; 
v_enabled_3076_ = lean_ctor_get_uint8(v_s_3075_, sizeof(void*)*3);
v_assignment_3077_ = lean_ctor_get(v_s_3075_, 0);
v_lazyAssignment_3078_ = lean_ctor_get(v_s_3075_, 1);
v_isSharedCheck_3086_ = !lean_is_exclusive(v_s_3075_);
if (v_isSharedCheck_3086_ == 0)
{
lean_object* v_unused_3087_; 
v_unused_3087_ = lean_ctor_get(v_s_3075_, 2);
lean_dec(v_unused_3087_);
v___x_3080_ = v_s_3075_;
v_isShared_3081_ = v_isSharedCheck_3086_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_lazyAssignment_3078_);
lean_inc(v_assignment_3077_);
lean_dec(v_s_3075_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3086_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3082_; lean_object* v___x_3084_; 
v___x_3082_ = l_Lean_PersistentArray_append___redArg(v_treesSaved_3073_, v_trees_3074_);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 2, v___x_3082_);
v___x_3084_ = v___x_3080_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_assignment_3077_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v_lazyAssignment_3078_);
lean_ctor_set(v_reuseFailAlloc_3085_, 2, v___x_3082_);
lean_ctor_set_uint8(v_reuseFailAlloc_3085_, sizeof(void*)*3, v_enabled_3076_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object* v_treesSaved_3088_, lean_object* v_trees_3089_, lean_object* v_s_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_3088_, v_trees_3089_, v_s_3090_);
lean_dec_ref(v_trees_3089_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object* v_treesSaved_3092_, lean_object* v_modifyInfoState_3093_, lean_object* v_trees_3094_){
_start:
{
lean_object* v___f_3095_; lean_object* v___x_3096_; 
v___f_3095_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3095_, 0, v_treesSaved_3092_);
lean_closure_set(v___f_3095_, 1, v_trees_3094_);
v___x_3096_ = lean_apply_1(v_modifyInfoState_3093_, v___f_3095_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object* v_toPure_3097_, lean_object* v_tree_3098_, lean_object* v_____do__lift_3099_){
_start:
{
if (lean_obj_tag(v_____do__lift_3099_) == 0)
{
lean_object* v___x_3100_; 
v___x_3100_ = lean_apply_2(v_toPure_3097_, lean_box(0), v_tree_3098_);
return v___x_3100_;
}
else
{
lean_object* v_val_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v_val_3101_ = lean_ctor_get(v_____do__lift_3099_, 0);
lean_inc(v_val_3101_);
v___x_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3102_, 0, v_val_3101_);
lean_ctor_set(v___x_3102_, 1, v_tree_3098_);
v___x_3103_ = lean_apply_2(v_toPure_3097_, lean_box(0), v___x_3102_);
return v___x_3103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object* v_toPure_3104_, lean_object* v_tree_3105_, lean_object* v_____do__lift_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_3104_, v_tree_3105_, v_____do__lift_3106_);
lean_dec(v_____do__lift_3106_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object* v_assignment_3108_, lean_object* v_toPure_3109_, lean_object* v_toBind_3110_, lean_object* v_ctx_x3f_3111_, lean_object* v_tree_3112_){
_start:
{
lean_object* v_tree_3113_; lean_object* v___f_3114_; lean_object* v___x_3115_; 
v_tree_3113_ = l_Lean_Elab_InfoTree_substitute(v_tree_3112_, v_assignment_3108_);
v___f_3114_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3114_, 0, v_toPure_3109_);
lean_closure_set(v___f_3114_, 1, v_tree_3113_);
v___x_3115_ = lean_apply_4(v_toBind_3110_, lean_box(0), lean_box(0), v_ctx_x3f_3111_, v___f_3114_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object* v_assignment_3116_, lean_object* v_toPure_3117_, lean_object* v_toBind_3118_, lean_object* v_ctx_x3f_3119_, lean_object* v_tree_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(v_assignment_3116_, v_toPure_3117_, v_toBind_3118_, v_ctx_x3f_3119_, v_tree_3120_);
lean_dec_ref(v_assignment_3116_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object* v_toPure_3122_, lean_object* v_toBind_3123_, lean_object* v_ctx_x3f_3124_, lean_object* v_inst_3125_, lean_object* v___f_3126_, lean_object* v_st_3127_){
_start:
{
lean_object* v_assignment_3128_; lean_object* v_trees_3129_; lean_object* v___f_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v_assignment_3128_ = lean_ctor_get(v_st_3127_, 0);
lean_inc_ref(v_assignment_3128_);
v_trees_3129_ = lean_ctor_get(v_st_3127_, 2);
lean_inc_ref(v_trees_3129_);
lean_dec_ref(v_st_3127_);
lean_inc(v_toBind_3123_);
v___f_3130_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_3130_, 0, v_assignment_3128_);
lean_closure_set(v___f_3130_, 1, v_toPure_3122_);
lean_closure_set(v___f_3130_, 2, v_toBind_3123_);
lean_closure_set(v___f_3130_, 3, v_ctx_x3f_3124_);
v___x_3131_ = l_Lean_PersistentArray_mapM___redArg(v_inst_3125_, v___f_3130_, v_trees_3129_);
v___x_3132_ = lean_apply_4(v_toBind_3123_, lean_box(0), lean_box(0), v___x_3131_, v___f_3126_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object* v_toFunctor_3133_, lean_object* v_modifyInfoState_3134_, lean_object* v_toPure_3135_, lean_object* v_toBind_3136_, lean_object* v_ctx_x3f_3137_, lean_object* v_inst_3138_, lean_object* v_getInfoState_3139_, lean_object* v_inst_3140_, lean_object* v_x_3141_, lean_object* v___f_3142_, lean_object* v_treesSaved_3143_){
_start:
{
lean_object* v_map_3144_; lean_object* v___f_3145_; lean_object* v___f_3146_; lean_object* v___f_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v_map_3144_ = lean_ctor_get(v_toFunctor_3133_, 0);
lean_inc(v_map_3144_);
lean_dec_ref(v_toFunctor_3133_);
v___f_3145_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3145_, 0, v_treesSaved_3143_);
lean_closure_set(v___f_3145_, 1, v_modifyInfoState_3134_);
lean_inc(v_toBind_3136_);
v___f_3146_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4), 6, 5);
lean_closure_set(v___f_3146_, 0, v_toPure_3135_);
lean_closure_set(v___f_3146_, 1, v_toBind_3136_);
lean_closure_set(v___f_3146_, 2, v_ctx_x3f_3137_);
lean_closure_set(v___f_3146_, 3, v_inst_3138_);
lean_closure_set(v___f_3146_, 4, v___f_3145_);
v___f_3147_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3147_, 0, v_toBind_3136_);
lean_closure_set(v___f_3147_, 1, v_getInfoState_3139_);
lean_closure_set(v___f_3147_, 2, v___f_3146_);
v___x_3148_ = lean_apply_4(v_inst_3140_, lean_box(0), lean_box(0), v_x_3141_, v___f_3147_);
v___x_3149_ = lean_apply_4(v_map_3144_, lean_box(0), lean_box(0), v___f_3142_, v___x_3148_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object* v_inst_3150_, lean_object* v_inst_3151_, lean_object* v_inst_3152_, lean_object* v_x_3153_, lean_object* v_ctx_x3f_3154_){
_start:
{
lean_object* v_toApplicative_3155_; lean_object* v_toBind_3156_; lean_object* v_getInfoState_3157_; lean_object* v_modifyInfoState_3158_; lean_object* v_toFunctor_3159_; lean_object* v_toPure_3160_; lean_object* v___f_3161_; lean_object* v___f_3162_; lean_object* v___f_3163_; lean_object* v___x_3164_; 
v_toApplicative_3155_ = lean_ctor_get(v_inst_3150_, 0);
v_toBind_3156_ = lean_ctor_get(v_inst_3150_, 1);
lean_inc_n(v_toBind_3156_, 3);
v_getInfoState_3157_ = lean_ctor_get(v_inst_3151_, 0);
lean_inc_n(v_getInfoState_3157_, 2);
v_modifyInfoState_3158_ = lean_ctor_get(v_inst_3151_, 1);
v_toFunctor_3159_ = lean_ctor_get(v_toApplicative_3155_, 0);
v_toPure_3160_ = lean_ctor_get(v_toApplicative_3155_, 1);
v___f_3161_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3153_);
lean_inc_ref(v_inst_3150_);
lean_inc(v_toPure_3160_);
lean_inc(v_modifyInfoState_3158_);
lean_inc_ref(v_toFunctor_3159_);
v___f_3162_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6), 11, 10);
lean_closure_set(v___f_3162_, 0, v_toFunctor_3159_);
lean_closure_set(v___f_3162_, 1, v_modifyInfoState_3158_);
lean_closure_set(v___f_3162_, 2, v_toPure_3160_);
lean_closure_set(v___f_3162_, 3, v_toBind_3156_);
lean_closure_set(v___f_3162_, 4, v_ctx_x3f_3154_);
lean_closure_set(v___f_3162_, 5, v_inst_3150_);
lean_closure_set(v___f_3162_, 6, v_getInfoState_3157_);
lean_closure_set(v___f_3162_, 7, v_inst_3152_);
lean_closure_set(v___f_3162_, 8, v_x_3153_);
lean_closure_set(v___f_3162_, 9, v___f_3161_);
v___f_3163_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3163_, 0, v_x_3153_);
lean_closure_set(v___f_3163_, 1, v_inst_3150_);
lean_closure_set(v___f_3163_, 2, v_inst_3151_);
lean_closure_set(v___f_3163_, 3, v_toBind_3156_);
lean_closure_set(v___f_3163_, 4, v___f_3162_);
v___x_3164_ = lean_apply_4(v_toBind_3156_, lean_box(0), lean_box(0), v_getInfoState_3157_, v___f_3163_);
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object* v_m_3165_, lean_object* v_inst_3166_, lean_object* v_inst_3167_, lean_object* v_00_u03b1_3168_, lean_object* v_inst_3169_, lean_object* v_x_3170_, lean_object* v_ctx_x3f_3171_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3166_, v_inst_3167_, v_inst_3169_, v_x_3170_, v_ctx_x3f_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object* v_toPure_3173_, lean_object* v_____do__lift_3174_){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3175_, 0, v_____do__lift_3174_);
v___x_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
v___x_3177_ = lean_apply_2(v_toPure_3173_, lean_box(0), v___x_3176_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object* v_inst_3178_, lean_object* v_inst_3179_, lean_object* v_inst_3180_, lean_object* v_inst_3181_, lean_object* v_inst_3182_, lean_object* v_inst_3183_, lean_object* v_inst_3184_, lean_object* v_inst_3185_, lean_object* v_inst_3186_, lean_object* v_x_3187_){
_start:
{
lean_object* v_toApplicative_3188_; lean_object* v_toBind_3189_; lean_object* v_toPure_3190_; lean_object* v___x_3191_; lean_object* v___f_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v_toApplicative_3188_ = lean_ctor_get(v_inst_3178_, 0);
v_toBind_3189_ = lean_ctor_get(v_inst_3178_, 1);
v_toPure_3190_ = lean_ctor_get(v_toApplicative_3188_, 1);
lean_inc_ref(v_inst_3178_);
v___x_3191_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_3178_, v_inst_3182_, v_inst_3184_, v_inst_3183_, v_inst_3185_, v_inst_3180_, v_inst_3186_);
lean_inc(v_toPure_3190_);
v___f_3192_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3192_, 0, v_toPure_3190_);
lean_inc(v_toBind_3189_);
v___x_3193_ = lean_apply_4(v_toBind_3189_, lean_box(0), lean_box(0), v___x_3191_, v___f_3192_);
v___x_3194_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3178_, v_inst_3179_, v_inst_3181_, v_x_3187_, v___x_3193_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object* v_m_3195_, lean_object* v_inst_3196_, lean_object* v_inst_3197_, lean_object* v_00_u03b1_3198_, lean_object* v_inst_3199_, lean_object* v_inst_3200_, lean_object* v_inst_3201_, lean_object* v_inst_3202_, lean_object* v_inst_3203_, lean_object* v_inst_3204_, lean_object* v_inst_3205_, lean_object* v_x_3206_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Lean_Elab_withSaveInfoContext___redArg(v_inst_3196_, v_inst_3197_, v_inst_3199_, v_inst_3200_, v_inst_3201_, v_inst_3202_, v_inst_3203_, v_inst_3204_, v_inst_3205_, v_x_3206_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object* v_toPure_3208_, lean_object* v_____x_3209_){
_start:
{
if (lean_obj_tag(v_____x_3209_) == 1)
{
lean_object* v_val_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3219_; 
v_val_3210_ = lean_ctor_get(v_____x_3209_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v_____x_3209_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3212_ = v_____x_3209_;
v_isShared_3213_ = v_isSharedCheck_3219_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_val_3210_);
lean_dec(v_____x_3209_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3219_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3214_; lean_object* v___x_3216_; 
v___x_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3214_, 0, v_val_3210_);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 0, v___x_3214_);
v___x_3216_ = v___x_3212_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3214_);
v___x_3216_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_apply_2(v_toPure_3208_, lean_box(0), v___x_3216_);
return v___x_3217_;
}
}
}
else
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
lean_dec(v_____x_3209_);
v___x_3220_ = lean_box(0);
v___x_3221_ = lean_apply_2(v_toPure_3208_, lean_box(0), v___x_3220_);
return v___x_3221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object* v_inst_3222_, lean_object* v_inst_3223_, lean_object* v_inst_3224_, lean_object* v_inst_3225_, lean_object* v_x_3226_){
_start:
{
lean_object* v_toApplicative_3227_; lean_object* v_toBind_3228_; lean_object* v_toPure_3229_; lean_object* v___f_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v_toApplicative_3227_ = lean_ctor_get(v_inst_3222_, 0);
v_toBind_3228_ = lean_ctor_get(v_inst_3222_, 1);
v_toPure_3229_ = lean_ctor_get(v_toApplicative_3227_, 1);
lean_inc(v_toPure_3229_);
v___f_3230_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3230_, 0, v_toPure_3229_);
lean_inc(v_toBind_3228_);
v___x_3231_ = lean_apply_4(v_toBind_3228_, lean_box(0), lean_box(0), v_inst_3225_, v___f_3230_);
v___x_3232_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3222_, v_inst_3223_, v_inst_3224_, v_x_3226_, v___x_3231_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object* v_m_3233_, lean_object* v_inst_3234_, lean_object* v_inst_3235_, lean_object* v_00_u03b1_3236_, lean_object* v_inst_3237_, lean_object* v_inst_3238_, lean_object* v_x_3239_){
_start:
{
lean_object* v___x_3240_; 
v___x_3240_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(v_inst_3234_, v_inst_3235_, v_inst_3237_, v_inst_3238_, v_x_3239_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object* v_toPure_3241_, lean_object* v_autoImplicits_3242_){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3243_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3243_, 0, v_autoImplicits_3242_);
v___x_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
v___x_3245_ = lean_apply_2(v_toPure_3241_, lean_box(0), v___x_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object* v_inst_3246_, lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_inst_3249_, lean_object* v_x_3250_){
_start:
{
lean_object* v_toApplicative_3251_; lean_object* v_toBind_3252_; lean_object* v_toPure_3253_; lean_object* v___f_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v_toApplicative_3251_ = lean_ctor_get(v_inst_3246_, 0);
v_toBind_3252_ = lean_ctor_get(v_inst_3246_, 1);
v_toPure_3253_ = lean_ctor_get(v_toApplicative_3251_, 1);
lean_inc(v_toPure_3253_);
v___f_3254_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3254_, 0, v_toPure_3253_);
lean_inc(v_toBind_3252_);
v___x_3255_ = lean_apply_4(v_toBind_3252_, lean_box(0), lean_box(0), v_inst_3249_, v___f_3254_);
v___x_3256_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3246_, v_inst_3247_, v_inst_3248_, v_x_3250_, v___x_3255_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object* v_m_3257_, lean_object* v_inst_3258_, lean_object* v_inst_3259_, lean_object* v_00_u03b1_3260_, lean_object* v_inst_3261_, lean_object* v_inst_3262_, lean_object* v_x_3263_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(v_inst_3258_, v_inst_3259_, v_inst_3261_, v_inst_3262_, v_x_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object* v___x_3265_, lean_object* v___x_3266_, lean_object* v_mvarId_3267_, lean_object* v_toPure_3268_, lean_object* v_____do__lift_3269_){
_start:
{
lean_object* v_assignment_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v_assignment_3270_ = lean_ctor_get(v_____do__lift_3269_, 0);
v___x_3271_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_3265_, v___x_3266_, v_assignment_3270_, v_mvarId_3267_);
v___x_3272_ = lean_apply_2(v_toPure_3268_, lean_box(0), v___x_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object* v___x_3273_, lean_object* v___x_3274_, lean_object* v_mvarId_3275_, lean_object* v_toPure_3276_, lean_object* v_____do__lift_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(v___x_3273_, v___x_3274_, v_mvarId_3275_, v_toPure_3276_, v_____do__lift_3277_);
lean_dec_ref(v_____do__lift_3277_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object* v_inst_3281_, lean_object* v_inst_3282_, lean_object* v_mvarId_3283_){
_start:
{
lean_object* v_toApplicative_3284_; lean_object* v_toBind_3285_; lean_object* v_getInfoState_3286_; lean_object* v_toPure_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___f_3290_; lean_object* v___x_3291_; 
v_toApplicative_3284_ = lean_ctor_get(v_inst_3281_, 0);
lean_inc_ref(v_toApplicative_3284_);
v_toBind_3285_ = lean_ctor_get(v_inst_3281_, 1);
lean_inc(v_toBind_3285_);
lean_dec_ref(v_inst_3281_);
v_getInfoState_3286_ = lean_ctor_get(v_inst_3282_, 0);
lean_inc(v_getInfoState_3286_);
lean_dec_ref(v_inst_3282_);
v_toPure_3287_ = lean_ctor_get(v_toApplicative_3284_, 1);
lean_inc(v_toPure_3287_);
lean_dec_ref(v_toApplicative_3284_);
v___x_3288_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3289_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___f_3290_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3290_, 0, v___x_3288_);
lean_closure_set(v___f_3290_, 1, v___x_3289_);
lean_closure_set(v___f_3290_, 2, v_mvarId_3283_);
lean_closure_set(v___f_3290_, 3, v_toPure_3287_);
v___x_3291_ = lean_apply_4(v_toBind_3285_, lean_box(0), lean_box(0), v_getInfoState_3286_, v___f_3290_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* v_m_3292_, lean_object* v_inst_3293_, lean_object* v_inst_3294_, lean_object* v_mvarId_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3293_, v_inst_3294_, v_mvarId_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object* v___x_3297_, lean_object* v___x_3298_, lean_object* v_mvarId_3299_, lean_object* v_infoTree_3300_, lean_object* v_s_3301_){
_start:
{
uint8_t v_enabled_3302_; lean_object* v_assignment_3303_; lean_object* v_lazyAssignment_3304_; lean_object* v_trees_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3313_; 
v_enabled_3302_ = lean_ctor_get_uint8(v_s_3301_, sizeof(void*)*3);
v_assignment_3303_ = lean_ctor_get(v_s_3301_, 0);
v_lazyAssignment_3304_ = lean_ctor_get(v_s_3301_, 1);
v_trees_3305_ = lean_ctor_get(v_s_3301_, 2);
v_isSharedCheck_3313_ = !lean_is_exclusive(v_s_3301_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3307_ = v_s_3301_;
v_isShared_3308_ = v_isSharedCheck_3313_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_trees_3305_);
lean_inc(v_lazyAssignment_3304_);
lean_inc(v_assignment_3303_);
lean_dec(v_s_3301_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3313_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3309_; lean_object* v___x_3311_; 
v___x_3309_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3297_, v___x_3298_, v_assignment_3303_, v_mvarId_3299_, v_infoTree_3300_);
if (v_isShared_3308_ == 0)
{
lean_ctor_set(v___x_3307_, 0, v___x_3309_);
v___x_3311_ = v___x_3307_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3309_);
lean_ctor_set(v_reuseFailAlloc_3312_, 1, v_lazyAssignment_3304_);
lean_ctor_set(v_reuseFailAlloc_3312_, 2, v_trees_3305_);
lean_ctor_set_uint8(v_reuseFailAlloc_3312_, sizeof(void*)*3, v_enabled_3302_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3317_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2));
v___x_3318_ = lean_unsigned_to_nat(2u);
v___x_3319_ = lean_unsigned_to_nat(384u);
v___x_3320_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1));
v___x_3321_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0));
v___x_3322_ = l_mkPanicMessageWithDecl(v___x_3321_, v___x_3320_, v___x_3319_, v___x_3318_, v___x_3317_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object* v_inst_3323_, lean_object* v___f_3324_, lean_object* v___x_3325_, lean_object* v_____do__lift_3326_){
_start:
{
if (lean_obj_tag(v_____do__lift_3326_) == 0)
{
lean_object* v_modifyInfoState_3327_; lean_object* v___x_3328_; 
v_modifyInfoState_3327_ = lean_ctor_get(v_inst_3323_, 1);
lean_inc(v_modifyInfoState_3327_);
lean_dec_ref(v_inst_3323_);
v___x_3328_ = lean_apply_1(v_modifyInfoState_3327_, v___f_3324_);
return v___x_3328_;
}
else
{
lean_object* v___x_3329_; lean_object* v___x_3330_; 
lean_dec_ref(v___f_3324_);
lean_dec_ref(v_inst_3323_);
v___x_3329_ = lean_obj_once(&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3, &l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3_once, _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3);
v___x_3330_ = l_panic___redArg(v___x_3325_, v___x_3329_);
return v___x_3330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object* v_inst_3331_, lean_object* v___f_3332_, lean_object* v___x_3333_, lean_object* v_____do__lift_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(v_inst_3331_, v___f_3332_, v___x_3333_, v_____do__lift_3334_);
lean_dec(v_____do__lift_3334_);
lean_dec(v___x_3333_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object* v_inst_3336_, lean_object* v_inst_3337_, lean_object* v_mvarId_3338_, lean_object* v_infoTree_3339_){
_start:
{
lean_object* v_toBind_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___f_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___f_3347_; lean_object* v___x_3348_; 
v_toBind_3340_ = lean_ctor_get(v_inst_3336_, 1);
lean_inc(v_toBind_3340_);
v___x_3341_ = lean_box(0);
v___x_3342_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3343_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
lean_inc(v_mvarId_3338_);
v___f_3344_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__0), 5, 4);
lean_closure_set(v___f_3344_, 0, v___x_3342_);
lean_closure_set(v___f_3344_, 1, v___x_3343_);
lean_closure_set(v___f_3344_, 2, v_mvarId_3338_);
lean_closure_set(v___f_3344_, 3, v_infoTree_3339_);
lean_inc_ref(v_inst_3337_);
lean_inc_ref(v_inst_3336_);
v___x_3345_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3336_, v_inst_3337_, v_mvarId_3338_);
v___x_3346_ = l_instInhabitedOfMonad___redArg(v_inst_3336_, v___x_3341_);
v___f_3347_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3347_, 0, v_inst_3337_);
lean_closure_set(v___f_3347_, 1, v___f_3344_);
lean_closure_set(v___f_3347_, 2, v___x_3346_);
v___x_3348_ = lean_apply_4(v_toBind_3340_, lean_box(0), lean_box(0), v___x_3345_, v___f_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* v_m_3349_, lean_object* v_inst_3350_, lean_object* v_inst_3351_, lean_object* v_mvarId_3352_, lean_object* v_infoTree_3353_){
_start:
{
lean_object* v___x_3354_; 
v___x_3354_ = l_Lean_Elab_assignInfoHoleId___redArg(v_inst_3350_, v_inst_3351_, v_mvarId_3352_, v_infoTree_3353_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object* v_stx_3355_, lean_object* v_output_3356_, lean_object* v_toPure_3357_, lean_object* v_____do__lift_3358_){
_start:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3359_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3359_, 0, v_____do__lift_3358_);
lean_ctor_set(v___x_3359_, 1, v_stx_3355_);
lean_ctor_set(v___x_3359_, 2, v_output_3356_);
v___x_3360_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
v___x_3361_ = lean_apply_2(v_toPure_3357_, lean_box(0), v___x_3360_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object* v_inst_3362_, lean_object* v_inst_3363_, lean_object* v_inst_3364_, lean_object* v_inst_3365_, lean_object* v_stx_3366_, lean_object* v_output_3367_, lean_object* v_x_3368_){
_start:
{
lean_object* v_toApplicative_3369_; lean_object* v_toBind_3370_; lean_object* v_toPure_3371_; lean_object* v___f_3372_; lean_object* v_mkInfo_3373_; lean_object* v___f_3374_; lean_object* v___x_3375_; 
v_toApplicative_3369_ = lean_ctor_get(v_inst_3363_, 0);
v_toBind_3370_ = lean_ctor_get(v_inst_3363_, 1);
v_toPure_3371_ = lean_ctor_get(v_toApplicative_3369_, 1);
lean_inc_n(v_toPure_3371_, 2);
v___f_3372_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3372_, 0, v_stx_3366_);
lean_closure_set(v___f_3372_, 1, v_output_3367_);
lean_closure_set(v___f_3372_, 2, v_toPure_3371_);
lean_inc_n(v_toBind_3370_, 2);
v_mkInfo_3373_ = lean_apply_4(v_toBind_3370_, lean_box(0), lean_box(0), v_inst_3365_, v___f_3372_);
v___f_3374_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3374_, 0, v_toPure_3371_);
lean_closure_set(v___f_3374_, 1, v_toBind_3370_);
lean_closure_set(v___f_3374_, 2, v_mkInfo_3373_);
v___x_3375_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3363_, v_inst_3364_, v_inst_3362_, v_x_3368_, v___f_3374_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* v_m_3376_, lean_object* v_00_u03b1_3377_, lean_object* v_inst_3378_, lean_object* v_inst_3379_, lean_object* v_inst_3380_, lean_object* v_inst_3381_, lean_object* v_stx_3382_, lean_object* v_output_3383_, lean_object* v_x_3384_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_Elab_withMacroExpansionInfo___redArg(v_inst_3378_, v_inst_3379_, v_inst_3380_, v_inst_3381_, v_stx_3382_, v_output_3383_, v_x_3384_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object* v_treesSaved_3386_, lean_object* v___x_3387_, lean_object* v___x_3388_, lean_object* v___x_3389_, lean_object* v_mvarId_3390_, lean_object* v_s_3391_){
_start:
{
lean_object* v_trees_3392_; uint8_t v_enabled_3393_; lean_object* v_assignment_3394_; lean_object* v_lazyAssignment_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3412_; 
v_trees_3392_ = lean_ctor_get(v_s_3391_, 2);
v_enabled_3393_ = lean_ctor_get_uint8(v_s_3391_, sizeof(void*)*3);
v_assignment_3394_ = lean_ctor_get(v_s_3391_, 0);
v_lazyAssignment_3395_ = lean_ctor_get(v_s_3391_, 1);
v_isSharedCheck_3412_ = !lean_is_exclusive(v_s_3391_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3397_ = v_s_3391_;
v_isShared_3398_ = v_isSharedCheck_3412_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_trees_3392_);
lean_inc(v_lazyAssignment_3395_);
lean_inc(v_assignment_3394_);
lean_dec(v_s_3391_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3412_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v_size_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v_size_3399_ = lean_ctor_get(v_trees_3392_, 2);
v___x_3400_ = lean_unsigned_to_nat(0u);
v___x_3401_ = lean_nat_dec_lt(v___x_3400_, v_size_3399_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3403_; 
lean_dec_ref(v_trees_3392_);
lean_dec(v_mvarId_3390_);
lean_dec_ref(v___x_3389_);
lean_dec_ref(v___x_3388_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 2, v_treesSaved_3386_);
v___x_3403_ = v___x_3397_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_assignment_3394_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_lazyAssignment_3395_);
lean_ctor_set(v_reuseFailAlloc_3404_, 2, v_treesSaved_3386_);
lean_ctor_set_uint8(v_reuseFailAlloc_3404_, sizeof(void*)*3, v_enabled_3393_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
else
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3410_; 
v___x_3405_ = lean_unsigned_to_nat(1u);
v___x_3406_ = lean_nat_sub(v_size_3399_, v___x_3405_);
v___x_3407_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3387_, v_trees_3392_, v___x_3406_);
lean_dec(v___x_3406_);
lean_dec_ref(v_trees_3392_);
v___x_3408_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3388_, v___x_3389_, v_assignment_3394_, v_mvarId_3390_, v___x_3407_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 2, v_treesSaved_3386_);
lean_ctor_set(v___x_3397_, 0, v___x_3408_);
v___x_3410_ = v___x_3397_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3408_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v_lazyAssignment_3395_);
lean_ctor_set(v_reuseFailAlloc_3411_, 2, v_treesSaved_3386_);
lean_ctor_set_uint8(v_reuseFailAlloc_3411_, sizeof(void*)*3, v_enabled_3393_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1___boxed(lean_object* v_treesSaved_3413_, lean_object* v___x_3414_, lean_object* v___x_3415_, lean_object* v___x_3416_, lean_object* v_mvarId_3417_, lean_object* v_s_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Lean_Elab_withInfoHole___redArg___lam__1(v_treesSaved_3413_, v___x_3414_, v___x_3415_, v___x_3416_, v_mvarId_3417_, v_s_3418_);
lean_dec_ref(v___x_3414_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object* v_modifyInfoState_3420_, lean_object* v___f_3421_, lean_object* v_x_3422_){
_start:
{
lean_object* v___x_3423_; 
v___x_3423_ = lean_apply_1(v_modifyInfoState_3420_, v___f_3421_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object* v_modifyInfoState_3424_, lean_object* v___f_3425_, lean_object* v_x_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_3424_, v___f_3425_, v_x_3426_);
lean_dec(v_x_3426_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object* v_toFunctor_3428_, lean_object* v___x_3429_, lean_object* v___x_3430_, lean_object* v___x_3431_, lean_object* v_mvarId_3432_, lean_object* v_modifyInfoState_3433_, lean_object* v_inst_3434_, lean_object* v_x_3435_, lean_object* v___f_3436_, lean_object* v_treesSaved_3437_){
_start:
{
lean_object* v_map_3438_; lean_object* v___f_3439_; lean_object* v___f_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v_map_3438_ = lean_ctor_get(v_toFunctor_3428_, 0);
lean_inc(v_map_3438_);
lean_dec_ref(v_toFunctor_3428_);
v___f_3439_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_3439_, 0, v_treesSaved_3437_);
lean_closure_set(v___f_3439_, 1, v___x_3429_);
lean_closure_set(v___f_3439_, 2, v___x_3430_);
lean_closure_set(v___f_3439_, 3, v___x_3431_);
lean_closure_set(v___f_3439_, 4, v_mvarId_3432_);
v___f_3440_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3440_, 0, v_modifyInfoState_3433_);
lean_closure_set(v___f_3440_, 1, v___f_3439_);
v___x_3441_ = lean_apply_4(v_inst_3434_, lean_box(0), lean_box(0), v_x_3435_, v___f_3440_);
v___x_3442_ = lean_apply_4(v_map_3438_, lean_box(0), lean_box(0), v___f_3436_, v___x_3441_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object* v_inst_3443_, lean_object* v_inst_3444_, lean_object* v_inst_3445_, lean_object* v_mvarId_3446_, lean_object* v_x_3447_){
_start:
{
lean_object* v_toApplicative_3448_; lean_object* v_toBind_3449_; lean_object* v_getInfoState_3450_; lean_object* v_modifyInfoState_3451_; lean_object* v_toFunctor_3452_; lean_object* v___f_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___f_3457_; lean_object* v___f_3458_; lean_object* v___x_3459_; 
v_toApplicative_3448_ = lean_ctor_get(v_inst_3444_, 0);
v_toBind_3449_ = lean_ctor_get(v_inst_3444_, 1);
lean_inc_n(v_toBind_3449_, 2);
v_getInfoState_3450_ = lean_ctor_get(v_inst_3445_, 0);
lean_inc(v_getInfoState_3450_);
v_modifyInfoState_3451_ = lean_ctor_get(v_inst_3445_, 1);
v_toFunctor_3452_ = lean_ctor_get(v_toApplicative_3448_, 0);
v___f_3453_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
v___x_3454_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3455_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3456_ = l_Lean_Elab_instInhabitedInfoTree_default;
lean_inc(v_x_3447_);
lean_inc(v_modifyInfoState_3451_);
lean_inc_ref(v_toFunctor_3452_);
v___f_3457_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3457_, 0, v_toFunctor_3452_);
lean_closure_set(v___f_3457_, 1, v___x_3456_);
lean_closure_set(v___f_3457_, 2, v___x_3454_);
lean_closure_set(v___f_3457_, 3, v___x_3455_);
lean_closure_set(v___f_3457_, 4, v_mvarId_3446_);
lean_closure_set(v___f_3457_, 5, v_modifyInfoState_3451_);
lean_closure_set(v___f_3457_, 6, v_inst_3443_);
lean_closure_set(v___f_3457_, 7, v_x_3447_);
lean_closure_set(v___f_3457_, 8, v___f_3453_);
v___f_3458_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3458_, 0, v_x_3447_);
lean_closure_set(v___f_3458_, 1, v_inst_3444_);
lean_closure_set(v___f_3458_, 2, v_inst_3445_);
lean_closure_set(v___f_3458_, 3, v_toBind_3449_);
lean_closure_set(v___f_3458_, 4, v___f_3457_);
v___x_3459_ = lean_apply_4(v_toBind_3449_, lean_box(0), lean_box(0), v_getInfoState_3450_, v___f_3458_);
return v___x_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object* v_m_3460_, lean_object* v_00_u03b1_3461_, lean_object* v_inst_3462_, lean_object* v_inst_3463_, lean_object* v_inst_3464_, lean_object* v_mvarId_3465_, lean_object* v_x_3466_){
_start:
{
lean_object* v_toApplicative_3467_; lean_object* v_toBind_3468_; lean_object* v_getInfoState_3469_; lean_object* v_modifyInfoState_3470_; lean_object* v_toFunctor_3471_; lean_object* v___f_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___f_3476_; lean_object* v___f_3477_; lean_object* v___x_3478_; 
v_toApplicative_3467_ = lean_ctor_get(v_inst_3463_, 0);
v_toBind_3468_ = lean_ctor_get(v_inst_3463_, 1);
lean_inc_n(v_toBind_3468_, 2);
v_getInfoState_3469_ = lean_ctor_get(v_inst_3464_, 0);
lean_inc(v_getInfoState_3469_);
v_modifyInfoState_3470_ = lean_ctor_get(v_inst_3464_, 1);
v_toFunctor_3471_ = lean_ctor_get(v_toApplicative_3467_, 0);
v___f_3472_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
v___x_3473_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3474_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3475_ = l_Lean_Elab_instInhabitedInfoTree_default;
lean_inc(v_x_3466_);
lean_inc(v_modifyInfoState_3470_);
lean_inc_ref(v_toFunctor_3471_);
v___f_3476_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3476_, 0, v_toFunctor_3471_);
lean_closure_set(v___f_3476_, 1, v___x_3475_);
lean_closure_set(v___f_3476_, 2, v___x_3473_);
lean_closure_set(v___f_3476_, 3, v___x_3474_);
lean_closure_set(v___f_3476_, 4, v_mvarId_3465_);
lean_closure_set(v___f_3476_, 5, v_modifyInfoState_3470_);
lean_closure_set(v___f_3476_, 6, v_inst_3462_);
lean_closure_set(v___f_3476_, 7, v_x_3466_);
lean_closure_set(v___f_3476_, 8, v___f_3472_);
v___f_3477_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3477_, 0, v_x_3466_);
lean_closure_set(v___f_3477_, 1, v_inst_3463_);
lean_closure_set(v___f_3477_, 2, v_inst_3464_);
lean_closure_set(v___f_3477_, 3, v_toBind_3468_);
lean_closure_set(v___f_3477_, 4, v___f_3476_);
v___x_3478_ = lean_apply_4(v_toBind_3468_, lean_box(0), lean_box(0), v_getInfoState_3469_, v___f_3477_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t v_flag_3479_, lean_object* v_s_3480_){
_start:
{
lean_object* v_assignment_3481_; lean_object* v_lazyAssignment_3482_; lean_object* v_trees_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
v_assignment_3481_ = lean_ctor_get(v_s_3480_, 0);
v_lazyAssignment_3482_ = lean_ctor_get(v_s_3480_, 1);
v_trees_3483_ = lean_ctor_get(v_s_3480_, 2);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_s_3480_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v_s_3480_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_trees_3483_);
lean_inc(v_lazyAssignment_3482_);
lean_inc(v_assignment_3481_);
lean_dec(v_s_3480_);
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
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_assignment_3481_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_lazyAssignment_3482_);
lean_ctor_set(v_reuseFailAlloc_3489_, 2, v_trees_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_ctor_set_uint8(v___x_3488_, sizeof(void*)*3, v_flag_3479_);
return v___x_3488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object* v_flag_3491_, lean_object* v_s_3492_){
_start:
{
uint8_t v_flag_boxed_3493_; lean_object* v_res_3494_; 
v_flag_boxed_3493_ = lean_unbox(v_flag_3491_);
v_res_3494_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_3493_, v_s_3492_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object* v_inst_3495_, uint8_t v_flag_3496_){
_start:
{
lean_object* v_modifyInfoState_3497_; lean_object* v___x_3498_; lean_object* v___f_3499_; lean_object* v___x_3500_; 
v_modifyInfoState_3497_ = lean_ctor_get(v_inst_3495_, 1);
lean_inc(v_modifyInfoState_3497_);
lean_dec_ref(v_inst_3495_);
v___x_3498_ = lean_box(v_flag_3496_);
v___f_3499_ = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3499_, 0, v___x_3498_);
v___x_3500_ = lean_apply_1(v_modifyInfoState_3497_, v___f_3499_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object* v_inst_3501_, lean_object* v_flag_3502_){
_start:
{
uint8_t v_flag_boxed_3503_; lean_object* v_res_3504_; 
v_flag_boxed_3503_ = lean_unbox(v_flag_3502_);
v_res_3504_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3501_, v_flag_boxed_3503_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object* v_m_3505_, lean_object* v_inst_3506_, uint8_t v_flag_3507_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3506_, v_flag_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object* v_m_3509_, lean_object* v_inst_3510_, lean_object* v_flag_3511_){
_start:
{
uint8_t v_flag_boxed_3512_; lean_object* v_res_3513_; 
v_flag_boxed_3512_ = lean_unbox(v_flag_3511_);
v_res_3513_ = l_Lean_Elab_enableInfoTree(v_m_3509_, v_inst_3510_, v_flag_boxed_3512_);
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object* v_x_3514_){
_start:
{
lean_object* v_fst_3515_; 
v_fst_3515_ = lean_ctor_get(v_x_3514_, 0);
lean_inc(v_fst_3515_);
return v_fst_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object* v_x_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_3516_);
lean_dec_ref(v_x_3516_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object* v_x_3518_, lean_object* v_____r_3519_){
_start:
{
lean_inc(v_x_3518_);
return v_x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object* v_x_3520_, lean_object* v_____r_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_3520_, v_____r_3521_);
lean_dec(v_x_3520_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object* v___x_3523_, lean_object* v_x_3524_){
_start:
{
lean_inc(v___x_3523_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object* v___x_3525_, lean_object* v_x_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_3525_, v_x_3526_);
lean_dec(v_x_3526_);
lean_dec(v___x_3525_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object* v_toFunctor_3528_, lean_object* v_inst_3529_, uint8_t v_flag_3530_, lean_object* v_toBind_3531_, lean_object* v___f_3532_, lean_object* v_inst_3533_, lean_object* v___f_3534_, lean_object* v_____do__lift_3535_){
_start:
{
uint8_t v_enabled_3536_; lean_object* v_map_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___f_3541_; lean_object* v_y_3542_; lean_object* v___x_3543_; 
v_enabled_3536_ = lean_ctor_get_uint8(v_____do__lift_3535_, sizeof(void*)*3);
v_map_3537_ = lean_ctor_get(v_toFunctor_3528_, 0);
lean_inc(v_map_3537_);
lean_dec_ref(v_toFunctor_3528_);
lean_inc_ref(v_inst_3529_);
v___x_3538_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3529_, v_flag_3530_);
v___x_3539_ = lean_apply_4(v_toBind_3531_, lean_box(0), lean_box(0), v___x_3538_, v___f_3532_);
v___x_3540_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3529_, v_enabled_3536_);
v___f_3541_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_3541_, 0, v___x_3540_);
v_y_3542_ = lean_apply_4(v_inst_3533_, lean_box(0), lean_box(0), v___x_3539_, v___f_3541_);
v___x_3543_ = lean_apply_4(v_map_3537_, lean_box(0), lean_box(0), v___f_3534_, v_y_3542_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object* v_toFunctor_3544_, lean_object* v_inst_3545_, lean_object* v_flag_3546_, lean_object* v_toBind_3547_, lean_object* v___f_3548_, lean_object* v_inst_3549_, lean_object* v___f_3550_, lean_object* v_____do__lift_3551_){
_start:
{
uint8_t v_flag_boxed_3552_; lean_object* v_res_3553_; 
v_flag_boxed_3552_ = lean_unbox(v_flag_3546_);
v_res_3553_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_3544_, v_inst_3545_, v_flag_boxed_3552_, v_toBind_3547_, v___f_3548_, v_inst_3549_, v___f_3550_, v_____do__lift_3551_);
lean_dec_ref(v_____do__lift_3551_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object* v_inst_3555_, lean_object* v_inst_3556_, lean_object* v_inst_3557_, uint8_t v_flag_3558_, lean_object* v_x_3559_){
_start:
{
lean_object* v_toApplicative_3560_; lean_object* v_toBind_3561_; lean_object* v_getInfoState_3562_; lean_object* v_toFunctor_3563_; lean_object* v___f_3564_; lean_object* v___f_3565_; lean_object* v___x_3566_; lean_object* v___f_3567_; lean_object* v___x_3568_; 
v_toApplicative_3560_ = lean_ctor_get(v_inst_3555_, 0);
lean_inc_ref(v_toApplicative_3560_);
v_toBind_3561_ = lean_ctor_get(v_inst_3555_, 1);
lean_inc_n(v_toBind_3561_, 2);
lean_dec_ref(v_inst_3555_);
v_getInfoState_3562_ = lean_ctor_get(v_inst_3556_, 0);
lean_inc(v_getInfoState_3562_);
v_toFunctor_3563_ = lean_ctor_get(v_toApplicative_3560_, 0);
lean_inc_ref(v_toFunctor_3563_);
lean_dec_ref(v_toApplicative_3560_);
v___f_3564_ = ((lean_object*)(l_Lean_Elab_withEnableInfoTree___redArg___closed__0));
v___f_3565_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3565_, 0, v_x_3559_);
v___x_3566_ = lean_box(v_flag_3558_);
v___f_3567_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_3567_, 0, v_toFunctor_3563_);
lean_closure_set(v___f_3567_, 1, v_inst_3556_);
lean_closure_set(v___f_3567_, 2, v___x_3566_);
lean_closure_set(v___f_3567_, 3, v_toBind_3561_);
lean_closure_set(v___f_3567_, 4, v___f_3565_);
lean_closure_set(v___f_3567_, 5, v_inst_3557_);
lean_closure_set(v___f_3567_, 6, v___f_3564_);
v___x_3568_ = lean_apply_4(v_toBind_3561_, lean_box(0), lean_box(0), v_getInfoState_3562_, v___f_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object* v_inst_3569_, lean_object* v_inst_3570_, lean_object* v_inst_3571_, lean_object* v_flag_3572_, lean_object* v_x_3573_){
_start:
{
uint8_t v_flag_boxed_3574_; lean_object* v_res_3575_; 
v_flag_boxed_3574_ = lean_unbox(v_flag_3572_);
v_res_3575_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3569_, v_inst_3570_, v_inst_3571_, v_flag_boxed_3574_, v_x_3573_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object* v_m_3576_, lean_object* v_00_u03b1_3577_, lean_object* v_inst_3578_, lean_object* v_inst_3579_, lean_object* v_inst_3580_, uint8_t v_flag_3581_, lean_object* v_x_3582_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3578_, v_inst_3579_, v_inst_3580_, v_flag_3581_, v_x_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object* v_m_3584_, lean_object* v_00_u03b1_3585_, lean_object* v_inst_3586_, lean_object* v_inst_3587_, lean_object* v_inst_3588_, lean_object* v_flag_3589_, lean_object* v_x_3590_){
_start:
{
uint8_t v_flag_boxed_3591_; lean_object* v_res_3592_; 
v_flag_boxed_3591_ = lean_unbox(v_flag_3589_);
v_res_3592_ = l_Lean_Elab_withEnableInfoTree(v_m_3584_, v_00_u03b1_3585_, v_inst_3586_, v_inst_3587_, v_inst_3588_, v_flag_boxed_3591_, v_x_3590_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object* v_toPure_3593_, lean_object* v_____do__lift_3594_){
_start:
{
lean_object* v_trees_3595_; lean_object* v___x_3596_; 
v_trees_3595_ = lean_ctor_get(v_____do__lift_3594_, 2);
lean_inc_ref(v_trees_3595_);
lean_dec_ref(v_____do__lift_3594_);
v___x_3596_ = lean_apply_2(v_toPure_3593_, lean_box(0), v_trees_3595_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object* v_inst_3597_, lean_object* v_inst_3598_){
_start:
{
lean_object* v_toApplicative_3599_; lean_object* v_toBind_3600_; lean_object* v_getInfoState_3601_; lean_object* v_toPure_3602_; lean_object* v___f_3603_; lean_object* v___x_3604_; 
v_toApplicative_3599_ = lean_ctor_get(v_inst_3598_, 0);
lean_inc_ref(v_toApplicative_3599_);
v_toBind_3600_ = lean_ctor_get(v_inst_3598_, 1);
lean_inc(v_toBind_3600_);
lean_dec_ref(v_inst_3598_);
v_getInfoState_3601_ = lean_ctor_get(v_inst_3597_, 0);
lean_inc(v_getInfoState_3601_);
lean_dec_ref(v_inst_3597_);
v_toPure_3602_ = lean_ctor_get(v_toApplicative_3599_, 1);
lean_inc(v_toPure_3602_);
lean_dec_ref(v_toApplicative_3599_);
v___f_3603_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3603_, 0, v_toPure_3602_);
v___x_3604_ = lean_apply_4(v_toBind_3600_, lean_box(0), lean_box(0), v_getInfoState_3601_, v___f_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object* v_m_3605_, lean_object* v_inst_3606_, lean_object* v_inst_3607_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_3606_, v_inst_3607_);
return v___x_3608_;
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
