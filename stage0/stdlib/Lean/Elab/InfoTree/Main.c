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
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = l_Lean_Options_empty;
v___x_199_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11));
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___x_198_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = l_Lean_NameSet_empty;
v___x_202_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6);
v___x_203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
lean_ctor_set(v___x_203_, 2, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; lean_object* v___x_207_; 
v___x_204_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6);
v___x_205_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9);
v___x_206_ = 1;
v___x_207_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_205_);
lean_ctor_set(v___x_207_, 2, v___x_204_);
lean_ctor_set_uint8(v___x_207_, sizeof(void*)*3, v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_211_ = l_Lean_maxRecDepth;
v___x_212_ = l_Lean_Options_empty;
v___x_213_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v___x_212_, v___x_211_);
return v___x_213_;
}
}
static uint16_t _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__19(void){
_start:
{
uint16_t v___x_214_; uint16_t v___x_215_; uint16_t v___x_216_; 
v___x_214_ = 512;
v___x_215_ = lean_uint16_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2);
v___x_216_ = lean_uint16_land(v___x_215_, v___x_214_);
return v___x_216_;
}
}
static uint8_t _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__20(void){
_start:
{
uint16_t v___x_217_; uint16_t v___x_218_; uint8_t v___x_219_; 
v___x_217_ = 0;
v___x_218_ = lean_uint16_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__19, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__19_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__19);
v___x_219_ = lean_uint16_dec_eq(v___x_218_, v___x_217_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg(lean_object* v_info_220_, lean_object* v_x_221_){
_start:
{
lean_object* v_a_224_; lean_object* v_toCommandContextInfo_227_; lean_object* v_env_228_; lean_object* v_options_229_; lean_object* v_currNamespace_230_; lean_object* v_openDecls_231_; lean_object* v_ngen_232_; uint8_t v___x_233_; lean_object* v_env_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint16_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___y_258_; lean_object* v___y_259_; uint16_t v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; uint8_t v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; uint16_t v___y_333_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v_fileName_368_; lean_object* v_fileMap_369_; lean_object* v_currNamespace_370_; lean_object* v_openDecls_371_; lean_object* v_initHeartbeats_372_; lean_object* v_maxHeartbeats_373_; lean_object* v_quotContext_374_; lean_object* v_currMacroScope_375_; lean_object* v_cancelTk_x3f_376_; lean_object* v_inheritedTraceOptions_377_; lean_object* v_currRecDepth_378_; lean_object* v_ref_379_; uint8_t v_suppressElabErrors_380_; uint8_t v_isRecordingDeps_381_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___y_390_; lean_object* v_env_411_; uint8_t v___x_412_; uint8_t v___x_413_; 
v_toCommandContextInfo_227_ = lean_ctor_get(v_info_220_, 0);
lean_inc_ref(v_toCommandContextInfo_227_);
lean_dec_ref(v_info_220_);
v_env_228_ = lean_ctor_get(v_toCommandContextInfo_227_, 0);
lean_inc_ref(v_env_228_);
v_options_229_ = lean_ctor_get(v_toCommandContextInfo_227_, 4);
lean_inc_ref(v_options_229_);
v_currNamespace_230_ = lean_ctor_get(v_toCommandContextInfo_227_, 5);
lean_inc(v_currNamespace_230_);
v_openDecls_231_ = lean_ctor_get(v_toCommandContextInfo_227_, 6);
lean_inc(v_openDecls_231_);
v_ngen_232_ = lean_ctor_get(v_toCommandContextInfo_227_, 7);
lean_inc_ref(v_ngen_232_);
lean_dec_ref(v_toCommandContextInfo_227_);
v___x_233_ = 0;
v_env_234_ = l_Lean_Environment_setExporting(v_env_228_, v___x_233_);
v___x_235_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0));
v___x_236_ = l_Lean_instInhabitedFileMap_default;
v___x_237_ = l_Lean_Options_empty;
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_240_ = lean_box(0);
v___x_241_ = l_Lean_firstFrontendMacroScope;
v___x_242_ = lean_box(0);
v___x_243_ = lean_box(0);
v___x_244_ = lean_uint16_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2);
v___x_245_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3);
v___x_246_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4));
v___x_247_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7);
v___x_248_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10);
v___x_249_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11));
v___x_250_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12);
v___x_251_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13);
v___x_252_ = 1;
v___x_253_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14);
v___x_254_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_254_, 0, v_env_234_);
lean_ctor_set(v___x_254_, 1, v___x_245_);
lean_ctor_set(v___x_254_, 2, v_ngen_232_);
lean_ctor_set(v___x_254_, 3, v___x_246_);
lean_ctor_set(v___x_254_, 4, v___x_247_);
lean_ctor_set(v___x_254_, 5, v___x_248_);
lean_ctor_set(v___x_254_, 6, v___x_250_);
lean_ctor_set(v___x_254_, 7, v___x_251_);
lean_ctor_set(v___x_254_, 8, v___x_253_);
lean_ctor_set(v___x_254_, 9, v___x_249_);
v___x_255_ = lean_io_get_num_heartbeats();
v___x_256_ = lean_st_mk_ref(v___x_254_);
v___x_386_ = l_Lean_inheritedTraceOptions;
v___x_387_ = lean_st_ref_get(v___x_386_);
v___x_388_ = lean_st_ref_get(v___x_256_);
v_env_411_ = lean_ctor_get(v___x_388_, 0);
lean_inc_ref(v_env_411_);
lean_dec(v___x_388_);
v___x_412_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_411_);
lean_dec_ref(v_env_411_);
v___x_413_ = lean_uint8_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__20, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__20_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__20);
if (v___x_413_ == 0)
{
if (v___x_412_ == 0)
{
v___y_390_ = v___x_252_;
goto v___jp_389_;
}
else
{
v_fileName_368_ = v___x_235_;
v_fileMap_369_ = v___x_236_;
v_currNamespace_370_ = v_currNamespace_230_;
v_openDecls_371_ = v_openDecls_231_;
v_initHeartbeats_372_ = v___x_255_;
v_maxHeartbeats_373_ = v___x_239_;
v_quotContext_374_ = v___x_240_;
v_currMacroScope_375_ = v___x_241_;
v_cancelTk_x3f_376_ = v___x_242_;
v_inheritedTraceOptions_377_ = v___x_387_;
v_currRecDepth_378_ = v___x_238_;
v_ref_379_ = v___x_243_;
v_suppressElabErrors_380_ = v___x_233_;
v_isRecordingDeps_381_ = v___x_233_;
goto v___jp_367_;
}
}
else
{
if (v___x_412_ == 0)
{
v_fileName_368_ = v___x_235_;
v_fileMap_369_ = v___x_236_;
v_currNamespace_370_ = v_currNamespace_230_;
v_openDecls_371_ = v_openDecls_231_;
v_initHeartbeats_372_ = v___x_255_;
v_maxHeartbeats_373_ = v___x_239_;
v_quotContext_374_ = v___x_240_;
v_currMacroScope_375_ = v___x_241_;
v_cancelTk_x3f_376_ = v___x_242_;
v_inheritedTraceOptions_377_ = v___x_387_;
v_currRecDepth_378_ = v___x_238_;
v_ref_379_ = v___x_243_;
v_suppressElabErrors_380_ = v___x_233_;
v_isRecordingDeps_381_ = v___x_233_;
goto v___jp_367_;
}
else
{
v___y_390_ = v___x_233_;
goto v___jp_389_;
}
}
v___jp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_mk_io_user_error(v_a_224_);
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
v___jp_257_:
{
lean_object* v_toCold_263_; lean_object* v_currRecDepth_264_; lean_object* v_ref_265_; uint8_t v_suppressElabErrors_266_; uint8_t v_isRecordingDeps_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_326_; 
v_toCold_263_ = lean_ctor_get(v___y_261_, 0);
v_currRecDepth_264_ = lean_ctor_get(v___y_261_, 1);
v_ref_265_ = lean_ctor_get(v___y_261_, 2);
v_suppressElabErrors_266_ = lean_ctor_get_uint8(v___y_261_, sizeof(void*)*3 + 2);
v_isRecordingDeps_267_ = lean_ctor_get_uint8(v___y_261_, sizeof(void*)*3 + 3);
v_isSharedCheck_326_ = !lean_is_exclusive(v___y_261_);
if (v_isSharedCheck_326_ == 0)
{
v___x_269_ = v___y_261_;
v_isShared_270_ = v_isSharedCheck_326_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_ref_265_);
lean_inc(v_currRecDepth_264_);
lean_inc(v_toCold_263_);
lean_dec(v___y_261_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_326_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v_fileName_271_; lean_object* v_fileMap_272_; lean_object* v_currNamespace_273_; lean_object* v_openDecls_274_; lean_object* v_initHeartbeats_275_; lean_object* v_maxHeartbeats_276_; lean_object* v_quotContext_277_; lean_object* v_currMacroScope_278_; lean_object* v_cancelTk_x3f_279_; lean_object* v_inheritedTraceOptions_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_323_; 
v_fileName_271_ = lean_ctor_get(v_toCold_263_, 0);
v_fileMap_272_ = lean_ctor_get(v_toCold_263_, 1);
v_currNamespace_273_ = lean_ctor_get(v_toCold_263_, 4);
v_openDecls_274_ = lean_ctor_get(v_toCold_263_, 5);
v_initHeartbeats_275_ = lean_ctor_get(v_toCold_263_, 6);
v_maxHeartbeats_276_ = lean_ctor_get(v_toCold_263_, 7);
v_quotContext_277_ = lean_ctor_get(v_toCold_263_, 8);
v_currMacroScope_278_ = lean_ctor_get(v_toCold_263_, 9);
v_cancelTk_x3f_279_ = lean_ctor_get(v_toCold_263_, 10);
v_inheritedTraceOptions_280_ = lean_ctor_get(v_toCold_263_, 11);
v_isSharedCheck_323_ = !lean_is_exclusive(v_toCold_263_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; lean_object* v_unused_325_; 
v_unused_324_ = lean_ctor_get(v_toCold_263_, 3);
lean_dec(v_unused_324_);
v_unused_325_ = lean_ctor_get(v_toCold_263_, 2);
lean_dec(v_unused_325_);
v___x_282_ = v_toCold_263_;
v_isShared_283_ = v_isSharedCheck_323_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_inheritedTraceOptions_280_);
lean_inc(v_cancelTk_x3f_279_);
lean_inc(v_currMacroScope_278_);
lean_inc(v_quotContext_277_);
lean_inc(v_maxHeartbeats_276_);
lean_inc(v_initHeartbeats_275_);
lean_inc(v_openDecls_274_);
lean_inc(v_currNamespace_273_);
lean_inc(v_fileMap_272_);
lean_inc(v_fileName_271_);
lean_dec(v_toCold_263_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_323_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_284_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v___y_258_, v___y_259_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 3, v___x_284_);
lean_ctor_set(v___x_282_, 2, v___y_258_);
v___x_286_ = v___x_282_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_fileName_271_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_fileMap_272_);
lean_ctor_set(v_reuseFailAlloc_322_, 2, v___y_258_);
lean_ctor_set(v_reuseFailAlloc_322_, 3, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_322_, 4, v_currNamespace_273_);
lean_ctor_set(v_reuseFailAlloc_322_, 5, v_openDecls_274_);
lean_ctor_set(v_reuseFailAlloc_322_, 6, v_initHeartbeats_275_);
lean_ctor_set(v_reuseFailAlloc_322_, 7, v_maxHeartbeats_276_);
lean_ctor_set(v_reuseFailAlloc_322_, 8, v_quotContext_277_);
lean_ctor_set(v_reuseFailAlloc_322_, 9, v_currMacroScope_278_);
lean_ctor_set(v_reuseFailAlloc_322_, 10, v_cancelTk_x3f_279_);
lean_ctor_set(v_reuseFailAlloc_322_, 11, v_inheritedTraceOptions_280_);
v___x_286_ = v_reuseFailAlloc_322_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_288_; 
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_286_);
v___x_288_ = v___x_269_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_currRecDepth_264_);
lean_ctor_set(v_reuseFailAlloc_321_, 2, v_ref_265_);
lean_ctor_set_uint8(v_reuseFailAlloc_321_, sizeof(void*)*3 + 2, v_suppressElabErrors_266_);
lean_ctor_set_uint8(v_reuseFailAlloc_321_, sizeof(void*)*3 + 3, v_isRecordingDeps_267_);
v___x_288_ = v_reuseFailAlloc_321_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; 
lean_ctor_set_uint16(v___x_288_, sizeof(void*)*3, v___y_260_);
v___x_289_ = lean_apply_3(v_x_221_, v___x_288_, v___y_262_, lean_box(0));
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_298_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_298_ == 0)
{
v___x_292_ = v___x_289_;
v_isShared_293_ = v_isSharedCheck_298_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_298_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_294_ = lean_st_ref_get(v___x_256_);
lean_dec(v___x_256_);
lean_dec(v___x_294_);
if (v_isShared_293_ == 0)
{
v___x_296_ = v___x_292_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_290_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_320_; 
lean_dec(v___x_256_);
v_a_299_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_320_ == 0)
{
v___x_301_ = v___x_289_;
v_isShared_302_ = v_isSharedCheck_320_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_289_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_320_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
if (lean_obj_tag(v_a_299_) == 0)
{
lean_object* v_msg_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v_msg_303_ = lean_ctor_get(v_a_299_, 1);
lean_inc_ref(v_msg_303_);
lean_dec_ref_known(v_a_299_, 2);
v___x_304_ = l_Lean_MessageData_toString(v_msg_303_);
v___x_305_ = lean_mk_io_user_error(v___x_304_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_305_);
v___x_307_ = v___x_301_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
else
{
lean_object* v_id_309_; lean_object* v___x_310_; 
lean_del_object(v___x_301_);
v_id_309_ = lean_ctor_get(v_a_299_, 0);
lean_inc(v_id_309_);
lean_dec_ref_known(v_a_299_, 2);
v___x_310_ = l_Lean_InternalExceptionId_getName(v_id_309_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec(v_id_309_);
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref_known(v___x_310_, 1);
v___x_312_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15));
v___x_313_ = l_Lean_Name_toString(v_a_311_, v___x_252_);
v___x_314_ = lean_string_append(v___x_312_, v___x_313_);
lean_dec_ref(v___x_313_);
v_a_224_ = v___x_314_;
goto v___jp_223_;
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec_ref_known(v___x_310_, 1);
v___x_315_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16));
v___x_316_ = l_Nat_reprFast(v_id_309_);
v___x_317_ = lean_string_append(v___x_315_, v___x_316_);
lean_dec_ref(v___x_316_);
v___x_318_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17));
v___x_319_ = lean_string_append(v___x_317_, v___x_318_);
v_a_224_ = v___x_319_;
goto v___jp_223_;
}
}
}
}
}
}
}
}
}
v___jp_327_:
{
lean_object* v___x_334_; lean_object* v_env_335_; lean_object* v_nextMacroScope_336_; lean_object* v_ngen_337_; lean_object* v_auxDeclNGen_338_; lean_object* v_traceState_339_; lean_object* v_recordedDeps_340_; lean_object* v_messages_341_; lean_object* v_infoState_342_; lean_object* v_snapshotTasks_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_352_; 
v___x_334_ = lean_st_ref_take(v___y_330_);
v_env_335_ = lean_ctor_get(v___x_334_, 0);
v_nextMacroScope_336_ = lean_ctor_get(v___x_334_, 1);
v_ngen_337_ = lean_ctor_get(v___x_334_, 2);
v_auxDeclNGen_338_ = lean_ctor_get(v___x_334_, 3);
v_traceState_339_ = lean_ctor_get(v___x_334_, 4);
v_recordedDeps_340_ = lean_ctor_get(v___x_334_, 6);
v_messages_341_ = lean_ctor_get(v___x_334_, 7);
v_infoState_342_ = lean_ctor_get(v___x_334_, 8);
v_snapshotTasks_343_ = lean_ctor_get(v___x_334_, 9);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_352_ == 0)
{
lean_object* v_unused_353_; 
v_unused_353_ = lean_ctor_get(v___x_334_, 5);
lean_dec(v_unused_353_);
v___x_345_ = v___x_334_;
v_isShared_346_ = v_isSharedCheck_352_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_snapshotTasks_343_);
lean_inc(v_infoState_342_);
lean_inc(v_messages_341_);
lean_inc(v_recordedDeps_340_);
lean_inc(v_traceState_339_);
lean_inc(v_auxDeclNGen_338_);
lean_inc(v_ngen_337_);
lean_inc(v_nextMacroScope_336_);
lean_inc(v_env_335_);
lean_dec(v___x_334_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_352_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_347_ = l_Lean_Kernel_enableDiag(v_env_335_, v___y_328_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 5, v___x_248_);
lean_ctor_set(v___x_345_, 0, v___x_347_);
v___x_349_ = v___x_345_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_nextMacroScope_336_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v_ngen_337_);
lean_ctor_set(v_reuseFailAlloc_351_, 3, v_auxDeclNGen_338_);
lean_ctor_set(v_reuseFailAlloc_351_, 4, v_traceState_339_);
lean_ctor_set(v_reuseFailAlloc_351_, 5, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_351_, 6, v_recordedDeps_340_);
lean_ctor_set(v_reuseFailAlloc_351_, 7, v_messages_341_);
lean_ctor_set(v_reuseFailAlloc_351_, 8, v_infoState_342_);
lean_ctor_set(v_reuseFailAlloc_351_, 9, v_snapshotTasks_343_);
v___x_349_ = v_reuseFailAlloc_351_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_350_; 
v___x_350_ = lean_st_ref_put(v___y_330_, v___x_349_);
v___y_258_ = v___y_331_;
v___y_259_ = v___y_332_;
v___y_260_ = v___y_333_;
v___y_261_ = v___y_329_;
v___y_262_ = v___y_330_;
goto v___jp_257_;
}
}
}
v___jp_354_:
{
uint16_t v___x_359_; lean_object* v___x_360_; lean_object* v_env_361_; uint8_t v___x_362_; uint16_t v___x_363_; uint16_t v___x_364_; uint16_t v___x_365_; uint8_t v___x_366_; 
v___x_359_ = l_Lean_OptionFlags_ofOptions(v___y_358_);
v___x_360_ = lean_st_ref_get(v___y_356_);
v_env_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc_ref(v_env_361_);
lean_dec(v___x_360_);
v___x_362_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_361_);
lean_dec_ref(v_env_361_);
v___x_363_ = 512;
v___x_364_ = lean_uint16_land(v___x_359_, v___x_363_);
v___x_365_ = 0;
v___x_366_ = lean_uint16_dec_eq(v___x_364_, v___x_365_);
if (v___x_366_ == 0)
{
if (v___x_362_ == 0)
{
v___y_328_ = v___x_252_;
v___y_329_ = v___y_355_;
v___y_330_ = v___y_356_;
v___y_331_ = v___y_358_;
v___y_332_ = v___y_357_;
v___y_333_ = v___x_359_;
goto v___jp_327_;
}
else
{
v___y_258_ = v___y_358_;
v___y_259_ = v___y_357_;
v___y_260_ = v___x_359_;
v___y_261_ = v___y_355_;
v___y_262_ = v___y_356_;
goto v___jp_257_;
}
}
else
{
if (v___x_362_ == 0)
{
v___y_258_ = v___y_358_;
v___y_259_ = v___y_357_;
v___y_260_ = v___x_359_;
v___y_261_ = v___y_355_;
v___y_262_ = v___y_356_;
goto v___jp_257_;
}
else
{
v___y_328_ = v___x_233_;
v___y_329_ = v___y_355_;
v___y_330_ = v___y_356_;
v___y_331_ = v___y_358_;
v___y_332_ = v___y_357_;
v___y_333_ = v___x_359_;
goto v___jp_327_;
}
}
}
v___jp_367_:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_382_ = l_Lean_maxRecDepth;
v___x_383_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18);
lean_inc(v_cancelTk_x3f_376_);
lean_inc(v_currMacroScope_375_);
lean_inc(v_quotContext_374_);
lean_inc(v_maxHeartbeats_373_);
lean_inc_ref(v_fileMap_369_);
lean_inc_ref(v_fileName_368_);
v___x_384_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_384_, 0, v_fileName_368_);
lean_ctor_set(v___x_384_, 1, v_fileMap_369_);
lean_ctor_set(v___x_384_, 2, v___x_237_);
lean_ctor_set(v___x_384_, 3, v___x_383_);
lean_ctor_set(v___x_384_, 4, v_currNamespace_370_);
lean_ctor_set(v___x_384_, 5, v_openDecls_371_);
lean_ctor_set(v___x_384_, 6, v_initHeartbeats_372_);
lean_ctor_set(v___x_384_, 7, v_maxHeartbeats_373_);
lean_ctor_set(v___x_384_, 8, v_quotContext_374_);
lean_ctor_set(v___x_384_, 9, v_currMacroScope_375_);
lean_ctor_set(v___x_384_, 10, v_cancelTk_x3f_376_);
lean_ctor_set(v___x_384_, 11, v_inheritedTraceOptions_377_);
lean_inc(v_ref_379_);
v___x_385_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v_currRecDepth_378_);
lean_ctor_set(v___x_385_, 2, v_ref_379_);
lean_ctor_set_uint16(v___x_385_, sizeof(void*)*3, v___x_244_);
lean_ctor_set_uint8(v___x_385_, sizeof(void*)*3 + 2, v_suppressElabErrors_380_);
lean_ctor_set_uint8(v___x_385_, sizeof(void*)*3 + 3, v_isRecordingDeps_381_);
lean_inc(v___x_256_);
v___y_355_ = v___x_385_;
v___y_356_ = v___x_256_;
v___y_357_ = v___x_382_;
v___y_358_ = v_options_229_;
goto v___jp_354_;
}
v___jp_389_:
{
lean_object* v___x_391_; lean_object* v_env_392_; lean_object* v_nextMacroScope_393_; lean_object* v_ngen_394_; lean_object* v_auxDeclNGen_395_; lean_object* v_traceState_396_; lean_object* v_recordedDeps_397_; lean_object* v_messages_398_; lean_object* v_infoState_399_; lean_object* v_snapshotTasks_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_409_; 
v___x_391_ = lean_st_ref_take(v___x_256_);
v_env_392_ = lean_ctor_get(v___x_391_, 0);
v_nextMacroScope_393_ = lean_ctor_get(v___x_391_, 1);
v_ngen_394_ = lean_ctor_get(v___x_391_, 2);
v_auxDeclNGen_395_ = lean_ctor_get(v___x_391_, 3);
v_traceState_396_ = lean_ctor_get(v___x_391_, 4);
v_recordedDeps_397_ = lean_ctor_get(v___x_391_, 6);
v_messages_398_ = lean_ctor_get(v___x_391_, 7);
v_infoState_399_ = lean_ctor_get(v___x_391_, 8);
v_snapshotTasks_400_ = lean_ctor_get(v___x_391_, 9);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v___x_391_, 5);
lean_dec(v_unused_410_);
v___x_402_ = v___x_391_;
v_isShared_403_ = v_isSharedCheck_409_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_snapshotTasks_400_);
lean_inc(v_infoState_399_);
lean_inc(v_messages_398_);
lean_inc(v_recordedDeps_397_);
lean_inc(v_traceState_396_);
lean_inc(v_auxDeclNGen_395_);
lean_inc(v_ngen_394_);
lean_inc(v_nextMacroScope_393_);
lean_inc(v_env_392_);
lean_dec(v___x_391_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_409_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = l_Lean_Kernel_enableDiag(v_env_392_, v___y_390_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 5, v___x_248_);
lean_ctor_set(v___x_402_, 0, v___x_404_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_nextMacroScope_393_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_ngen_394_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_auxDeclNGen_395_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v_traceState_396_);
lean_ctor_set(v_reuseFailAlloc_408_, 5, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_408_, 6, v_recordedDeps_397_);
lean_ctor_set(v_reuseFailAlloc_408_, 7, v_messages_398_);
lean_ctor_set(v_reuseFailAlloc_408_, 8, v_infoState_399_);
lean_ctor_set(v_reuseFailAlloc_408_, 9, v_snapshotTasks_400_);
v___x_406_ = v_reuseFailAlloc_408_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; 
v___x_407_ = lean_st_ref_put(v___x_256_, v___x_406_);
v_fileName_368_ = v___x_235_;
v_fileMap_369_ = v___x_236_;
v_currNamespace_370_ = v_currNamespace_230_;
v_openDecls_371_ = v_openDecls_231_;
v_initHeartbeats_372_ = v___x_255_;
v_maxHeartbeats_373_ = v___x_239_;
v_quotContext_374_ = v___x_240_;
v_currMacroScope_375_ = v___x_241_;
v_cancelTk_x3f_376_ = v___x_242_;
v_inheritedTraceOptions_377_ = v___x_387_;
v_currRecDepth_378_ = v___x_238_;
v_ref_379_ = v___x_243_;
v_suppressElabErrors_380_ = v___x_233_;
v_isRecordingDeps_381_ = v___x_233_;
goto v___jp_367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___boxed(lean_object* v_info_414_, lean_object* v_x_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_414_, v_x_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM(lean_object* v_00_u03b1_418_, lean_object* v_info_419_, lean_object* v_x_420_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_419_, v_x_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___boxed(lean_object* v_00_u03b1_423_, lean_object* v_info_424_, lean_object* v_x_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Elab_ContextInfo_runCoreM(v_00_u03b1_423_, v_info_424_, v_x_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(lean_object* v___x_428_, lean_object* v_x_429_, lean_object* v___x_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_st_mk_ref(v___x_428_);
lean_inc(v___x_434_);
v___x_435_ = lean_apply_5(v_x_429_, v___x_430_, v___x_434_, v___y_431_, v___y_432_, lean_box(0));
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_445_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_445_ == 0)
{
v___x_438_ = v___x_435_;
v_isShared_439_ = v_isSharedCheck_445_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_445_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_440_ = lean_st_ref_get(v___x_434_);
lean_dec(v___x_434_);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v_a_436_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_441_);
v___x_443_ = v___x_438_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec(v___x_434_);
v_a_446_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_435_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_435_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed(lean_object* v___x_454_, lean_object* v_x_455_, lean_object* v___x_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(v___x_454_, v_x_455_, v___x_456_, v___y_457_, v___y_458_);
return v_res_460_;
}
}
static uint64_t _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1(void){
_start:
{
lean_object* v___x_467_; uint64_t v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_468_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_467_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2(void){
_start:
{
uint64_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_uint64_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1);
v___x_470_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_471_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set_uint64(v___x_471_, sizeof(void*)*1, v___x_469_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_477_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
lean_ctor_set(v___x_477_, 2, v___x_476_);
lean_ctor_set(v___x_477_, 3, v___x_476_);
lean_ctor_set(v___x_477_, 4, v___x_476_);
lean_ctor_set(v___x_477_, 5, v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_unsigned_to_nat(32u);
v___x_479_ = lean_mk_empty_array_with_capacity(v___x_478_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7(void){
_start:
{
size_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_481_ = ((size_t)5ULL);
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = lean_unsigned_to_nat(32u);
v___x_484_ = lean_mk_empty_array_with_capacity(v___x_483_);
v___x_485_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6);
v___x_486_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_484_);
lean_ctor_set(v___x_486_, 2, v___x_482_);
lean_ctor_set(v___x_486_, 3, v___x_482_);
lean_ctor_set_usize(v___x_486_, 4, v___x_481_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
lean_ctor_set(v___x_488_, 2, v___x_487_);
lean_ctor_set(v___x_488_, 3, v___x_487_);
lean_ctor_set(v___x_488_, 4, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object* v_info_489_, lean_object* v_lctx_490_, lean_object* v_x_491_){
_start:
{
lean_object* v___x_493_; uint8_t v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v_toCommandContextInfo_501_; lean_object* v_mctx_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___f_507_; lean_object* v___x_508_; 
v___x_493_ = lean_box(1);
v___x_494_ = 0;
v___x_495_ = 1;
v___x_496_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2);
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3));
v___x_499_ = lean_box(0);
v___x_500_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_500_, 0, v___x_496_);
lean_ctor_set(v___x_500_, 1, v___x_493_);
lean_ctor_set(v___x_500_, 2, v_lctx_490_);
lean_ctor_set(v___x_500_, 3, v___x_498_);
lean_ctor_set(v___x_500_, 4, v___x_499_);
lean_ctor_set(v___x_500_, 5, v___x_497_);
lean_ctor_set(v___x_500_, 6, v___x_499_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*7, v___x_494_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*7 + 1, v___x_494_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*7 + 2, v___x_494_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*7 + 3, v___x_495_);
v_toCommandContextInfo_501_ = lean_ctor_get(v_info_489_, 0);
v_mctx_502_ = lean_ctor_get(v_toCommandContextInfo_501_, 3);
v___x_503_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_504_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7);
v___x_505_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8);
lean_inc_ref(v_mctx_502_);
v___x_506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_506_, 0, v_mctx_502_);
lean_ctor_set(v___x_506_, 1, v___x_503_);
lean_ctor_set(v___x_506_, 2, v___x_493_);
lean_ctor_set(v___x_506_, 3, v___x_504_);
lean_ctor_set(v___x_506_, 4, v___x_505_);
v___f_507_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_507_, 0, v___x_506_);
lean_closure_set(v___f_507_, 1, v_x_491_);
lean_closure_set(v___f_507_, 2, v___x_500_);
v___x_508_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_489_, v___f_507_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_517_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_517_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_517_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_517_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_fst_513_; lean_object* v___x_515_; 
v_fst_513_ = lean_ctor_get(v_a_509_, 0);
lean_inc(v_fst_513_);
lean_dec(v_a_509_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v_fst_513_);
v___x_515_ = v___x_511_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_fst_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
v_a_518_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_508_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_508_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object* v_info_526_, lean_object* v_lctx_527_, lean_object* v_x_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_526_, v_lctx_527_, v_x_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object* v_00_u03b1_531_, lean_object* v_info_532_, lean_object* v_lctx_533_, lean_object* v_x_534_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_532_, v_lctx_533_, v_x_534_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object* v_00_u03b1_537_, lean_object* v_info_538_, lean_object* v_lctx_539_, lean_object* v_x_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_Elab_ContextInfo_runMetaM(v_00_u03b1_537_, v_info_538_, v_lctx_539_, v_x_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object* v_info_543_, lean_object* v_lctx_544_){
_start:
{
lean_object* v_toCommandContextInfo_545_; lean_object* v_env_546_; lean_object* v_mctx_547_; lean_object* v_options_548_; lean_object* v_currNamespace_549_; lean_object* v_openDecls_550_; lean_object* v___x_551_; 
v_toCommandContextInfo_545_ = lean_ctor_get(v_info_543_, 0);
v_env_546_ = lean_ctor_get(v_toCommandContextInfo_545_, 0);
v_mctx_547_ = lean_ctor_get(v_toCommandContextInfo_545_, 3);
v_options_548_ = lean_ctor_get(v_toCommandContextInfo_545_, 4);
v_currNamespace_549_ = lean_ctor_get(v_toCommandContextInfo_545_, 5);
v_openDecls_550_ = lean_ctor_get(v_toCommandContextInfo_545_, 6);
lean_inc(v_openDecls_550_);
lean_inc(v_currNamespace_549_);
lean_inc_ref(v_options_548_);
lean_inc_ref(v_mctx_547_);
lean_inc_ref(v_env_546_);
v___x_551_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_551_, 0, v_env_546_);
lean_ctor_set(v___x_551_, 1, v_mctx_547_);
lean_ctor_set(v___x_551_, 2, v_lctx_544_);
lean_ctor_set(v___x_551_, 3, v_options_548_);
lean_ctor_set(v___x_551_, 4, v_currNamespace_549_);
lean_ctor_set(v___x_551_, 5, v_openDecls_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object* v_info_552_, lean_object* v_lctx_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_552_, v_lctx_553_);
lean_dec_ref(v_info_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object* v_info_555_, lean_object* v_lctx_556_, lean_object* v_stx_557_){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_555_, v_lctx_556_);
v___x_560_ = l_Lean_ppTerm(v___x_559_, v_stx_557_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object* v_info_562_, lean_object* v_lctx_563_, lean_object* v_stx_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Elab_ContextInfo_ppSyntax(v_info_562_, v_lctx_563_, v_stx_564_);
lean_dec_ref(v_info_562_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(lean_object* v_ctx_582_, lean_object* v_pos_583_, lean_object* v_info_584_){
_start:
{
lean_object* v_toCommandContextInfo_585_; lean_object* v_fileMap_586_; lean_object* v___x_587_; lean_object* v_line_588_; lean_object* v_column_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_612_; 
v_toCommandContextInfo_585_ = lean_ctor_get(v_ctx_582_, 0);
lean_inc_ref(v_toCommandContextInfo_585_);
lean_dec_ref(v_ctx_582_);
v_fileMap_586_ = lean_ctor_get(v_toCommandContextInfo_585_, 2);
lean_inc_ref(v_fileMap_586_);
lean_dec_ref(v_toCommandContextInfo_585_);
v___x_587_ = l_Lean_FileMap_toPosition(v_fileMap_586_, v_pos_583_);
v_line_588_ = lean_ctor_get(v___x_587_, 0);
v_column_589_ = lean_ctor_get(v___x_587_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_612_ == 0)
{
v___x_591_ = v___x_587_;
v_isShared_592_ = v_isSharedCheck_612_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_column_589_);
lean_inc(v_line_588_);
lean_dec(v___x_587_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_612_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_593_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_594_ = l_Nat_reprFast(v_line_588_);
v___x_595_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
if (v_isShared_592_ == 0)
{
lean_ctor_set_tag(v___x_591_, 5);
lean_ctor_set(v___x_591_, 1, v___x_595_);
lean_ctor_set(v___x_591_, 0, v___x_593_);
v___x_597_ = v___x_591_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v___x_595_);
v___x_597_ = v_reuseFailAlloc_611_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v_pos_604_; 
v___x_598_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
v___x_599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = l_Nat_reprFast(v_column_589_);
v___x_601_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
v___x_602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_599_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v_pos_604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_pos_604_, 0, v___x_602_);
lean_ctor_set(v_pos_604_, 1, v___x_603_);
switch(lean_obj_tag(v_info_584_))
{
case 0:
{
return v_pos_604_;
}
case 1:
{
uint8_t v_canonical_608_; 
v_canonical_608_ = lean_ctor_get_uint8(v_info_584_, sizeof(void*)*2);
if (v_canonical_608_ == 1)
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9));
v___x_610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_610_, 0, v_pos_604_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
return v___x_610_;
}
else
{
goto v___jp_605_;
}
}
default: 
{
goto v___jp_605_;
}
}
v___jp_605_:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7));
v___x_607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_607_, 0, v_pos_604_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
return v___x_607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(lean_object* v_ctx_613_, lean_object* v_pos_614_, lean_object* v_info_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_613_, v_pos_614_, v_info_615_);
lean_dec(v_info_615_);
lean_dec(v_pos_614_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(lean_object* v_ctx_620_, lean_object* v_stx_621_){
_start:
{
lean_object* v___y_623_; lean_object* v___y_624_; uint8_t v___x_632_; lean_object* v___y_634_; lean_object* v___x_637_; 
v___x_632_ = 0;
v___x_637_ = l_Lean_Syntax_getPos_x3f(v_stx_621_, v___x_632_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v___x_638_; 
v___x_638_ = lean_unsigned_to_nat(0u);
v___y_634_ = v___x_638_;
goto v___jp_633_;
}
else
{
lean_object* v_val_639_; 
v_val_639_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_val_639_);
lean_dec_ref_known(v___x_637_, 1);
v___y_634_ = v_val_639_;
goto v___jp_633_;
}
v___jp_622_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_625_ = l_Lean_Syntax_getHeadInfo(v_stx_621_);
lean_inc_ref(v_ctx_620_);
v___x_626_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_620_, v___y_623_, v___x_625_);
lean_dec(v___x_625_);
lean_dec(v___y_623_);
v___x_627_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = l_Lean_Syntax_getTailInfo(v_stx_621_);
v___x_630_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_620_, v___y_624_, v___x_629_);
lean_dec(v___x_629_);
lean_dec(v___y_624_);
v___x_631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_628_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
return v___x_631_;
}
v___jp_633_:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Syntax_getTailPos_x3f(v_stx_621_, v___x_632_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_inc(v___y_634_);
v___y_623_ = v___y_634_;
v___y_624_ = v___y_634_;
goto v___jp_622_;
}
else
{
lean_object* v_val_636_; 
v_val_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_val_636_);
lean_dec_ref_known(v___x_635_, 1);
v___y_623_ = v___y_634_;
v___y_624_ = v_val_636_;
goto v___jp_622_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(lean_object* v_ctx_640_, lean_object* v_stx_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_640_, v_stx_641_);
lean_dec(v_stx_641_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(lean_object* v_ctx_646_, lean_object* v_info_647_){
_start:
{
lean_object* v_elaborator_648_; lean_object* v_stx_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_664_; 
v_elaborator_648_ = lean_ctor_get(v_info_647_, 0);
v_stx_649_ = lean_ctor_get(v_info_647_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_info_647_);
if (v_isSharedCheck_664_ == 0)
{
v___x_651_ = v_info_647_;
v_isShared_652_ = v_isSharedCheck_664_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_stx_649_);
lean_inc(v_elaborator_648_);
lean_dec(v_info_647_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_664_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
uint8_t v___x_653_; 
v___x_653_ = l_Lean_Name_isAnonymous(v_elaborator_648_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_654_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_646_, v_stx_649_);
lean_dec(v_stx_649_);
v___x_655_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
if (v_isShared_652_ == 0)
{
lean_ctor_set_tag(v___x_651_, 5);
lean_ctor_set(v___x_651_, 1, v___x_655_);
lean_ctor_set(v___x_651_, 0, v___x_654_);
v___x_657_ = v___x_651_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v___x_655_);
v___x_657_ = v_reuseFailAlloc_662_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_658_ = 1;
v___x_659_ = l_Lean_Name_toString(v_elaborator_648_, v___x_658_);
v___x_660_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
v___x_661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_657_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
return v___x_661_;
}
}
else
{
lean_object* v___x_663_; 
lean_del_object(v___x_651_);
lean_dec(v_elaborator_648_);
v___x_663_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_646_, v_stx_649_);
lean_dec(v_stx_649_);
return v___x_663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object* v_info_665_, lean_object* v_ctx_666_, lean_object* v_x_667_){
_start:
{
lean_object* v_lctx_669_; lean_object* v___x_670_; 
v_lctx_669_ = lean_ctor_get(v_info_665_, 1);
lean_inc_ref(v_lctx_669_);
lean_dec_ref(v_info_665_);
v___x_670_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_666_, v_lctx_669_, v_x_667_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(lean_object* v_info_671_, lean_object* v_ctx_672_, lean_object* v_x_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_671_, v_ctx_672_, v_x_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM(lean_object* v_00_u03b1_676_, lean_object* v_info_677_, lean_object* v_ctx_678_, lean_object* v_x_679_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_677_, v_ctx_678_, v_x_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___boxed(lean_object* v_00_u03b1_682_, lean_object* v_info_683_, lean_object* v_ctx_684_, lean_object* v_x_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Elab_TermInfo_runMetaM(v_00_u03b1_682_, v_info_683_, v_ctx_684_, v_x_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0(lean_object* v_ctx_702_, lean_object* v_toElabInfo_703_, lean_object* v_expr_704_, uint8_t v_isBinder_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v_a_726_; lean_object* v___y_736_; uint8_t v___y_737_; lean_object* v___y_740_; lean_object* v_a_741_; lean_object* v___x_744_; 
lean_inc(v___y_709_);
lean_inc_ref(v___y_708_);
lean_inc(v___y_707_);
lean_inc_ref(v___y_706_);
lean_inc_ref(v_expr_704_);
v___x_744_ = lean_infer_type(v_expr_704_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_746_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 1);
v___x_746_ = l_Lean_Meta_ppExpr(v_a_745_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v_a_726_ = v_a_747_;
goto v___jp_725_;
}
else
{
lean_object* v_a_748_; 
v_a_748_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_748_);
v___y_740_ = v___x_746_;
v_a_741_ = v_a_748_;
goto v___jp_739_;
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
v_a_749_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_744_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_744_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
lean_inc(v_a_749_);
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
v___y_740_ = v___x_754_;
v_a_741_ = v_a_749_;
goto v___jp_739_;
}
}
}
v___jp_711_:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
lean_inc_ref(v___y_714_);
v___x_715_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_715_, 0, v___y_714_);
v___x_716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_716_, 0, v___y_713_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v___y_712_);
v___x_720_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_702_, v_toElabInfo_703_);
v___x_723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
v___jp_725_:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Meta_ppExpr(v_expr_704_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_727_, 1);
v___x_729_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__3));
v___x_730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v_a_728_);
v___x_731_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
v___x_732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
if (v_isBinder_705_ == 0)
{
lean_object* v___x_733_; 
v___x_733_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__6));
v___y_712_ = v_a_726_;
v___y_713_ = v___x_732_;
v___y_714_ = v___x_733_;
goto v___jp_711_;
}
else
{
lean_object* v___x_734_; 
v___x_734_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__7));
v___y_712_ = v_a_726_;
v___y_713_ = v___x_732_;
v___y_714_ = v___x_734_;
goto v___jp_711_;
}
}
else
{
lean_dec(v_a_726_);
lean_dec_ref(v_toElabInfo_703_);
lean_dec_ref(v_ctx_702_);
return v___x_727_;
}
}
v___jp_735_:
{
if (v___y_737_ == 0)
{
lean_object* v___x_738_; 
lean_dec_ref(v___y_736_);
v___x_738_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__9));
v_a_726_ = v___x_738_;
goto v___jp_725_;
}
else
{
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v_expr_704_);
lean_dec_ref(v_toElabInfo_703_);
lean_dec_ref(v_ctx_702_);
return v___y_736_;
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
v___y_736_ = v___y_740_;
v___y_737_ = v___x_743_;
goto v___jp_735_;
}
else
{
lean_dec_ref(v_a_741_);
v___y_736_ = v___y_740_;
v___y_737_ = v___x_742_;
goto v___jp_735_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0___boxed(lean_object* v_ctx_757_, lean_object* v_toElabInfo_758_, lean_object* v_expr_759_, lean_object* v_isBinder_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
uint8_t v_isBinder_boxed_766_; lean_object* v_res_767_; 
v_isBinder_boxed_766_ = lean_unbox(v_isBinder_760_);
v_res_767_ = l_Lean_Elab_TermInfo_format___lam__0(v_ctx_757_, v_toElabInfo_758_, v_expr_759_, v_isBinder_boxed_766_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format(lean_object* v_ctx_768_, lean_object* v_info_769_){
_start:
{
lean_object* v_toElabInfo_771_; lean_object* v_expr_772_; uint8_t v_isBinder_773_; lean_object* v___x_774_; lean_object* v___f_775_; lean_object* v___x_776_; 
v_toElabInfo_771_ = lean_ctor_get(v_info_769_, 0);
v_expr_772_ = lean_ctor_get(v_info_769_, 3);
v_isBinder_773_ = lean_ctor_get_uint8(v_info_769_, sizeof(void*)*4);
v___x_774_ = lean_box(v_isBinder_773_);
lean_inc_ref(v_expr_772_);
lean_inc_ref(v_toElabInfo_771_);
lean_inc_ref(v_ctx_768_);
v___f_775_ = lean_alloc_closure((void*)(l_Lean_Elab_TermInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_775_, 0, v_ctx_768_);
lean_closure_set(v___f_775_, 1, v_toElabInfo_771_);
lean_closure_set(v___f_775_, 2, v_expr_772_);
lean_closure_set(v___f_775_, 3, v___x_774_);
v___x_776_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_769_, v_ctx_768_, v___f_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___boxed(lean_object* v_ctx_777_, lean_object* v_info_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_Elab_TermInfo_format(v_ctx_777_, v_info_778_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialTermInfo_format(lean_object* v_ctx_784_, lean_object* v_info_785_){
_start:
{
lean_object* v_toElabInfo_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v_toElabInfo_786_ = lean_ctor_get(v_info_785_, 0);
lean_inc_ref(v_toElabInfo_786_);
lean_dec_ref(v_info_785_);
v___x_787_ = ((lean_object*)(l_Lean_Elab_PartialTermInfo_format___closed__1));
v___x_788_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_784_, v_toElabInfo_786_);
v___x_789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(lean_object* v_x_796_){
_start:
{
if (lean_obj_tag(v_x_796_) == 0)
{
lean_object* v___x_797_; 
v___x_797_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_797_;
}
else
{
lean_object* v_val_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_808_; 
v_val_798_ = lean_ctor_get(v_x_796_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v_x_796_);
if (v_isSharedCheck_808_ == 0)
{
v___x_800_ = v_x_796_;
v_isShared_801_ = v_isSharedCheck_808_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_val_798_);
lean_dec(v_x_796_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_808_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_802_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_803_ = lean_expr_dbg_to_string(v_val_798_);
lean_dec(v_val_798_);
if (v_isShared_801_ == 0)
{
lean_ctor_set_tag(v___x_800_, 3);
lean_ctor_set(v___x_800_, 0, v___x_803_);
v___x_805_ = v___x_800_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_807_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; 
v___x_806_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_802_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
return v___x_806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0(lean_object* v_ctx_815_, lean_object* v_lctx_816_, lean_object* v_stx_817_, lean_object* v_expectedType_x3f_818_, lean_object* v_info_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v___x_825_; lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_844_; 
v___x_825_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_815_, v_lctx_816_, v_stx_817_);
v_a_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_844_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_844_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_844_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_830_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__1));
v___x_831_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v_a_826_);
v___x_832_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_831_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_818_);
v___x_835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = l_Lean_Elab_CompletionInfo_stx(v_info_819_);
v___x_839_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_815_, v___x_838_);
lean_dec(v___x_838_);
v___x_840_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_837_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_840_);
v___x_842_ = v___x_828_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___boxed(lean_object* v_ctx_845_, lean_object* v_lctx_846_, lean_object* v_stx_847_, lean_object* v_expectedType_x3f_848_, lean_object* v_info_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Elab_CompletionInfo_format___lam__0(v_ctx_845_, v_lctx_846_, v_stx_847_, v_expectedType_x3f_848_, v_info_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec_ref(v_info_849_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format(lean_object* v_ctx_862_, lean_object* v_info_863_){
_start:
{
switch(lean_obj_tag(v_info_863_))
{
case 0:
{
lean_object* v_termInfo_865_; lean_object* v_expectedType_x3f_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_887_; 
v_termInfo_865_ = lean_ctor_get(v_info_863_, 0);
v_expectedType_x3f_866_ = lean_ctor_get(v_info_863_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v_info_863_);
if (v_isSharedCheck_887_ == 0)
{
v___x_868_ = v_info_863_;
v_isShared_869_ = v_isSharedCheck_887_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_expectedType_x3f_866_);
lean_inc(v_termInfo_865_);
lean_dec(v_info_863_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_887_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Elab_TermInfo_format(v_ctx_862_, v_termInfo_865_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_886_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_886_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_886_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_886_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_875_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__1));
if (v_isShared_869_ == 0)
{
lean_ctor_set_tag(v___x_868_, 5);
lean_ctor_set(v___x_868_, 1, v_a_871_);
lean_ctor_set(v___x_868_, 0, v___x_875_);
v___x_877_ = v___x_868_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_a_871_);
v___x_877_ = v_reuseFailAlloc_885_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_878_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_866_);
v___x_881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_881_);
v___x_883_ = v___x_873_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_del_object(v___x_868_);
lean_dec(v_expectedType_x3f_866_);
return v___x_870_;
}
}
}
case 1:
{
lean_object* v_stx_888_; lean_object* v_lctx_889_; lean_object* v_expectedType_x3f_890_; lean_object* v___f_891_; lean_object* v___x_892_; 
v_stx_888_ = lean_ctor_get(v_info_863_, 0);
lean_inc(v_stx_888_);
v_lctx_889_ = lean_ctor_get(v_info_863_, 2);
lean_inc_ref_n(v_lctx_889_, 2);
v_expectedType_x3f_890_ = lean_ctor_get(v_info_863_, 3);
lean_inc(v_expectedType_x3f_890_);
lean_inc_ref(v_ctx_862_);
v___f_891_ = lean_alloc_closure((void*)(l_Lean_Elab_CompletionInfo_format___lam__0___boxed), 10, 5);
lean_closure_set(v___f_891_, 0, v_ctx_862_);
lean_closure_set(v___f_891_, 1, v_lctx_889_);
lean_closure_set(v___f_891_, 2, v_stx_888_);
lean_closure_set(v___f_891_, 3, v_expectedType_x3f_890_);
lean_closure_set(v___f_891_, 4, v_info_863_);
v___x_892_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_862_, v_lctx_889_, v___f_891_);
return v___x_892_;
}
default: 
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_893_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__3));
v___x_894_ = l_Lean_Elab_CompletionInfo_stx(v_info_863_);
lean_dec_ref(v_info_863_);
v___x_895_ = lean_box(0);
v___x_896_ = 0;
lean_inc(v___x_894_);
v___x_897_ = l_Lean_Syntax_formatStx(v___x_894_, v___x_895_, v___x_896_);
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_893_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_862_, v___x_894_);
lean_dec(v___x_894_);
v___x_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
return v___x_903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___boxed(lean_object* v_ctx_904_, lean_object* v_info_905_, lean_object* v_a_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_Elab_CompletionInfo_format(v_ctx_904_, v_info_905_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format(lean_object* v_ctx_911_, lean_object* v_info_912_){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_914_ = ((lean_object*)(l_Lean_Elab_CommandInfo_format___closed__1));
v___x_915_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_911_, v_info_912_);
v___x_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format___boxed(lean_object* v_ctx_918_, lean_object* v_info_919_, lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Elab_CommandInfo_format(v_ctx_918_, v_info_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format(lean_object* v_ctx_925_, lean_object* v_info_926_){
_start:
{
lean_object* v_stx_928_; lean_object* v_optionName_929_; lean_object* v___x_930_; uint8_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v_stx_928_ = lean_ctor_get(v_info_926_, 0);
lean_inc(v_stx_928_);
v_optionName_929_ = lean_ctor_get(v_info_926_, 1);
lean_inc(v_optionName_929_);
lean_dec_ref(v_info_926_);
v___x_930_ = ((lean_object*)(l_Lean_Elab_OptionInfo_format___closed__1));
v___x_931_ = 1;
v___x_932_ = l_Lean_Name_toString(v_optionName_929_, v___x_931_);
v___x_933_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
v___x_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_930_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_925_, v_stx_928_);
lean_dec(v_stx_928_);
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format___boxed(lean_object* v_ctx_940_, lean_object* v_info_941_, lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Elab_OptionInfo_format(v_ctx_940_, v_info_941_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format(lean_object* v_ctx_947_, lean_object* v_info_948_){
_start:
{
lean_object* v_stx_950_; lean_object* v_errorName_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_967_; 
v_stx_950_ = lean_ctor_get(v_info_948_, 0);
v_errorName_951_ = lean_ctor_get(v_info_948_, 1);
v_isSharedCheck_967_ = !lean_is_exclusive(v_info_948_);
if (v_isSharedCheck_967_ == 0)
{
v___x_953_ = v_info_948_;
v_isShared_954_ = v_isSharedCheck_967_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_errorName_951_);
lean_inc(v_stx_950_);
lean_dec(v_info_948_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_967_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; uint8_t v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_955_ = ((lean_object*)(l_Lean_Elab_ErrorNameInfo_format___closed__1));
v___x_956_ = 1;
v___x_957_ = l_Lean_Name_toString(v_errorName_951_, v___x_956_);
v___x_958_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
if (v_isShared_954_ == 0)
{
lean_ctor_set_tag(v___x_953_, 5);
lean_ctor_set(v___x_953_, 1, v___x_958_);
lean_ctor_set(v___x_953_, 0, v___x_955_);
v___x_960_ = v___x_953_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v___x_958_);
v___x_960_ = v_reuseFailAlloc_966_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_961_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_947_, v_stx_950_);
lean_dec(v_stx_950_);
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format___boxed(lean_object* v_ctx_968_, lean_object* v_info_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_968_, v_info_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0(lean_object* v_val_978_, lean_object* v_fieldName_979_, lean_object* v_ctx_980_, lean_object* v_stx_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; 
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc_ref(v_val_978_);
v___x_987_ = lean_infer_type(v_val_978_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_989_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = l_Lean_Meta_ppExpr(v_a_988_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1020_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1020_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1020_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_Meta_ppExpr(v_val_978_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1019_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1019_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1019_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; uint8_t v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_999_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__1));
v___x_1000_ = 1;
v___x_1001_ = l_Lean_Name_toString(v_fieldName_979_, v___x_1000_);
if (v_isShared_993_ == 0)
{
lean_ctor_set_tag(v___x_992_, 3);
lean_ctor_set(v___x_992_, 0, v___x_1001_);
v___x_1003_ = v___x_992_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_999_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1004_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v_a_990_);
v___x_1008_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__3));
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v_a_995_);
v___x_1011_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_980_, v_stx_981_);
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1014_);
v___x_1016_ = v___x_997_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
else
{
lean_del_object(v___x_992_);
lean_dec(v_a_990_);
lean_dec_ref(v_ctx_980_);
lean_dec(v_fieldName_979_);
return v___x_994_;
}
}
}
else
{
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec_ref(v_ctx_980_);
lean_dec(v_fieldName_979_);
lean_dec_ref(v_val_978_);
return v___x_989_;
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec_ref(v_ctx_980_);
lean_dec(v_fieldName_979_);
lean_dec_ref(v_val_978_);
v_a_1021_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_987_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_987_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0___boxed(lean_object* v_val_1029_, lean_object* v_fieldName_1030_, lean_object* v_ctx_1031_, lean_object* v_stx_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Elab_FieldInfo_format___lam__0(v_val_1029_, v_fieldName_1030_, v_ctx_1031_, v_stx_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v_stx_1032_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format(lean_object* v_ctx_1039_, lean_object* v_info_1040_){
_start:
{
lean_object* v_fieldName_1042_; lean_object* v_lctx_1043_; lean_object* v_val_1044_; lean_object* v_stx_1045_; lean_object* v___f_1046_; lean_object* v___x_1047_; 
v_fieldName_1042_ = lean_ctor_get(v_info_1040_, 1);
lean_inc(v_fieldName_1042_);
v_lctx_1043_ = lean_ctor_get(v_info_1040_, 2);
lean_inc_ref(v_lctx_1043_);
v_val_1044_ = lean_ctor_get(v_info_1040_, 3);
lean_inc_ref(v_val_1044_);
v_stx_1045_ = lean_ctor_get(v_info_1040_, 4);
lean_inc(v_stx_1045_);
lean_dec_ref(v_info_1040_);
lean_inc_ref(v_ctx_1039_);
v___f_1046_ = lean_alloc_closure((void*)(l_Lean_Elab_FieldInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1046_, 0, v_val_1044_);
lean_closure_set(v___f_1046_, 1, v_fieldName_1042_);
lean_closure_set(v___f_1046_, 2, v_ctx_1039_);
lean_closure_set(v___f_1046_, 3, v_stx_1045_);
v___x_1047_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1039_, v_lctx_1043_, v___f_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___boxed(lean_object* v_ctx_1048_, lean_object* v_info_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_Elab_FieldInfo_format(v_ctx_1048_, v_info_1049_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(lean_object* v_pre_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
if (lean_obj_tag(v_x_1054_) == 0)
{
lean_dec(v_pre_1052_);
return v_x_1053_;
}
else
{
lean_object* v_head_1055_; lean_object* v_tail_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1065_; 
v_head_1055_ = lean_ctor_get(v_x_1054_, 0);
v_tail_1056_ = lean_ctor_get(v_x_1054_, 1);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_x_1054_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1058_ = v_x_1054_;
v_isShared_1059_ = v_isSharedCheck_1065_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_tail_1056_);
lean_inc(v_head_1055_);
lean_dec(v_x_1054_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1065_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
lean_inc(v_pre_1052_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 5);
lean_ctor_set(v___x_1058_, 1, v_pre_1052_);
lean_ctor_set(v___x_1058_, 0, v_x_1053_);
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_x_1053_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_pre_1052_);
v___x_1061_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v_head_1055_);
v_x_1053_ = v___x_1062_;
v_x_1054_ = v_tail_1056_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(lean_object* v_pre_1066_, lean_object* v_x_1067_){
_start:
{
if (lean_obj_tag(v_x_1067_) == 0)
{
lean_object* v___x_1068_; 
lean_dec(v_pre_1066_);
v___x_1068_ = lean_box(0);
return v___x_1068_;
}
else
{
lean_object* v_head_1069_; lean_object* v_tail_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1078_; 
v_head_1069_ = lean_ctor_get(v_x_1067_, 0);
v_tail_1070_ = lean_ctor_get(v_x_1067_, 1);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_x_1067_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1072_ = v_x_1067_;
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_tail_1070_);
lean_inc(v_head_1069_);
lean_dec(v_x_1067_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
lean_inc(v_pre_1066_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set_tag(v___x_1072_, 5);
lean_ctor_set(v___x_1072_, 1, v_head_1069_);
lean_ctor_set(v___x_1072_, 0, v_pre_1066_);
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_pre_1066_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_head_1069_);
v___x_1075_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(v_pre_1066_, v___x_1075_, v_tail_1070_);
return v___x_1076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(lean_object* v_x_1079_, lean_object* v_x_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
if (lean_obj_tag(v_x_1079_) == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = l_List_reverse___redArg(v_x_1080_);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
return v___x_1087_;
}
else
{
lean_object* v_head_1088_; lean_object* v_tail_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1107_; 
v_head_1088_ = lean_ctor_get(v_x_1079_, 0);
v_tail_1089_ = lean_ctor_get(v_x_1079_, 1);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_x_1079_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1091_ = v_x_1079_;
v_isShared_1092_ = v_isSharedCheck_1107_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_tail_1089_);
lean_inc(v_head_1088_);
lean_dec(v_x_1079_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1107_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_Meta_ppGoal(v_head_1088_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v_head_1088_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1096_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 1);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 1, v_x_1080_);
lean_ctor_set(v___x_1091_, 0, v_a_1094_);
v___x_1096_ = v___x_1091_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1094_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_x_1080_);
v___x_1096_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
v_x_1079_ = v_tail_1089_;
v_x_1080_ = v___x_1096_;
goto _start;
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_del_object(v___x_1091_);
lean_dec(v_tail_1089_);
lean_dec(v_x_1080_);
v_a_1099_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1093_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1093_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(lean_object* v_x_1108_, lean_object* v_x_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_x_1108_, v_x_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0(lean_object* v_goals_1119_, lean_object* v___x_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_goals_1119_, v___x_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1136_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1129_ = v___x_1126_;
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1131_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1132_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1131_, v_a_1127_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1132_);
v___x_1134_ = v___x_1129_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
v_a_1137_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1126_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1126_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(lean_object* v_goals_1145_, lean_object* v___x_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0(v_goals_1145_, v___x_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
return v_res_1152_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = lean_unsigned_to_nat(32u);
v___x_1156_ = lean_mk_empty_array_with_capacity(v___x_1155_);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2(void){
_start:
{
size_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1158_ = ((size_t)5ULL);
v___x_1159_ = lean_unsigned_to_nat(0u);
v___x_1160_ = lean_unsigned_to_nat(32u);
v___x_1161_ = lean_mk_empty_array_with_capacity(v___x_1160_);
v___x_1162_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__1, &l_Lean_Elab_ContextInfo_ppGoals___closed__1_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1);
v___x_1163_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
lean_ctor_set(v___x_1163_, 1, v___x_1161_);
lean_ctor_set(v___x_1163_, 2, v___x_1159_);
lean_ctor_set(v___x_1163_, 3, v___x_1159_);
lean_ctor_set_usize(v___x_1163_, 4, v___x_1158_);
return v___x_1163_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1164_ = lean_box(1);
v___x_1165_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_1166_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__0, &l_Lean_Elab_ContextInfo_ppGoals___closed__0_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0);
v___x_1167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
lean_ctor_set(v___x_1167_, 1, v___x_1165_);
lean_ctor_set(v___x_1167_, 2, v___x_1164_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object* v_ctx_1171_, lean_object* v_goals_1172_){
_start:
{
uint8_t v___x_1174_; 
v___x_1174_ = l_List_isEmpty___redArg(v_goals_1172_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___f_1177_; lean_object* v___x_1178_; 
v___x_1175_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_1176_ = lean_box(0);
v___f_1177_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1177_, 0, v_goals_1172_);
lean_closure_set(v___f_1177_, 1, v___x_1176_);
v___x_1178_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1171_, v___x_1175_, v___f_1177_);
return v___x_1178_;
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec(v_goals_1172_);
lean_dec_ref(v_ctx_1171_);
v___x_1179_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___closed__5));
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object* v_ctx_1181_, lean_object* v_goals_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctx_1181_, v_goals_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format(lean_object* v_ctx_1194_, lean_object* v_info_1195_){
_start:
{
lean_object* v_toCommandContextInfo_1197_; lean_object* v_parentDecl_x3f_1198_; lean_object* v_autoImplicits_1199_; lean_object* v_env_1200_; lean_object* v_cmdEnv_x3f_1201_; lean_object* v_fileMap_1202_; lean_object* v_options_1203_; lean_object* v_currNamespace_1204_; lean_object* v_openDecls_1205_; lean_object* v_ngen_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1248_; 
v_toCommandContextInfo_1197_ = lean_ctor_get(v_ctx_1194_, 0);
lean_inc_ref(v_toCommandContextInfo_1197_);
v_parentDecl_x3f_1198_ = lean_ctor_get(v_ctx_1194_, 1);
v_autoImplicits_1199_ = lean_ctor_get(v_ctx_1194_, 2);
v_env_1200_ = lean_ctor_get(v_toCommandContextInfo_1197_, 0);
v_cmdEnv_x3f_1201_ = lean_ctor_get(v_toCommandContextInfo_1197_, 1);
v_fileMap_1202_ = lean_ctor_get(v_toCommandContextInfo_1197_, 2);
v_options_1203_ = lean_ctor_get(v_toCommandContextInfo_1197_, 4);
v_currNamespace_1204_ = lean_ctor_get(v_toCommandContextInfo_1197_, 5);
v_openDecls_1205_ = lean_ctor_get(v_toCommandContextInfo_1197_, 6);
v_ngen_1206_ = lean_ctor_get(v_toCommandContextInfo_1197_, 7);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_toCommandContextInfo_1197_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v_toCommandContextInfo_1197_, 3);
lean_dec(v_unused_1249_);
v___x_1208_ = v_toCommandContextInfo_1197_;
v_isShared_1209_ = v_isSharedCheck_1248_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_ngen_1206_);
lean_inc(v_openDecls_1205_);
lean_inc(v_currNamespace_1204_);
lean_inc(v_options_1203_);
lean_inc(v_fileMap_1202_);
lean_inc(v_cmdEnv_x3f_1201_);
lean_inc(v_env_1200_);
lean_dec(v_toCommandContextInfo_1197_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1248_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v_toElabInfo_1210_; lean_object* v_mctxBefore_1211_; lean_object* v_goalsBefore_1212_; lean_object* v_mctxAfter_1213_; lean_object* v_goalsAfter_1214_; lean_object* v___x_1216_; 
v_toElabInfo_1210_ = lean_ctor_get(v_info_1195_, 0);
lean_inc_ref(v_toElabInfo_1210_);
v_mctxBefore_1211_ = lean_ctor_get(v_info_1195_, 1);
lean_inc_ref(v_mctxBefore_1211_);
v_goalsBefore_1212_ = lean_ctor_get(v_info_1195_, 2);
lean_inc(v_goalsBefore_1212_);
v_mctxAfter_1213_ = lean_ctor_get(v_info_1195_, 3);
lean_inc_ref(v_mctxAfter_1213_);
v_goalsAfter_1214_ = lean_ctor_get(v_info_1195_, 4);
lean_inc(v_goalsAfter_1214_);
lean_dec_ref(v_info_1195_);
lean_inc_ref(v_ngen_1206_);
lean_inc(v_openDecls_1205_);
lean_inc(v_currNamespace_1204_);
lean_inc_ref(v_options_1203_);
lean_inc_ref(v_fileMap_1202_);
lean_inc(v_cmdEnv_x3f_1201_);
lean_inc_ref(v_env_1200_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 3, v_mctxBefore_1211_);
v___x_1216_ = v___x_1208_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_env_1200_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_cmdEnv_x3f_1201_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v_fileMap_1202_);
lean_ctor_set(v_reuseFailAlloc_1247_, 3, v_mctxBefore_1211_);
lean_ctor_set(v_reuseFailAlloc_1247_, 4, v_options_1203_);
lean_ctor_set(v_reuseFailAlloc_1247_, 5, v_currNamespace_1204_);
lean_ctor_set(v_reuseFailAlloc_1247_, 6, v_openDecls_1205_);
lean_ctor_set(v_reuseFailAlloc_1247_, 7, v_ngen_1206_);
v___x_1216_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v_ctxB_1217_; lean_object* v___x_1218_; lean_object* v_ctxA_1219_; lean_object* v___x_1220_; 
lean_inc_ref_n(v_autoImplicits_1199_, 2);
lean_inc_n(v_parentDecl_x3f_1198_, 2);
v_ctxB_1217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxB_1217_, 0, v___x_1216_);
lean_ctor_set(v_ctxB_1217_, 1, v_parentDecl_x3f_1198_);
lean_ctor_set(v_ctxB_1217_, 2, v_autoImplicits_1199_);
v___x_1218_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1218_, 0, v_env_1200_);
lean_ctor_set(v___x_1218_, 1, v_cmdEnv_x3f_1201_);
lean_ctor_set(v___x_1218_, 2, v_fileMap_1202_);
lean_ctor_set(v___x_1218_, 3, v_mctxAfter_1213_);
lean_ctor_set(v___x_1218_, 4, v_options_1203_);
lean_ctor_set(v___x_1218_, 5, v_currNamespace_1204_);
lean_ctor_set(v___x_1218_, 6, v_openDecls_1205_);
lean_ctor_set(v___x_1218_, 7, v_ngen_1206_);
v_ctxA_1219_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxA_1219_, 0, v___x_1218_);
lean_ctor_set(v_ctxA_1219_, 1, v_parentDecl_x3f_1198_);
lean_ctor_set(v_ctxA_1219_, 2, v_autoImplicits_1199_);
v___x_1220_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxB_1217_, v_goalsBefore_1212_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1222_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1220_, 1);
v___x_1222_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxA_1219_, v_goalsAfter_1214_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1246_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1246_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1246_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v_stx_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
v_stx_1227_ = lean_ctor_get(v_toElabInfo_1210_, 1);
lean_inc(v_stx_1227_);
v___x_1228_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__1));
v___x_1229_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1194_, v_toElabInfo_1210_);
v___x_1230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1228_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___x_1231_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = lean_box(0);
v___x_1234_ = 0;
v___x_1235_ = l_Lean_Syntax_formatStx(v_stx_1227_, v___x_1233_, v___x_1234_);
v___x_1236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1232_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
v___x_1237_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__3));
v___x_1238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1236_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
v___x_1239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
lean_ctor_set(v___x_1239_, 1, v_a_1221_);
v___x_1240_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__5));
v___x_1241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v_a_1223_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1242_);
v___x_1244_ = v___x_1225_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
else
{
lean_dec(v_a_1221_);
lean_dec_ref(v_toElabInfo_1210_);
lean_dec_ref(v_ctx_1194_);
return v___x_1222_;
}
}
else
{
lean_dec_ref_known(v_ctxA_1219_, 3);
lean_dec(v_goalsAfter_1214_);
lean_dec_ref(v_toElabInfo_1210_);
lean_dec_ref(v_ctx_1194_);
return v___x_1220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format___boxed(lean_object* v_ctx_1250_, lean_object* v_info_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_Elab_TacticInfo_format(v_ctx_1250_, v_info_1251_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object* v_ctx_1260_, lean_object* v_info_1261_){
_start:
{
lean_object* v_lctx_1263_; lean_object* v_stx_1264_; lean_object* v_output_1265_; lean_object* v___x_1266_; lean_object* v_a_1267_; lean_object* v___x_1268_; lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1281_; 
v_lctx_1263_ = lean_ctor_get(v_info_1261_, 0);
lean_inc_ref_n(v_lctx_1263_, 2);
v_stx_1264_ = lean_ctor_get(v_info_1261_, 1);
lean_inc(v_stx_1264_);
v_output_1265_ = lean_ctor_get(v_info_1261_, 2);
lean_inc(v_output_1265_);
lean_dec_ref(v_info_1261_);
v___x_1266_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1260_, v_lctx_1263_, v_stx_1264_);
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref(v___x_1266_);
v___x_1268_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1260_, v_lctx_1263_, v_output_1265_);
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1281_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1281_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1273_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__1));
v___x_1274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set(v___x_1274_, 1, v_a_1267_);
v___x_1275_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__3));
v___x_1276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1274_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v_a_1269_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1277_);
v___x_1279_ = v___x_1271_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object* v_ctx_1282_, lean_object* v_info_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1282_, v_info_1283_);
lean_dec_ref(v_ctx_1282_);
return v_res_1285_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__0(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
return v___x_1287_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__1(void){
_start:
{
uint8_t v___x_1288_; size_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1288_ = 1;
v___x_1289_ = ((size_t)0ULL);
v___x_1290_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__0, &l_Lean_Elab_UserWidgetInfo_format___closed__0_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__0);
v___x_1291_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
lean_ctor_set_usize(v___x_1291_, 2, v___x_1289_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*3, v___x_1288_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_UserWidgetInfo_format(lean_object* v_info_1295_){
_start:
{
lean_object* v_toWidgetInstance_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1325_; 
v_toWidgetInstance_1296_ = lean_ctor_get(v_info_1295_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_info_1295_);
if (v_isSharedCheck_1325_ == 0)
{
lean_object* v_unused_1326_; 
v_unused_1326_ = lean_ctor_get(v_info_1295_, 1);
lean_dec(v_unused_1326_);
v___x_1298_ = v_info_1295_;
v_isShared_1299_ = v_isSharedCheck_1325_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_toWidgetInstance_1296_);
lean_dec(v_info_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1325_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v_id_1300_; lean_object* v_props_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v_fst_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1323_; 
v_id_1300_ = lean_ctor_get(v_toWidgetInstance_1296_, 0);
lean_inc(v_id_1300_);
v_props_1301_ = lean_ctor_get(v_toWidgetInstance_1296_, 1);
lean_inc_ref(v_props_1301_);
lean_dec_ref(v_toWidgetInstance_1296_);
v___x_1302_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__1, &l_Lean_Elab_UserWidgetInfo_format___closed__1_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__1);
v___x_1303_ = lean_apply_1(v_props_1301_, v___x_1302_);
v_fst_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; 
v_unused_1324_ = lean_ctor_get(v___x_1303_, 1);
lean_dec(v_unused_1324_);
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1323_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_fst_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1323_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; uint8_t v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1308_ = ((lean_object*)(l_Lean_Elab_UserWidgetInfo_format___closed__3));
v___x_1309_ = 1;
v___x_1310_ = l_Lean_Name_toString(v_id_1300_, v___x_1309_);
v___x_1311_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set_tag(v___x_1306_, 5);
lean_ctor_set(v___x_1306_, 1, v___x_1311_);
lean_ctor_set(v___x_1306_, 0, v___x_1308_);
v___x_1313_ = v___x_1306_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1308_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
if (v_isShared_1299_ == 0)
{
lean_ctor_set_tag(v___x_1298_, 5);
lean_ctor_set(v___x_1298_, 1, v___x_1314_);
lean_ctor_set(v___x_1298_, 0, v___x_1313_);
v___x_1316_ = v___x_1298_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1317_ = lean_unsigned_to_nat(80u);
v___x_1318_ = l_Lean_Json_pretty(v_fst_1304_, v___x_1317_);
v___x_1319_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
v___x_1320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1316_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
return v___x_1320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FVarAliasInfo_format(lean_object* v_info_1333_){
_start:
{
lean_object* v_userName_1334_; lean_object* v_id_1335_; lean_object* v_baseId_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v_userName_1334_ = lean_ctor_get(v_info_1333_, 0);
lean_inc(v_userName_1334_);
v_id_1335_ = lean_ctor_get(v_info_1333_, 1);
lean_inc(v_id_1335_);
v_baseId_1336_ = lean_ctor_get(v_info_1333_, 2);
lean_inc(v_baseId_1336_);
lean_dec_ref(v_info_1333_);
v___x_1337_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__1));
v___x_1338_ = l_Lean_Name_eraseMacroScopes(v_userName_1334_);
lean_dec(v_userName_1334_);
v___x_1339_ = 1;
v___x_1340_ = l_Lean_Name_toString(v___x_1338_, v___x_1339_);
v___x_1341_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
v___x_1342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1337_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_1344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1342_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
v___x_1345_ = l_Lean_Name_toString(v_id_1335_, v___x_1339_);
v___x_1346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
v___x_1347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1344_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__3));
v___x_1349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1347_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
v___x_1350_ = l_Lean_Name_toString(v_baseId_1336_, v___x_1339_);
v___x_1351_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
v___x_1352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1349_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format(lean_object* v_ctx_1356_, lean_object* v_info_1357_){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1358_ = ((lean_object*)(l_Lean_Elab_FieldRedeclInfo_format___closed__1));
v___x_1359_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1356_, v_info_1357_);
v___x_1360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format___boxed(lean_object* v_ctx_1361_, lean_object* v_info_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1361_, v_info_1362_);
lean_dec(v_info_1362_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f(lean_object* v_ppCtx_1366_, lean_object* v_info_1367_){
_start:
{
lean_object* v_mkDocString_x3f_1369_; 
v_mkDocString_x3f_1369_ = lean_ctor_get(v_info_1367_, 2);
lean_inc(v_mkDocString_x3f_1369_);
lean_dec_ref(v_info_1367_);
if (lean_obj_tag(v_mkDocString_x3f_1369_) == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
lean_dec_ref(v_ppCtx_1366_);
v___x_1370_ = lean_box(0);
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
return v___x_1371_;
}
else
{
lean_object* v_val_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1404_; 
v_val_1372_ = lean_ctor_get(v_mkDocString_x3f_1369_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_mkDocString_x3f_1369_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1374_ = v_mkDocString_x3f_1369_;
v_isShared_1375_ = v_isSharedCheck_1404_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_val_1372_);
lean_dec(v_mkDocString_x3f_1369_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1404_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_apply_2(v_val_1372_, v_ppCtx_1366_, lean_box(0));
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1387_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1387_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1387_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v_a_1377_);
v___x_1382_ = v___x_1374_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1384_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1382_);
v___x_1384_ = v___x_1379_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1403_; 
v_a_1388_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1390_ = v___x_1376_;
v_isShared_1391_ = v_isSharedCheck_1403_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1376_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1403_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1392_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0));
v___x_1393_ = lean_io_error_to_string(v_a_1388_);
v___x_1394_ = lean_string_append(v___x_1392_, v___x_1393_);
lean_dec_ref(v___x_1393_);
v___x_1395_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1396_ = lean_string_append(v___x_1394_, v___x_1395_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1396_);
v___x_1398_ = v___x_1374_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1400_; 
if (v_isShared_1391_ == 0)
{
lean_ctor_set_tag(v___x_1390_, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1398_);
v___x_1400_ = v___x_1390_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___boxed(lean_object* v_ppCtx_1405_, lean_object* v_info_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_ppCtx_1405_, v_info_1406_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(lean_object* v_x_1409_, lean_object* v_x_1410_){
_start:
{
if (lean_obj_tag(v_x_1409_) == 0)
{
lean_object* v___x_1411_; 
v___x_1411_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_1411_;
}
else
{
lean_object* v_val_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1423_; 
v_val_1412_ = lean_ctor_get(v_x_1409_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_x_1409_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1414_ = v_x_1409_;
v_isShared_1415_ = v_isSharedCheck_1423_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_val_1412_);
lean_dec(v_x_1409_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1423_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1416_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_1417_ = l_String_quote(v_val_1412_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set_tag(v___x_1414_, 3);
lean_ctor_set(v___x_1414_, 0, v___x_1417_);
v___x_1419_ = v___x_1414_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1416_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = l_Repr_addAppParen(v___x_1420_, v_x_1410_);
return v___x_1421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(lean_object* v_x_1424_, lean_object* v_x_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_x_1424_, v_x_1425_);
lean_dec(v_x_1425_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object* v_ctx_1441_, lean_object* v_info_1442_){
_start:
{
lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v_toTermInfo_1450_; lean_object* v_location_x3f_1451_; uint8_t v_explicit_1452_; lean_object* v___y_1454_; 
v_toTermInfo_1450_ = lean_ctor_get(v_info_1442_, 0);
lean_inc_ref(v_toTermInfo_1450_);
v_location_x3f_1451_ = lean_ctor_get(v_info_1442_, 1);
lean_inc(v_location_x3f_1451_);
v_explicit_1452_ = lean_ctor_get_uint8(v_info_1442_, sizeof(void*)*3);
if (lean_obj_tag(v_location_x3f_1451_) == 1)
{
lean_object* v_val_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1536_; 
v_val_1475_ = lean_ctor_get(v_location_x3f_1451_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_location_x3f_1451_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1477_ = v_location_x3f_1451_;
v_isShared_1478_ = v_isSharedCheck_1536_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_val_1475_);
lean_dec(v_location_x3f_1451_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1536_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v_range_1479_; lean_object* v_pos_1480_; lean_object* v_endPos_1481_; lean_object* v_module_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1534_; 
v_range_1479_ = lean_ctor_get(v_val_1475_, 1);
v_pos_1480_ = lean_ctor_get(v_range_1479_, 0);
lean_inc_ref(v_pos_1480_);
v_endPos_1481_ = lean_ctor_get(v_range_1479_, 2);
lean_inc_ref(v_endPos_1481_);
v_module_1482_ = lean_ctor_get(v_val_1475_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_val_1475_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; 
v_unused_1535_ = lean_ctor_get(v_val_1475_, 1);
lean_dec(v_unused_1535_);
v___x_1484_ = v_val_1475_;
v_isShared_1485_ = v_isSharedCheck_1534_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_module_1482_);
lean_dec(v_val_1475_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1534_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v_line_1486_; lean_object* v_column_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1533_; 
v_line_1486_ = lean_ctor_get(v_pos_1480_, 0);
v_column_1487_ = lean_ctor_get(v_pos_1480_, 1);
v_isSharedCheck_1533_ = !lean_is_exclusive(v_pos_1480_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1489_ = v_pos_1480_;
v_isShared_1490_ = v_isSharedCheck_1533_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_column_1487_);
lean_inc(v_line_1486_);
lean_dec(v_pos_1480_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1533_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v_line_1491_; lean_object* v_column_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1532_; 
v_line_1491_ = lean_ctor_get(v_endPos_1481_, 0);
v_column_1492_ = lean_ctor_get(v_endPos_1481_, 1);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_endPos_1481_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1494_ = v_endPos_1481_;
v_isShared_1495_ = v_isSharedCheck_1532_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_column_1492_);
lean_inc(v_line_1491_);
lean_dec(v_endPos_1481_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1532_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
uint8_t v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1496_ = 1;
v___x_1497_ = l_Lean_Name_toString(v_module_1482_, v___x_1496_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set_tag(v___x_1477_, 3);
lean_ctor_set(v___x_1477_, 0, v___x_1497_);
v___x_1499_ = v___x_1477_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1500_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
if (v_isShared_1495_ == 0)
{
lean_ctor_set_tag(v___x_1494_, 5);
lean_ctor_set(v___x_1494_, 1, v___x_1500_);
lean_ctor_set(v___x_1494_, 0, v___x_1499_);
v___x_1502_ = v___x_1494_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1503_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_1504_ = l_Nat_reprFast(v_line_1486_);
v___x_1505_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set_tag(v___x_1489_, 5);
lean_ctor_set(v___x_1489_, 1, v___x_1505_);
lean_ctor_set(v___x_1489_, 0, v___x_1503_);
v___x_1507_ = v___x_1489_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1508_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
if (v_isShared_1485_ == 0)
{
lean_ctor_set_tag(v___x_1484_, 5);
lean_ctor_set(v___x_1484_, 1, v___x_1508_);
lean_ctor_set(v___x_1484_, 0, v___x_1507_);
v___x_1510_ = v___x_1484_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1511_ = l_Nat_reprFast(v_column_1487_);
v___x_1512_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
v___x_1513_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1510_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v___x_1515_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1513_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
v___x_1516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1502_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_1518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1516_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
v___x_1519_ = l_Nat_reprFast(v_line_1491_);
v___x_1520_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
v___x_1521_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1503_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
lean_ctor_set(v___x_1522_, 1, v___x_1508_);
v___x_1523_ = l_Nat_reprFast(v_column_1492_);
v___x_1524_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
v___x_1525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1522_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v___x_1514_);
v___x_1527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1518_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___y_1454_ = v___x_1527_;
goto v___jp_1453_;
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
lean_object* v___x_1537_; 
lean_dec(v_location_x3f_1451_);
v___x_1537_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
v___y_1454_ = v___x_1537_;
goto v___jp_1453_;
}
v___jp_1444_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_inc_ref(v___y_1446_);
v___x_1447_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___y_1446_);
v___x_1448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___y_1445_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
return v___x_1449_;
}
v___jp_1453_:
{
lean_object* v_lctx_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v_a_1458_; lean_object* v___x_1459_; 
v_lctx_1455_ = lean_ctor_get(v_toTermInfo_1450_, 1);
lean_inc_ref(v_lctx_1455_);
v___x_1456_ = l_Lean_Elab_ContextInfo_toPPContext(v_ctx_1441_, v_lctx_1455_);
v___x_1457_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v___x_1456_, v_info_1442_);
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref(v___x_1457_);
v___x_1459_ = l_Lean_Elab_TermInfo_format(v_ctx_1441_, v_toTermInfo_1450_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1459_, 1);
v___x_1461_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__1));
v___x_1462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
lean_ctor_set(v___x_1462_, 1, v_a_1460_);
v___x_1463_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__3));
v___x_1464_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1462_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v___x_1465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
lean_ctor_set(v___x_1465_, 1, v___y_1454_);
v___x_1466_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__5));
v___x_1467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1465_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_a_1458_, v___x_1468_);
v___x_1470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1467_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__7));
v___x_1472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1470_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
if (v_explicit_1452_ == 0)
{
lean_object* v___x_1473_; 
v___x_1473_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__8));
v___y_1445_ = v___x_1472_;
v___y_1446_ = v___x_1473_;
goto v___jp_1444_;
}
else
{
lean_object* v___x_1474_; 
v___x_1474_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__9));
v___y_1445_ = v___x_1472_;
v___y_1446_ = v___x_1474_;
goto v___jp_1444_;
}
}
else
{
lean_dec(v_a_1458_);
lean_dec(v___y_1454_);
return v___x_1459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object* v_ctx_1538_, lean_object* v_info_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1538_, v_info_1539_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object* v_ctx_1545_, lean_object* v_info_1546_){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1547_ = ((lean_object*)(l_Lean_Elab_ChoiceInfo_format___closed__1));
v___x_1548_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1545_, v_info_1546_);
v___x_1549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceResolutionInfo_format(lean_object* v_ctx_1562_, lean_object* v_info_1563_){
_start:
{
lean_object* v_stx_1564_; lean_object* v_chosenAltIdx_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1593_; 
v_stx_1564_ = lean_ctor_get(v_info_1563_, 0);
v_chosenAltIdx_1565_ = lean_ctor_get(v_info_1563_, 1);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_info_1563_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1567_ = v_info_1563_;
v_isShared_1568_ = v_isSharedCheck_1593_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_chosenAltIdx_1565_);
lean_inc(v_stx_1564_);
lean_dec(v_info_1563_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1593_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1569_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__1));
lean_inc(v_chosenAltIdx_1565_);
v___x_1570_ = l_Nat_reprFast(v_chosenAltIdx_1565_);
v___x_1571_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set_tag(v___x_1567_, 5);
lean_ctor_set(v___x_1567_, 1, v___x_1571_);
lean_ctor_set(v___x_1567_, 0, v___x_1569_);
v___x_1573_ = v___x_1567_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1574_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__3));
v___x_1575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = l_Lean_Syntax_getNumArgs(v_stx_1564_);
v___x_1577_ = l_Nat_reprFast(v___x_1576_);
v___x_1578_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
v___x_1579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1575_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__5));
v___x_1581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = l_Lean_Syntax_getArg(v_stx_1564_, v_chosenAltIdx_1565_);
lean_dec(v_chosenAltIdx_1565_);
v___x_1583_ = l_Lean_Syntax_getKind(v___x_1582_);
v___x_1584_ = 1;
v___x_1585_ = l_Lean_Name_toString(v___x_1583_, v___x_1584_);
v___x_1586_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
v___x_1587_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1581_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__7));
v___x_1589_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1562_, v_stx_1564_);
lean_dec(v_stx_1564_);
v___x_1591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
return v___x_1591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object* v_ctx_1597_, lean_object* v_info_1598_){
_start:
{
lean_object* v_stx_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v_stx_1599_ = lean_ctor_get(v_info_1598_, 1);
v___x_1600_ = ((lean_object*)(l_Lean_Elab_DocInfo_format___closed__1));
lean_inc(v_stx_1599_);
v___x_1601_ = l_Lean_Syntax_getKind(v_stx_1599_);
v___x_1602_ = 1;
v___x_1603_ = l_Lean_Name_toString(v___x_1601_, v___x_1602_);
v___x_1604_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
v___x_1605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1600_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1605_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
v___x_1608_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1597_, v_info_1598_);
v___x_1609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object* v_ctx_1613_, lean_object* v_info_1614_){
_start:
{
lean_object* v_toElabInfo_1615_; lean_object* v_name_1616_; uint8_t v_kind_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v_toElabInfo_1615_ = lean_ctor_get(v_info_1614_, 0);
lean_inc_ref(v_toElabInfo_1615_);
v_name_1616_ = lean_ctor_get(v_info_1614_, 1);
lean_inc(v_name_1616_);
v_kind_1617_ = lean_ctor_get_uint8(v_info_1614_, sizeof(void*)*2);
lean_dec_ref(v_info_1614_);
v___x_1618_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__1));
v___x_1619_ = 1;
v___x_1620_ = l_Lean_Name_toString(v_name_1616_, v___x_1619_);
v___x_1621_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
v___x_1622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1618_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__5));
v___x_1624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = lean_unsigned_to_nat(0u);
v___x_1626_ = l_Lean_Elab_instReprDocElabKind_repr(v_kind_1617_, v___x_1625_);
v___x_1627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1624_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__7));
v___x_1629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1613_, v_toElabInfo_1615_);
v___x_1631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object* v_ctx_1632_, lean_object* v_x_1633_){
_start:
{
switch(lean_obj_tag(v_x_1633_))
{
case 0:
{
lean_object* v_i_1635_; lean_object* v___x_1636_; 
v_i_1635_ = lean_ctor_get(v_x_1633_, 0);
lean_inc_ref(v_i_1635_);
lean_dec_ref_known(v_x_1633_, 1);
v___x_1636_ = l_Lean_Elab_TacticInfo_format(v_ctx_1632_, v_i_1635_);
return v___x_1636_;
}
case 1:
{
lean_object* v_i_1637_; lean_object* v___x_1638_; 
v_i_1637_ = lean_ctor_get(v_x_1633_, 0);
lean_inc_ref(v_i_1637_);
lean_dec_ref_known(v_x_1633_, 1);
v___x_1638_ = l_Lean_Elab_TermInfo_format(v_ctx_1632_, v_i_1637_);
return v___x_1638_;
}
case 2:
{
lean_object* v_i_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1647_; 
v_i_1639_ = lean_ctor_get(v_x_1633_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_x_1633_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1641_ = v_x_1633_;
v_isShared_1642_ = v_isSharedCheck_1647_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_i_1639_);
lean_dec(v_x_1633_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1647_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1643_ = l_Lean_Elab_PartialTermInfo_format(v_ctx_1632_, v_i_1639_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set_tag(v___x_1641_, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1643_);
v___x_1645_ = v___x_1641_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
case 3:
{
lean_object* v_i_1648_; lean_object* v___x_1649_; 
v_i_1648_ = lean_ctor_get(v_x_1633_, 0);
lean_inc_ref(v_i_1648_);
lean_dec_ref_known(v_x_1633_, 1);
v___x_1649_ = l_Lean_Elab_CommandInfo_format(v_ctx_1632_, v_i_1648_);
return v___x_1649_;
}
case 4:
{
lean_object* v_i_1650_; lean_object* v___x_1651_; 
v_i_1650_ = lean_ctor_get(v_x_1633_, 0);
lean_inc_ref(v_i_1650_);
lean_dec_ref_known(v_x_1633_, 1);
v___x_1651_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1632_, v_i_1650_);
lean_dec_ref(v_ctx_1632_);
return v___x_1651_;
}
case 5:
{
lean_object* v_i_1652_; lean_object* v___x_1653_; 
v_i_1652_ = lean_ctor_get(v_x_1633_, 0);
lean_inc_ref(v_i_1652_);
lean_dec_ref_known(v_x_1633_, 1);
v___x_1653_ = l_Lean_Elab_OptionInfo_format(v_ctx_1632_, v_i_1652_);
return v___x_1653_;
}
case 6:
{
lean_object* v_i_1654_; lean_object* v___x_1655_; 
v_i_1654_ = lean_ctor_get(v_x_1633_, 0);
lean_inc_ref(v_i_1654_);
lean_dec_ref_known(v_x_1633_, 1);
v___x_1655_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_1632_, v_i_1654_);
return v___x_1655_;
}
case 7:
{
lean_object* v_i_1656_; lean_object* v___x_1657_; 
v_i_1656_ = lean_ctor_get(v_x_1633_, 0);
lean_inc_ref(v_i_1656_);
lean_dec_ref_known(v_x_1633_, 1);
v___x_1657_ = l_Lean_Elab_FieldInfo_format(v_ctx_1632_, v_i_1656_);
return v___x_1657_;
}
case 8:
{
lean_object* v_i_1658_; lean_object* v___x_1659_; 
v_i_1658_ = lean_ctor_get(v_x_1633_, 0);
lean_inc_ref(v_i_1658_);
lean_dec_ref_known(v_x_1633_, 1);
v___x_1659_ = l_Lean_Elab_CompletionInfo_format(v_ctx_1632_, v_i_1658_);
return v___x_1659_;
}
case 9:
{
lean_object* v_i_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1668_; 
lean_dec_ref(v_ctx_1632_);
v_i_1660_ = lean_ctor_get(v_x_1633_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_x_1633_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1662_ = v_x_1633_;
v_isShared_1663_ = v_isSharedCheck_1668_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_i_1660_);
lean_dec(v_x_1633_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1668_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___x_1664_ = l_Lean_Elab_UserWidgetInfo_format(v_i_1660_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set_tag(v___x_1662_, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1664_);
v___x_1666_ = v___x_1662_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
case 10:
{
lean_object* v_i_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1677_; 
lean_dec_ref(v_ctx_1632_);
v_i_1669_ = lean_ctor_get(v_x_1633_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_x_1633_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1671_ = v_x_1633_;
v_isShared_1672_ = v_isSharedCheck_1677_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_i_1669_);
lean_dec(v_x_1633_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1677_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1673_ = l_Lean_Elab_CustomInfo_format(v_i_1669_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set_tag(v___x_1671_, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1673_);
v___x_1675_ = v___x_1671_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
case 11:
{
lean_object* v_i_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1686_; 
lean_dec_ref(v_ctx_1632_);
v_i_1678_ = lean_ctor_get(v_x_1633_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_x_1633_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1680_ = v_x_1633_;
v_isShared_1681_ = v_isSharedCheck_1686_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_i_1678_);
lean_dec(v_x_1633_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1686_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1684_; 
v___x_1682_ = l_Lean_Elab_FVarAliasInfo_format(v_i_1678_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set_tag(v___x_1680_, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1682_);
v___x_1684_ = v___x_1680_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
case 12:
{
lean_object* v_i_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1695_; 
v_i_1687_ = lean_ctor_get(v_x_1633_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_x_1633_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1689_ = v_x_1633_;
v_isShared_1690_ = v_isSharedCheck_1695_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_i_1687_);
lean_dec(v_x_1633_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1695_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1691_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1632_, v_i_1687_);
lean_dec(v_i_1687_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set_tag(v___x_1689_, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1691_);
v___x_1693_ = v___x_1689_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
case 13:
{
lean_object* v_i_1696_; lean_object* v___x_1697_; 
v_i_1696_ = lean_ctor_get(v_x_1633_, 0);
lean_inc_ref(v_i_1696_);
lean_dec_ref_known(v_x_1633_, 1);
v___x_1697_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1632_, v_i_1696_);
return v___x_1697_;
}
case 14:
{
lean_object* v_i_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1706_; 
v_i_1698_ = lean_ctor_get(v_x_1633_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_x_1633_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1700_ = v_x_1633_;
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_i_1698_);
lean_dec(v_x_1633_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1702_ = l_Lean_Elab_ChoiceInfo_format(v_ctx_1632_, v_i_1698_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set_tag(v___x_1700_, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1702_);
v___x_1704_ = v___x_1700_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
case 15:
{
lean_object* v_i_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1715_; 
v_i_1707_ = lean_ctor_get(v_x_1633_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_x_1633_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1709_ = v_x_1633_;
v_isShared_1710_ = v_isSharedCheck_1715_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_i_1707_);
lean_dec(v_x_1633_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1715_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; lean_object* v___x_1713_; 
v___x_1711_ = l_Lean_Elab_ChoiceResolutionInfo_format(v_ctx_1632_, v_i_1707_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set_tag(v___x_1709_, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1711_);
v___x_1713_ = v___x_1709_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
case 16:
{
lean_object* v_i_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1724_; 
v_i_1716_ = lean_ctor_get(v_x_1633_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_x_1633_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1718_ = v_x_1633_;
v_isShared_1719_ = v_isSharedCheck_1724_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_i_1716_);
lean_dec(v_x_1633_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1724_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1720_ = l_Lean_Elab_DocInfo_format(v_ctx_1632_, v_i_1716_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set_tag(v___x_1718_, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1720_);
v___x_1722_ = v___x_1718_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
default: 
{
lean_object* v_i_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1733_; 
v_i_1725_ = lean_ctor_get(v_x_1633_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_x_1633_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1727_ = v_x_1633_;
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_i_1725_);
lean_dec(v_x_1633_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1729_ = l_Lean_Elab_DocElabInfo_format(v_ctx_1632_, v_i_1725_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set_tag(v___x_1727_, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1729_);
v___x_1731_ = v___x_1727_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object* v_ctx_1734_, lean_object* v_x_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_Elab_Info_format(v_ctx_1734_, v_x_1735_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object* v_x_1738_, lean_object* v_x_1739_){
_start:
{
if (lean_obj_tag(v_x_1739_) == 0)
{
return v_x_1738_;
}
else
{
lean_object* v_head_1740_; lean_object* v_tail_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_head_1740_ = lean_ctor_get(v_x_1739_, 0);
v_tail_1741_ = lean_ctor_get(v_x_1739_, 1);
v___x_1742_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2));
v___x_1743_ = lean_string_append(v_x_1738_, v___x_1742_);
v___x_1744_ = lean_expr_dbg_to_string(v_head_1740_);
v___x_1745_ = lean_string_append(v___x_1743_, v___x_1744_);
lean_dec_ref(v___x_1744_);
v_x_1738_ = v___x_1745_;
v_x_1739_ = v_tail_1741_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object* v_x_1747_, lean_object* v_x_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v_x_1747_, v_x_1748_);
lean_dec(v_x_1748_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object* v_x_1752_){
_start:
{
if (lean_obj_tag(v_x_1752_) == 0)
{
lean_object* v___x_1753_; 
v___x_1753_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0));
return v___x_1753_;
}
else
{
lean_object* v_tail_1754_; 
v_tail_1754_ = lean_ctor_get(v_x_1752_, 1);
if (lean_obj_tag(v_tail_1754_) == 0)
{
lean_object* v_head_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v_head_1755_ = lean_ctor_get(v_x_1752_, 0);
v___x_1756_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1757_ = lean_expr_dbg_to_string(v_head_1755_);
v___x_1758_ = lean_string_append(v___x_1756_, v___x_1757_);
lean_dec_ref(v___x_1757_);
v___x_1759_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1760_ = lean_string_append(v___x_1758_, v___x_1759_);
return v___x_1760_;
}
else
{
lean_object* v_head_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; uint32_t v___x_1766_; lean_object* v___x_1767_; 
v_head_1761_ = lean_ctor_get(v_x_1752_, 0);
v___x_1762_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1763_ = lean_expr_dbg_to_string(v_head_1761_);
v___x_1764_ = lean_string_append(v___x_1762_, v___x_1763_);
lean_dec_ref(v___x_1763_);
v___x_1765_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v___x_1764_, v_tail_1754_);
v___x_1766_ = 93;
v___x_1767_ = lean_string_push(v___x_1765_, v___x_1766_);
return v___x_1767_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object* v_x_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v_x_1768_);
lean_dec(v_x_1768_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object* v_ctx_1776_){
_start:
{
switch(lean_obj_tag(v_ctx_1776_))
{
case 0:
{
lean_object* v___x_1777_; 
lean_dec_ref_known(v_ctx_1776_, 1);
v___x_1777_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__1));
return v___x_1777_;
}
case 1:
{
lean_object* v_parentDecl_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1791_; 
v_parentDecl_1778_ = lean_ctor_get(v_ctx_1776_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_ctx_1776_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1780_ = v_ctx_1776_;
v_isShared_1781_ = v_isSharedCheck_1791_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_parentDecl_1778_);
lean_dec(v_ctx_1776_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1791_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; uint8_t v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1782_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__2));
v___x_1783_ = 1;
v___x_1784_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_parentDecl_1778_, v___x_1783_);
v___x_1785_ = lean_string_append(v___x_1782_, v___x_1784_);
lean_dec_ref(v___x_1784_);
v___x_1786_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1787_ = lean_string_append(v___x_1785_, v___x_1786_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set_tag(v___x_1780_, 3);
lean_ctor_set(v___x_1780_, 0, v___x_1787_);
v___x_1789_ = v___x_1780_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
default: 
{
lean_object* v_autoImplicits_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1807_; 
v_autoImplicits_1792_ = lean_ctor_get(v_ctx_1776_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_ctx_1776_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1794_ = v_ctx_1776_;
v_isShared_1795_ = v_isSharedCheck_1807_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_autoImplicits_1792_);
lean_dec(v_ctx_1776_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1807_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1796_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__3));
v___x_1797_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__4));
v___x_1798_ = lean_array_to_list(v_autoImplicits_1792_);
v___x_1799_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v___x_1798_);
lean_dec(v___x_1798_);
v___x_1800_ = lean_string_append(v___x_1797_, v___x_1799_);
lean_dec_ref(v___x_1799_);
v___x_1801_ = lean_string_append(v___x_1796_, v___x_1800_);
lean_dec_ref(v___x_1800_);
v___x_1802_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1803_ = lean_string_append(v___x_1801_, v___x_1802_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set_tag(v___x_1794_, 3);
lean_ctor_set(v___x_1794_, 0, v___x_1803_);
v___x_1805_ = v___x_1794_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format(lean_object* v_tree_1817_, lean_object* v_ctx_x3f_1818_){
_start:
{
switch(lean_obj_tag(v_tree_1817_))
{
case 0:
{
lean_object* v_i_1820_; lean_object* v_t_1821_; lean_object* v___x_1822_; 
v_i_1820_ = lean_ctor_get(v_tree_1817_, 0);
lean_inc_ref(v_i_1820_);
v_t_1821_ = lean_ctor_get(v_tree_1817_, 1);
lean_inc_ref(v_t_1821_);
lean_dec_ref_known(v_tree_1817_, 2);
v___x_1822_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1820_, v_ctx_x3f_1818_);
v_tree_1817_ = v_t_1821_;
v_ctx_x3f_1818_ = v___x_1822_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_ctx_x3f_1818_) == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec_ref_known(v_tree_1817_, 2);
v___x_1824_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__1));
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
return v___x_1825_;
}
else
{
lean_object* v_i_1826_; lean_object* v_children_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1877_; 
v_i_1826_ = lean_ctor_get(v_tree_1817_, 0);
v_children_1827_ = lean_ctor_get(v_tree_1817_, 1);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_tree_1817_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1829_ = v_tree_1817_;
v_isShared_1830_ = v_isSharedCheck_1877_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_children_1827_);
lean_inc(v_i_1826_);
lean_dec(v_tree_1817_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1877_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v_val_1831_; lean_object* v___x_1832_; 
v_val_1831_ = lean_ctor_get(v_ctx_x3f_1818_, 0);
lean_inc_ref(v_i_1826_);
lean_inc(v_val_1831_);
v___x_1832_ = l_Lean_Elab_Info_format(v_val_1831_, v_i_1826_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1876_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1876_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1876_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v_size_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v_size_1837_ = lean_ctor_get(v_children_1827_, 2);
v___x_1838_ = lean_unsigned_to_nat(0u);
v___x_1839_ = lean_nat_dec_eq(v_size_1837_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
lean_del_object(v___x_1835_);
v___x_1840_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_1818_, v_i_1826_);
lean_dec_ref(v_i_1826_);
v___x_1841_ = l_Lean_PersistentArray_toList___redArg(v_children_1827_);
lean_dec_ref(v_children_1827_);
v___x_1842_ = lean_box(0);
v___x_1843_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1840_, v___x_1841_, v___x_1842_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1859_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1859_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1859_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1848_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1830_ == 0)
{
lean_ctor_set_tag(v___x_1829_, 5);
lean_ctor_set(v___x_1829_, 1, v_a_1833_);
lean_ctor_set(v___x_1829_, 0, v___x_1848_);
v___x_1850_ = v___x_1829_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1848_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_a_1833_);
v___x_1850_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1851_ = lean_box(1);
v___x_1852_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1851_, v_a_1844_);
v___x_1853_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1850_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = l_Std_Format_nestD(v___x_1853_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1854_);
v___x_1856_ = v___x_1846_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec(v_a_1833_);
lean_del_object(v___x_1829_);
v_a_1860_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1843_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1843_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1870_; 
lean_dec_ref(v_children_1827_);
lean_dec_ref_known(v_ctx_x3f_1818_, 1);
lean_dec_ref(v_i_1826_);
v___x_1868_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1830_ == 0)
{
lean_ctor_set_tag(v___x_1829_, 5);
lean_ctor_set(v___x_1829_, 1, v_a_1833_);
lean_ctor_set(v___x_1829_, 0, v___x_1868_);
v___x_1870_ = v___x_1829_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1868_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_a_1833_);
v___x_1870_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; lean_object* v___x_1873_; 
v___x_1871_ = l_Std_Format_nestD(v___x_1870_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1871_);
v___x_1873_ = v___x_1835_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
else
{
lean_del_object(v___x_1829_);
lean_dec_ref(v_children_1827_);
lean_dec_ref_known(v_ctx_x3f_1818_, 1);
lean_dec_ref(v_i_1826_);
return v___x_1832_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v_ctx_x3f_1818_);
v_mvarId_1878_ = lean_ctor_get(v_tree_1817_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_tree_1817_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1880_ = v_tree_1817_;
v_isShared_1881_ = v_isSharedCheck_1891_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_mvarId_1878_);
lean_dec(v_tree_1817_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1891_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; uint8_t v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1886_; 
v___x_1882_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__5));
v___x_1883_ = 1;
v___x_1884_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_1878_, v___x_1883_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set_tag(v___x_1880_, 3);
lean_ctor_set(v___x_1880_, 0, v___x_1884_);
v___x_1886_ = v___x_1880_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1882_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
v___x_1888_ = l_Std_Format_nestD(v___x_1887_);
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
return v___x_1889_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object* v___x_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_){
_start:
{
if (lean_obj_tag(v_x_1893_) == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_dec(v___x_1892_);
v___x_1896_ = l_List_reverse___redArg(v_x_1894_);
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
else
{
lean_object* v_head_1898_; lean_object* v_tail_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1917_; 
v_head_1898_ = lean_ctor_get(v_x_1893_, 0);
v_tail_1899_ = lean_ctor_get(v_x_1893_, 1);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_x_1893_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1901_ = v_x_1893_;
v_isShared_1902_ = v_isSharedCheck_1917_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_tail_1899_);
lean_inc(v_head_1898_);
lean_dec(v_x_1893_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1917_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; 
lean_inc(v___x_1892_);
v___x_1903_ = l_Lean_Elab_InfoTree_format(v_head_1898_, v___x_1892_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1906_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref_known(v___x_1903_, 1);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 1, v_x_1894_);
lean_ctor_set(v___x_1901_, 0, v_a_1904_);
v___x_1906_ = v___x_1901_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1904_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_x_1894_);
v___x_1906_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
v_x_1893_ = v_tail_1899_;
v_x_1894_ = v___x_1906_;
goto _start;
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_del_object(v___x_1901_);
lean_dec(v_tail_1899_);
lean_dec(v_x_1894_);
lean_dec(v___x_1892_);
v_a_1909_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1903_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1903_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object* v___x_1918_, lean_object* v_x_1919_, lean_object* v_x_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1918_, v_x_1919_, v_x_1920_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object* v_tree_1923_, lean_object* v_ctx_x3f_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_Elab_InfoTree_format(v_tree_1923_, v_ctx_x3f_1924_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object* v_f_1927_, lean_object* v_s_1928_){
_start:
{
uint8_t v_enabled_1929_; lean_object* v_assignment_1930_; lean_object* v_lazyAssignment_1931_; lean_object* v_trees_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1940_; 
v_enabled_1929_ = lean_ctor_get_uint8(v_s_1928_, sizeof(void*)*3);
v_assignment_1930_ = lean_ctor_get(v_s_1928_, 0);
v_lazyAssignment_1931_ = lean_ctor_get(v_s_1928_, 1);
v_trees_1932_ = lean_ctor_get(v_s_1928_, 2);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_s_1928_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1934_ = v_s_1928_;
v_isShared_1935_ = v_isSharedCheck_1940_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_trees_1932_);
lean_inc(v_lazyAssignment_1931_);
lean_inc(v_assignment_1930_);
lean_dec(v_s_1928_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1940_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1936_ = lean_apply_1(v_f_1927_, v_trees_1932_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 2, v___x_1936_);
v___x_1938_ = v___x_1934_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_assignment_1930_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_lazyAssignment_1931_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v___x_1936_);
lean_ctor_set_uint8(v_reuseFailAlloc_1939_, sizeof(void*)*3, v_enabled_1929_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object* v_inst_1941_, lean_object* v_f_1942_){
_start:
{
lean_object* v_modifyInfoState_1943_; lean_object* v___f_1944_; lean_object* v___x_1945_; 
v_modifyInfoState_1943_ = lean_ctor_get(v_inst_1941_, 1);
lean_inc(v_modifyInfoState_1943_);
lean_dec_ref(v_inst_1941_);
v___f_1944_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1944_, 0, v_f_1942_);
v___x_1945_ = lean_apply_1(v_modifyInfoState_1943_, v___f_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object* v_m_1946_, lean_object* v_inst_1947_, lean_object* v_f_1948_){
_start:
{
lean_object* v_modifyInfoState_1949_; lean_object* v___f_1950_; lean_object* v___x_1951_; 
v_modifyInfoState_1949_ = lean_ctor_get(v_inst_1947_, 1);
lean_inc(v_modifyInfoState_1949_);
lean_dec_ref(v_inst_1947_);
v___f_1950_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1950_, 0, v_f_1948_);
v___x_1951_ = lean_apply_1(v_modifyInfoState_1949_, v___f_1950_);
return v___x_1951_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1952_ = lean_unsigned_to_nat(32u);
v___x_1953_ = lean_mk_empty_array_with_capacity(v___x_1952_);
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
return v___x_1954_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1955_ = ((size_t)5ULL);
v___x_1956_ = lean_unsigned_to_nat(0u);
v___x_1957_ = lean_unsigned_to_nat(32u);
v___x_1958_ = lean_mk_empty_array_with_capacity(v___x_1957_);
v___x_1959_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0);
v___x_1960_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
lean_ctor_set(v___x_1960_, 1, v___x_1958_);
lean_ctor_set(v___x_1960_, 2, v___x_1956_);
lean_ctor_set(v___x_1960_, 3, v___x_1956_);
lean_ctor_set_usize(v___x_1960_, 4, v___x_1955_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object* v_s_1961_){
_start:
{
uint8_t v_enabled_1962_; lean_object* v_assignment_1963_; lean_object* v_lazyAssignment_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1972_; 
v_enabled_1962_ = lean_ctor_get_uint8(v_s_1961_, sizeof(void*)*3);
v_assignment_1963_ = lean_ctor_get(v_s_1961_, 0);
v_lazyAssignment_1964_ = lean_ctor_get(v_s_1961_, 1);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_s_1961_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; 
v_unused_1973_ = lean_ctor_get(v_s_1961_, 2);
lean_dec(v_unused_1973_);
v___x_1966_ = v_s_1961_;
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_lazyAssignment_1964_);
lean_inc(v_assignment_1963_);
lean_dec(v_s_1961_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1968_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 2, v___x_1968_);
v___x_1970_ = v___x_1966_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_assignment_1963_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_lazyAssignment_1964_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v___x_1968_);
lean_ctor_set_uint8(v_reuseFailAlloc_1971_, sizeof(void*)*3, v_enabled_1962_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object* v_toPure_1974_, lean_object* v_trees_1975_, lean_object* v_____r_1976_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = lean_apply_2(v_toPure_1974_, lean_box(0), v_trees_1975_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object* v_toPure_1978_, lean_object* v_modifyInfoState_1979_, lean_object* v___f_1980_, lean_object* v_toBind_1981_, lean_object* v_____do__lift_1982_){
_start:
{
lean_object* v_trees_1983_; lean_object* v___f_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v_trees_1983_ = lean_ctor_get(v_____do__lift_1982_, 2);
lean_inc_ref(v_trees_1983_);
lean_dec_ref(v_____do__lift_1982_);
v___f_1984_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1984_, 0, v_toPure_1978_);
lean_closure_set(v___f_1984_, 1, v_trees_1983_);
v___x_1985_ = lean_apply_1(v_modifyInfoState_1979_, v___f_1980_);
v___x_1986_ = lean_apply_4(v_toBind_1981_, lean_box(0), lean_box(0), v___x_1985_, v___f_1984_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object* v_inst_1988_, lean_object* v_inst_1989_){
_start:
{
lean_object* v_toApplicative_1990_; lean_object* v_toBind_1991_; lean_object* v_getInfoState_1992_; lean_object* v_modifyInfoState_1993_; lean_object* v_toPure_1994_; lean_object* v___f_1995_; lean_object* v___f_1996_; lean_object* v___x_1997_; 
v_toApplicative_1990_ = lean_ctor_get(v_inst_1988_, 0);
lean_inc_ref(v_toApplicative_1990_);
v_toBind_1991_ = lean_ctor_get(v_inst_1988_, 1);
lean_inc_n(v_toBind_1991_, 2);
lean_dec_ref(v_inst_1988_);
v_getInfoState_1992_ = lean_ctor_get(v_inst_1989_, 0);
lean_inc(v_getInfoState_1992_);
v_modifyInfoState_1993_ = lean_ctor_get(v_inst_1989_, 1);
lean_inc(v_modifyInfoState_1993_);
lean_dec_ref(v_inst_1989_);
v_toPure_1994_ = lean_ctor_get(v_toApplicative_1990_, 1);
lean_inc(v_toPure_1994_);
lean_dec_ref(v_toApplicative_1990_);
v___f_1995_ = ((lean_object*)(l_Lean_Elab_getResetInfoTrees___redArg___closed__0));
v___f_1996_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1996_, 0, v_toPure_1994_);
lean_closure_set(v___f_1996_, 1, v_modifyInfoState_1993_);
lean_closure_set(v___f_1996_, 2, v___f_1995_);
lean_closure_set(v___f_1996_, 3, v_toBind_1991_);
v___x_1997_ = lean_apply_4(v_toBind_1991_, lean_box(0), lean_box(0), v_getInfoState_1992_, v___f_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object* v_m_1998_, lean_object* v_inst_1999_, lean_object* v_inst_2000_){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_1999_, v_inst_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object* v_t_2002_, lean_object* v_s_2003_){
_start:
{
uint8_t v_enabled_2004_; lean_object* v_assignment_2005_; lean_object* v_lazyAssignment_2006_; lean_object* v_trees_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2015_; 
v_enabled_2004_ = lean_ctor_get_uint8(v_s_2003_, sizeof(void*)*3);
v_assignment_2005_ = lean_ctor_get(v_s_2003_, 0);
v_lazyAssignment_2006_ = lean_ctor_get(v_s_2003_, 1);
v_trees_2007_ = lean_ctor_get(v_s_2003_, 2);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_s_2003_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2009_ = v_s_2003_;
v_isShared_2010_ = v_isSharedCheck_2015_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_trees_2007_);
lean_inc(v_lazyAssignment_2006_);
lean_inc(v_assignment_2005_);
lean_dec(v_s_2003_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2015_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2011_ = l_Lean_PersistentArray_push___redArg(v_trees_2007_, v_t_2002_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 2, v___x_2011_);
v___x_2013_ = v___x_2009_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_assignment_2005_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_lazyAssignment_2006_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v___x_2011_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*3, v_enabled_2004_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object* v_toPure_2016_, lean_object* v_modifyInfoState_2017_, lean_object* v___f_2018_, lean_object* v_____do__lift_2019_){
_start:
{
uint8_t v_enabled_2020_; 
v_enabled_2020_ = lean_ctor_get_uint8(v_____do__lift_2019_, sizeof(void*)*3);
if (v_enabled_2020_ == 0)
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec_ref(v___f_2018_);
lean_dec(v_modifyInfoState_2017_);
v___x_2021_ = lean_box(0);
v___x_2022_ = lean_apply_2(v_toPure_2016_, lean_box(0), v___x_2021_);
return v___x_2022_;
}
else
{
lean_object* v___x_2023_; 
lean_dec(v_toPure_2016_);
v___x_2023_ = lean_apply_1(v_modifyInfoState_2017_, v___f_2018_);
return v___x_2023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object* v_toPure_2024_, lean_object* v_modifyInfoState_2025_, lean_object* v___f_2026_, lean_object* v_____do__lift_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Lean_Elab_pushInfoTree___redArg___lam__1(v_toPure_2024_, v_modifyInfoState_2025_, v___f_2026_, v_____do__lift_2027_);
lean_dec_ref(v_____do__lift_2027_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object* v_inst_2029_, lean_object* v_inst_2030_, lean_object* v_t_2031_){
_start:
{
lean_object* v_toApplicative_2032_; lean_object* v_toBind_2033_; lean_object* v_getInfoState_2034_; lean_object* v_modifyInfoState_2035_; lean_object* v_toPure_2036_; lean_object* v___f_2037_; lean_object* v___f_2038_; lean_object* v___x_2039_; 
v_toApplicative_2032_ = lean_ctor_get(v_inst_2029_, 0);
lean_inc_ref(v_toApplicative_2032_);
v_toBind_2033_ = lean_ctor_get(v_inst_2029_, 1);
lean_inc(v_toBind_2033_);
lean_dec_ref(v_inst_2029_);
v_getInfoState_2034_ = lean_ctor_get(v_inst_2030_, 0);
lean_inc(v_getInfoState_2034_);
v_modifyInfoState_2035_ = lean_ctor_get(v_inst_2030_, 1);
lean_inc(v_modifyInfoState_2035_);
lean_dec_ref(v_inst_2030_);
v_toPure_2036_ = lean_ctor_get(v_toApplicative_2032_, 1);
lean_inc(v_toPure_2036_);
lean_dec_ref(v_toApplicative_2032_);
v___f_2037_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2037_, 0, v_t_2031_);
v___f_2038_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2038_, 0, v_toPure_2036_);
lean_closure_set(v___f_2038_, 1, v_modifyInfoState_2035_);
lean_closure_set(v___f_2038_, 2, v___f_2037_);
v___x_2039_ = lean_apply_4(v_toBind_2033_, lean_box(0), lean_box(0), v_getInfoState_2034_, v___f_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object* v_m_2040_, lean_object* v_inst_2041_, lean_object* v_inst_2042_, lean_object* v_t_2043_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2041_, v_inst_2042_, v_t_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object* v_toPure_2045_, lean_object* v_t_2046_, lean_object* v_inst_2047_, lean_object* v_inst_2048_, lean_object* v_____do__lift_2049_){
_start:
{
uint8_t v_enabled_2050_; 
v_enabled_2050_ = lean_ctor_get_uint8(v_____do__lift_2049_, sizeof(void*)*3);
if (v_enabled_2050_ == 0)
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
lean_dec_ref(v_inst_2048_);
lean_dec_ref(v_inst_2047_);
lean_dec_ref(v_t_2046_);
v___x_2051_ = lean_box(0);
v___x_2052_ = lean_apply_2(v_toPure_2045_, lean_box(0), v___x_2051_);
return v___x_2052_;
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
lean_dec(v_toPure_2045_);
v___x_2053_ = lean_unsigned_to_nat(32u);
v___x_2054_ = lean_mk_empty_array_with_capacity(v___x_2053_);
lean_dec_ref(v___x_2054_);
v___x_2055_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2056_, 0, v_t_2046_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
v___x_2057_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2047_, v_inst_2048_, v___x_2056_);
return v___x_2057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object* v_toPure_2058_, lean_object* v_t_2059_, lean_object* v_inst_2060_, lean_object* v_inst_2061_, lean_object* v_____do__lift_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Lean_Elab_pushInfoLeaf___redArg___lam__0(v_toPure_2058_, v_t_2059_, v_inst_2060_, v_inst_2061_, v_____do__lift_2062_);
lean_dec_ref(v_____do__lift_2062_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object* v_inst_2064_, lean_object* v_inst_2065_, lean_object* v_t_2066_){
_start:
{
lean_object* v_toApplicative_2067_; lean_object* v_toBind_2068_; lean_object* v_getInfoState_2069_; lean_object* v_toPure_2070_; lean_object* v___f_2071_; lean_object* v___x_2072_; 
v_toApplicative_2067_ = lean_ctor_get(v_inst_2064_, 0);
v_toBind_2068_ = lean_ctor_get(v_inst_2064_, 1);
lean_inc(v_toBind_2068_);
v_getInfoState_2069_ = lean_ctor_get(v_inst_2065_, 0);
lean_inc(v_getInfoState_2069_);
v_toPure_2070_ = lean_ctor_get(v_toApplicative_2067_, 1);
lean_inc(v_toPure_2070_);
v___f_2071_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2071_, 0, v_toPure_2070_);
lean_closure_set(v___f_2071_, 1, v_t_2066_);
lean_closure_set(v___f_2071_, 2, v_inst_2064_);
lean_closure_set(v___f_2071_, 3, v_inst_2065_);
v___x_2072_ = lean_apply_4(v_toBind_2068_, lean_box(0), lean_box(0), v_getInfoState_2069_, v___f_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object* v_m_2073_, lean_object* v_inst_2074_, lean_object* v_inst_2075_, lean_object* v_t_2076_){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2074_, v_inst_2075_, v_t_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object* v_inst_2078_, lean_object* v_inst_2079_, lean_object* v_info_2080_){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2081_, 0, v_info_2080_);
v___x_2082_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2078_, v_inst_2079_, v___x_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object* v_m_2083_, lean_object* v_inst_2084_, lean_object* v_inst_2085_, lean_object* v_info_2086_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_2084_, v_inst_2085_, v_info_2086_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object* v_stx_2088_, lean_object* v_expectedType_x3f_2089_, lean_object* v_inst_2090_, lean_object* v_inst_2091_, lean_object* v_____do__lift_2092_){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; uint8_t v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2093_ = lean_box(0);
v___x_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
lean_ctor_set(v___x_2094_, 1, v_stx_2088_);
v___x_2095_ = l_Lean_LocalContext_empty;
v___x_2096_ = 0;
v___x_2097_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2097_, 0, v___x_2094_);
lean_ctor_set(v___x_2097_, 1, v___x_2095_);
lean_ctor_set(v___x_2097_, 2, v_expectedType_x3f_2089_);
lean_ctor_set(v___x_2097_, 3, v_____do__lift_2092_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*4, v___x_2096_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*4 + 1, v___x_2096_);
v___x_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
v___x_2099_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2090_, v_inst_2091_, v___x_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object* v_inst_2100_, lean_object* v_inst_2101_, lean_object* v_inst_2102_, lean_object* v_inst_2103_, lean_object* v_stx_2104_, lean_object* v_n_2105_, lean_object* v_expectedType_x3f_2106_){
_start:
{
lean_object* v_toBind_2107_; lean_object* v___f_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v_toBind_2107_ = lean_ctor_get(v_inst_2100_, 1);
lean_inc(v_toBind_2107_);
lean_inc_ref(v_inst_2100_);
v___f_2108_ = lean_alloc_closure((void*)(l_Lean_Elab_addConstInfo___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2108_, 0, v_stx_2104_);
lean_closure_set(v___f_2108_, 1, v_expectedType_x3f_2106_);
lean_closure_set(v___f_2108_, 2, v_inst_2100_);
lean_closure_set(v___f_2108_, 3, v_inst_2101_);
v___x_2109_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_2100_, v_inst_2102_, v_inst_2103_, v_n_2105_);
v___x_2110_ = lean_apply_4(v_toBind_2107_, lean_box(0), lean_box(0), v___x_2109_, v___f_2108_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object* v_m_2111_, lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_stx_2116_, lean_object* v_n_2117_, lean_object* v_expectedType_x3f_2118_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Lean_Elab_addConstInfo___redArg(v_inst_2112_, v_inst_2113_, v_inst_2114_, v_inst_2115_, v_stx_2116_, v_n_2117_, v_expectedType_x3f_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___x_2123_; lean_object* v_infoState_2124_; uint8_t v_enabled_2125_; 
v___x_2123_ = lean_st_ref_get(v___y_2121_);
v_infoState_2124_ = lean_ctor_get(v___x_2123_, 8);
lean_inc_ref(v_infoState_2124_);
lean_dec(v___x_2123_);
v_enabled_2125_ = lean_ctor_get_uint8(v_infoState_2124_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2124_);
if (v_enabled_2125_ == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
lean_dec_ref(v_t_2120_);
v___x_2126_ = lean_box(0);
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
return v___x_2127_;
}
else
{
lean_object* v___x_2128_; lean_object* v_infoState_2129_; lean_object* v_env_2130_; lean_object* v_nextMacroScope_2131_; lean_object* v_ngen_2132_; lean_object* v_auxDeclNGen_2133_; lean_object* v_traceState_2134_; lean_object* v_cache_2135_; lean_object* v_recordedDeps_2136_; lean_object* v_messages_2137_; lean_object* v_snapshotTasks_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2160_; 
v___x_2128_ = lean_st_ref_take(v___y_2121_);
v_infoState_2129_ = lean_ctor_get(v___x_2128_, 8);
v_env_2130_ = lean_ctor_get(v___x_2128_, 0);
v_nextMacroScope_2131_ = lean_ctor_get(v___x_2128_, 1);
v_ngen_2132_ = lean_ctor_get(v___x_2128_, 2);
v_auxDeclNGen_2133_ = lean_ctor_get(v___x_2128_, 3);
v_traceState_2134_ = lean_ctor_get(v___x_2128_, 4);
v_cache_2135_ = lean_ctor_get(v___x_2128_, 5);
v_recordedDeps_2136_ = lean_ctor_get(v___x_2128_, 6);
v_messages_2137_ = lean_ctor_get(v___x_2128_, 7);
v_snapshotTasks_2138_ = lean_ctor_get(v___x_2128_, 9);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2140_ = v___x_2128_;
v_isShared_2141_ = v_isSharedCheck_2160_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_snapshotTasks_2138_);
lean_inc(v_infoState_2129_);
lean_inc(v_messages_2137_);
lean_inc(v_recordedDeps_2136_);
lean_inc(v_cache_2135_);
lean_inc(v_traceState_2134_);
lean_inc(v_auxDeclNGen_2133_);
lean_inc(v_ngen_2132_);
lean_inc(v_nextMacroScope_2131_);
lean_inc(v_env_2130_);
lean_dec(v___x_2128_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2160_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
uint8_t v_enabled_2142_; lean_object* v_assignment_2143_; lean_object* v_lazyAssignment_2144_; lean_object* v_trees_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2159_; 
v_enabled_2142_ = lean_ctor_get_uint8(v_infoState_2129_, sizeof(void*)*3);
v_assignment_2143_ = lean_ctor_get(v_infoState_2129_, 0);
v_lazyAssignment_2144_ = lean_ctor_get(v_infoState_2129_, 1);
v_trees_2145_ = lean_ctor_get(v_infoState_2129_, 2);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_infoState_2129_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2147_ = v_infoState_2129_;
v_isShared_2148_ = v_isSharedCheck_2159_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_trees_2145_);
lean_inc(v_lazyAssignment_2144_);
lean_inc(v_assignment_2143_);
lean_dec(v_infoState_2129_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2159_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2149_ = lean_box(0);
v___x_2150_ = l_Lean_PersistentArray_push___redArg(v_trees_2145_, v_t_2120_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 2, v___x_2150_);
v___x_2152_ = v___x_2147_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_assignment_2143_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_lazyAssignment_2144_);
lean_ctor_set(v_reuseFailAlloc_2158_, 2, v___x_2150_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, sizeof(void*)*3, v_enabled_2142_);
v___x_2152_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2154_; 
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 8, v___x_2152_);
v___x_2154_ = v___x_2140_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_env_2130_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_nextMacroScope_2131_);
lean_ctor_set(v_reuseFailAlloc_2157_, 2, v_ngen_2132_);
lean_ctor_set(v_reuseFailAlloc_2157_, 3, v_auxDeclNGen_2133_);
lean_ctor_set(v_reuseFailAlloc_2157_, 4, v_traceState_2134_);
lean_ctor_set(v_reuseFailAlloc_2157_, 5, v_cache_2135_);
lean_ctor_set(v_reuseFailAlloc_2157_, 6, v_recordedDeps_2136_);
lean_ctor_set(v_reuseFailAlloc_2157_, 7, v_messages_2137_);
lean_ctor_set(v_reuseFailAlloc_2157_, 8, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2157_, 9, v_snapshotTasks_2138_);
v___x_2154_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = lean_st_ref_put(v___y_2121_, v___x_2154_);
v___x_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2149_);
return v___x_2156_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2161_, v___y_2162_);
lean_dec(v___y_2162_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object* v_t_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v___x_2169_; lean_object* v_infoState_2170_; uint8_t v_enabled_2171_; 
v___x_2169_ = lean_st_ref_get(v___y_2167_);
v_infoState_2170_ = lean_ctor_get(v___x_2169_, 8);
lean_inc_ref(v_infoState_2170_);
lean_dec(v___x_2169_);
v_enabled_2171_ = lean_ctor_get_uint8(v_infoState_2170_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2170_);
if (v_enabled_2171_ == 0)
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_dec_ref(v_t_2165_);
v___x_2172_ = lean_box(0);
v___x_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
return v___x_2173_;
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2174_ = lean_unsigned_to_nat(32u);
v___x_2175_ = lean_mk_empty_array_with_capacity(v___x_2174_);
lean_dec_ref(v___x_2175_);
v___x_2176_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2177_, 0, v_t_2165_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v___x_2177_, v___y_2167_);
return v___x_2178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object* v_t_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
return v_res_2183_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
return v___x_2185_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2187_ = lean_unsigned_to_nat(0u);
v___x_2188_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
lean_ctor_set(v___x_2188_, 2, v___x_2187_);
lean_ctor_set(v___x_2188_, 3, v___x_2187_);
lean_ctor_set(v___x_2188_, 4, v___x_2186_);
lean_ctor_set(v___x_2188_, 5, v___x_2186_);
lean_ctor_set(v___x_2188_, 6, v___x_2186_);
lean_ctor_set(v___x_2188_, 7, v___x_2186_);
lean_ctor_set(v___x_2188_, 8, v___x_2186_);
lean_ctor_set(v___x_2188_, 9, v___x_2186_);
lean_ctor_set(v___x_2188_, 10, v___x_2186_);
return v___x_2188_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2189_ = lean_box(1);
v___x_2190_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_2191_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
lean_ctor_set(v___x_2192_, 1, v___x_2190_);
lean_ctor_set(v___x_2192_, 2, v___x_2189_);
return v___x_2192_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3));
v___x_2195_ = l_Lean_stringToMessageData(v___x_2194_);
return v___x_2195_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5));
v___x_2198_ = l_Lean_stringToMessageData(v___x_2197_);
return v___x_2198_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7));
v___x_2201_ = l_Lean_stringToMessageData(v___x_2200_);
return v___x_2201_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9));
v___x_2204_ = l_Lean_stringToMessageData(v___x_2203_);
return v___x_2204_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11));
v___x_2207_ = l_Lean_stringToMessageData(v___x_2206_);
return v___x_2207_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13));
v___x_2210_ = l_Lean_stringToMessageData(v___x_2209_);
return v___x_2210_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15));
v___x_2213_ = l_Lean_stringToMessageData(v___x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_2214_, lean_object* v_declHint_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v_env_2220_; uint8_t v___x_2221_; 
v___x_2218_ = lean_box(0);
v___x_2219_ = lean_st_ref_get(v___y_2216_);
v_env_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc_ref(v_env_2220_);
lean_dec(v___x_2219_);
v___x_2221_ = l_Lean_Name_isAnonymous(v_declHint_2215_);
if (v___x_2221_ == 0)
{
uint8_t v_isExporting_2222_; 
v_isExporting_2222_ = lean_ctor_get_uint8(v_env_2220_, sizeof(void*)*8);
if (v_isExporting_2222_ == 0)
{
lean_object* v___x_2223_; 
lean_dec_ref(v_env_2220_);
lean_dec(v_declHint_2215_);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v_msg_2214_);
return v___x_2223_;
}
else
{
lean_object* v___x_2224_; uint8_t v___x_2225_; 
lean_inc_ref(v_env_2220_);
v___x_2224_ = l_Lean_Environment_setExporting(v_env_2220_, v___x_2221_);
lean_inc(v_declHint_2215_);
lean_inc_ref(v___x_2224_);
v___x_2225_ = l_Lean_Environment_contains(v___x_2224_, v_declHint_2215_, v_isExporting_2222_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; 
lean_dec_ref(v___x_2224_);
lean_dec_ref(v_env_2220_);
lean_dec(v_declHint_2215_);
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_msg_2214_);
return v___x_2226_;
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v_c_2232_; lean_object* v___x_2233_; 
v___x_2227_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2228_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_2229_ = l_Lean_Options_empty;
v___x_2230_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2224_);
lean_ctor_set(v___x_2230_, 1, v___x_2227_);
lean_ctor_set(v___x_2230_, 2, v___x_2228_);
lean_ctor_set(v___x_2230_, 3, v___x_2229_);
lean_inc(v_declHint_2215_);
v___x_2231_ = l_Lean_MessageData_ofConstName(v_declHint_2215_, v___x_2221_);
v_c_2232_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2232_, 0, v___x_2230_);
lean_ctor_set(v_c_2232_, 1, v___x_2231_);
v___x_2233_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2220_, v_declHint_2215_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec_ref(v_env_2220_);
lean_dec(v_declHint_2215_);
v___x_2234_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
lean_ctor_set(v___x_2235_, 1, v_c_2232_);
v___x_2236_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6);
v___x_2237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2235_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = l_Lean_MessageData_note(v___x_2237_);
v___x_2239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2239_, 0, v_msg_2214_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
return v___x_2240_;
}
else
{
lean_object* v_val_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2275_; 
v_val_2241_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2243_ = v___x_2233_;
v_isShared_2244_ = v_isSharedCheck_2275_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_val_2241_);
lean_dec(v___x_2233_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2275_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v_mod_2247_; uint8_t v___x_2248_; 
v___x_2245_ = l_Lean_Environment_header(v_env_2220_);
lean_dec_ref(v_env_2220_);
v___x_2246_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2245_);
v_mod_2247_ = lean_array_get(v___x_2218_, v___x_2246_, v_val_2241_);
lean_dec(v_val_2241_);
lean_dec_ref(v___x_2246_);
v___x_2248_ = l_Lean_isPrivateName(v_declHint_2215_);
lean_dec(v_declHint_2215_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2249_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8);
v___x_2250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
lean_ctor_set(v___x_2250_, 1, v_c_2232_);
v___x_2251_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10);
v___x_2252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2250_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = l_Lean_MessageData_ofName(v_mod_2247_);
v___x_2254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12);
v___x_2256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2254_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = l_Lean_MessageData_note(v___x_2256_);
v___x_2258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2258_, 0, v_msg_2214_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set_tag(v___x_2243_, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2258_);
v___x_2260_ = v___x_2243_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2258_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2273_; 
v___x_2262_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
lean_ctor_set(v___x_2263_, 1, v_c_2232_);
v___x_2264_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14);
v___x_2265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2263_);
lean_ctor_set(v___x_2265_, 1, v___x_2264_);
v___x_2266_ = l_Lean_MessageData_ofName(v_mod_2247_);
v___x_2267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2265_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
v___x_2268_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16);
v___x_2269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2267_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = l_Lean_MessageData_note(v___x_2269_);
v___x_2271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2271_, 0, v_msg_2214_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set_tag(v___x_2243_, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2271_);
v___x_2273_ = v___x_2243_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2276_; 
lean_dec_ref(v_env_2220_);
lean_dec(v_declHint_2215_);
v___x_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2276_, 0, v_msg_2214_);
return v___x_2276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_2277_, lean_object* v_declHint_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2277_, v_declHint_2278_, v___y_2279_);
lean_dec(v___y_2279_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_2282_, lean_object* v_declHint_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v___x_2287_; lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2297_; 
v___x_2287_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2282_, v_declHint_2283_, v___y_2285_);
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2290_ = v___x_2287_;
v_isShared_2291_ = v_isSharedCheck_2297_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2287_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2297_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2295_; 
v___x_2292_ = l_Lean_unknownIdentifierMessageTag;
v___x_2293_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
lean_ctor_set(v___x_2293_, 1, v_a_2288_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v___x_2293_);
v___x_2295_ = v___x_2290_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_2298_, lean_object* v_declHint_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2298_, v_declHint_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object* v_msgData_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2308_; lean_object* v_toCold_2309_; lean_object* v_env_2310_; lean_object* v_options_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2308_ = lean_st_ref_get(v___y_2306_);
v_toCold_2309_ = lean_ctor_get(v___y_2305_, 0);
v_env_2310_ = lean_ctor_get(v___x_2308_, 0);
lean_inc_ref(v_env_2310_);
lean_dec(v___x_2308_);
v_options_2311_ = lean_ctor_get(v_toCold_2309_, 2);
v___x_2312_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2313_ = lean_unsigned_to_nat(32u);
v___x_2314_ = lean_mk_empty_array_with_capacity(v___x_2313_);
lean_dec_ref(v___x_2314_);
v___x_2315_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
lean_inc_ref(v_options_2311_);
v___x_2316_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2316_, 0, v_env_2310_);
lean_ctor_set(v___x_2316_, 1, v___x_2312_);
lean_ctor_set(v___x_2316_, 2, v___x_2315_);
lean_ctor_set(v___x_2316_, 3, v_options_2311_);
v___x_2317_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
lean_ctor_set(v___x_2317_, 1, v_msgData_2304_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object* v_msgData_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_ref_2328_; lean_object* v___x_2329_; lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2338_; 
v_ref_2328_ = lean_ctor_get(v___y_2325_, 2);
v___x_2329_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_2324_, v___y_2325_, v___y_2326_);
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2338_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2338_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v___x_2336_; 
lean_inc(v_ref_2328_);
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v_ref_2328_);
lean_ctor_set(v___x_2334_, 1, v_a_2330_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set_tag(v___x_2332_, 1);
lean_ctor_set(v___x_2332_, 0, v___x_2334_);
v___x_2336_ = v___x_2332_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2339_, v___y_2340_, v___y_2341_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_2344_, lean_object* v_msg_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v_toCold_2349_; lean_object* v_currRecDepth_2350_; lean_object* v_ref_2351_; uint16_t v_optionFlags_2352_; uint8_t v_suppressElabErrors_2353_; uint8_t v_isRecordingDeps_2354_; lean_object* v_ref_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v_toCold_2349_ = lean_ctor_get(v___y_2346_, 0);
v_currRecDepth_2350_ = lean_ctor_get(v___y_2346_, 1);
v_ref_2351_ = lean_ctor_get(v___y_2346_, 2);
v_optionFlags_2352_ = lean_ctor_get_uint16(v___y_2346_, sizeof(void*)*3);
v_suppressElabErrors_2353_ = lean_ctor_get_uint8(v___y_2346_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2354_ = lean_ctor_get_uint8(v___y_2346_, sizeof(void*)*3 + 3);
v_ref_2355_ = l_Lean_replaceRef(v_ref_2344_, v_ref_2351_);
lean_inc(v_currRecDepth_2350_);
lean_inc_ref(v_toCold_2349_);
v___x_2356_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2356_, 0, v_toCold_2349_);
lean_ctor_set(v___x_2356_, 1, v_currRecDepth_2350_);
lean_ctor_set(v___x_2356_, 2, v_ref_2355_);
lean_ctor_set_uint16(v___x_2356_, sizeof(void*)*3, v_optionFlags_2352_);
lean_ctor_set_uint8(v___x_2356_, sizeof(void*)*3 + 2, v_suppressElabErrors_2353_);
lean_ctor_set_uint8(v___x_2356_, sizeof(void*)*3 + 3, v_isRecordingDeps_2354_);
v___x_2357_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2345_, v___x_2356_, v___y_2347_);
lean_dec_ref_known(v___x_2356_, 3);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_2358_, lean_object* v_msg_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2358_, v_msg_2359_, v___y_2360_, v___y_2361_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v_ref_2358_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_2364_, lean_object* v_msg_2365_, lean_object* v_declHint_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v___x_2370_; lean_object* v_a_2371_; lean_object* v___x_2372_; 
v___x_2370_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2365_, v_declHint_2366_, v___y_2367_, v___y_2368_);
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_a_2371_);
lean_dec_ref(v___x_2370_);
v___x_2372_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2364_, v_a_2371_, v___y_2367_, v___y_2368_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2373_, lean_object* v_msg_2374_, lean_object* v_declHint_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2373_, v_msg_2374_, v_declHint_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v_ref_2373_);
return v_res_2379_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_2382_ = l_Lean_stringToMessageData(v___x_2381_);
return v___x_2382_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2));
v___x_2385_ = l_Lean_stringToMessageData(v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_2386_, lean_object* v_constName_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v___x_2391_; uint8_t v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2391_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_2392_ = 0;
lean_inc(v_constName_2387_);
v___x_2393_ = l_Lean_MessageData_ofConstName(v_constName_2387_, v___x_2392_);
v___x_2394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2391_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_2396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2394_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
v___x_2397_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2386_, v___x_2396_, v_constName_2387_, v___y_2388_, v___y_2389_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2398_, lean_object* v_constName_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2398_, v_constName_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v_ref_2398_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v_ref_2408_; lean_object* v___x_2409_; 
v_ref_2408_ = lean_ctor_get(v___y_2405_, 2);
v___x_2409_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2408_, v_constName_2404_, v___y_2405_, v___y_2406_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object* v_constName_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v___x_2419_; lean_object* v_env_2420_; uint8_t v___x_2421_; lean_object* v___x_2422_; 
v___x_2419_ = lean_st_ref_get(v___y_2417_);
v_env_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc_ref(v_env_2420_);
lean_dec(v___x_2419_);
v___x_2421_ = 0;
lean_inc(v_constName_2415_);
v___x_2422_ = l_Lean_Environment_findConstVal_x3f(v_env_2420_, v_constName_2415_, v___x_2421_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2415_, v___y_2416_, v___y_2417_);
return v___x_2423_;
}
else
{
lean_object* v_val_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_dec(v_constName_2415_);
v_val_2424_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2422_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_val_2424_);
lean_dec(v___x_2422_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set_tag(v___x_2426_, 0);
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_val_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2432_, v___y_2433_, v___y_2434_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
if (lean_obj_tag(v_a_2437_) == 0)
{
lean_object* v___x_2439_; 
v___x_2439_ = l_List_reverse___redArg(v_a_2438_);
return v___x_2439_;
}
else
{
lean_object* v_head_2440_; lean_object* v_tail_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2450_; 
v_head_2440_ = lean_ctor_get(v_a_2437_, 0);
v_tail_2441_ = lean_ctor_get(v_a_2437_, 1);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_a_2437_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2443_ = v_a_2437_;
v_isShared_2444_ = v_isSharedCheck_2450_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_tail_2441_);
lean_inc(v_head_2440_);
lean_dec(v_a_2437_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2450_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; lean_object* v___x_2447_; 
v___x_2445_ = l_Lean_mkLevelParam(v_head_2440_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 1, v_a_2438_);
lean_ctor_set(v___x_2443_, 0, v___x_2445_);
v___x_2447_ = v___x_2443_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v_a_2438_);
v___x_2447_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
v_a_2437_ = v_tail_2441_;
v_a_2438_ = v___x_2447_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object* v_constName_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v___x_2455_; 
lean_inc(v_constName_2451_);
v___x_2455_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2451_, v___y_2452_, v___y_2453_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2467_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2458_ = v___x_2455_;
v_isShared_2459_ = v_isSharedCheck_2467_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2455_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2467_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v_levelParams_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
v_levelParams_2460_ = lean_ctor_get(v_a_2456_, 1);
lean_inc(v_levelParams_2460_);
lean_dec(v_a_2456_);
v___x_2461_ = lean_box(0);
v___x_2462_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_2460_, v___x_2461_);
v___x_2463_ = l_Lean_mkConst(v_constName_2451_, v___x_2462_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v___x_2463_);
v___x_2465_ = v___x_2458_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec(v_constName_2451_);
v_a_2468_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2455_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2455_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object* v_constName_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object* v_stx_2481_, lean_object* v_n_2482_, lean_object* v_expectedType_x3f_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_2482_, v___y_2484_, v___y_2485_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2488_);
lean_dec_ref_known(v___x_2487_, 1);
v___x_2489_ = lean_box(0);
v___x_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
lean_ctor_set(v___x_2490_, 1, v_stx_2481_);
v___x_2491_ = l_Lean_LocalContext_empty;
v___x_2492_ = 0;
v___x_2493_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2493_, 0, v___x_2490_);
lean_ctor_set(v___x_2493_, 1, v___x_2491_);
lean_ctor_set(v___x_2493_, 2, v_expectedType_x3f_2483_);
lean_ctor_set(v___x_2493_, 3, v_a_2488_);
lean_ctor_set_uint8(v___x_2493_, sizeof(void*)*4, v___x_2492_);
lean_ctor_set_uint8(v___x_2493_, sizeof(void*)*4 + 1, v___x_2492_);
v___x_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
v___x_2495_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_2494_, v___y_2484_, v___y_2485_);
return v___x_2495_;
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec(v_expectedType_x3f_2483_);
lean_dec(v_stx_2481_);
v_a_2496_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2487_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2487_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object* v_stx_2504_, lean_object* v_n_2505_, lean_object* v_expectedType_x3f_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_2504_, v_n_2505_, v_expectedType_x3f_2506_, v___y_2507_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object* v_id_2511_, lean_object* v_expectedType_x3f_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_){
_start:
{
lean_object* v___x_2516_; 
lean_inc(v_id_2511_);
v___x_2516_ = l_Lean_realizeGlobalConstNoOverload(v_id_2511_, v_a_2513_, v_a_2514_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2544_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2519_ = v___x_2516_;
v_isShared_2520_ = v_isSharedCheck_2544_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2516_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2544_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; lean_object* v_infoState_2522_; uint8_t v_enabled_2523_; 
v___x_2521_ = lean_st_ref_get(v_a_2514_);
v_infoState_2522_ = lean_ctor_get(v___x_2521_, 8);
lean_inc_ref(v_infoState_2522_);
lean_dec(v___x_2521_);
v_enabled_2523_ = lean_ctor_get_uint8(v_infoState_2522_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2522_);
if (v_enabled_2523_ == 0)
{
lean_object* v___x_2525_; 
lean_dec(v_expectedType_x3f_2512_);
lean_dec(v_id_2511_);
if (v_isShared_2520_ == 0)
{
v___x_2525_ = v___x_2519_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2517_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
else
{
lean_object* v___x_2527_; 
lean_del_object(v___x_2519_);
lean_inc(v_a_2517_);
v___x_2527_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2511_, v_a_2517_, v_expectedType_x3f_2512_, v_a_2513_, v_a_2514_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; 
v_unused_2535_ = lean_ctor_get(v___x_2527_, 0);
lean_dec(v_unused_2535_);
v___x_2529_ = v___x_2527_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_dec(v___x_2527_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 0, v_a_2517_);
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2517_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec(v_a_2517_);
v_a_2536_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2527_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2527_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2512_);
lean_dec(v_id_2511_);
return v___x_2516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object* v_id_2545_, lean_object* v_expectedType_x3f_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_2545_, v_expectedType_x3f_2546_, v_a_2547_, v_a_2548_);
lean_dec(v_a_2548_);
lean_dec_ref(v_a_2547_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object* v_t_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2551_, v___y_2553_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_2556_, v___y_2557_, v___y_2558_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2561_, lean_object* v_constName_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2562_, v___y_2563_, v___y_2564_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2567_, lean_object* v_constName_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2567_, v_constName_2568_, v___y_2569_, v___y_2570_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2573_, lean_object* v_ref_2574_, lean_object* v_constName_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v___x_2579_; 
v___x_2579_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2574_, v_constName_2575_, v___y_2576_, v___y_2577_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2580_, lean_object* v_ref_2581_, lean_object* v_constName_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_2580_, v_ref_2581_, v_constName_2582_, v___y_2583_, v___y_2584_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v_ref_2581_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2587_, lean_object* v_ref_2588_, lean_object* v_msg_2589_, lean_object* v_declHint_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2588_, v_msg_2589_, v_declHint_2590_, v___y_2591_, v___y_2592_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2595_, lean_object* v_ref_2596_, lean_object* v_msg_2597_, lean_object* v_declHint_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_2595_, v_ref_2596_, v_msg_2597_, v_declHint_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v_ref_2596_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_2603_, lean_object* v_declHint_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v___x_2608_; 
v___x_2608_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2603_, v_declHint_2604_, v___y_2606_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2609_, lean_object* v_declHint_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2609_, v_declHint_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_2615_, lean_object* v_ref_2616_, lean_object* v_msg_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2616_, v_msg_2617_, v___y_2618_, v___y_2619_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2622_, lean_object* v_ref_2623_, lean_object* v_msg_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_2622_, v_ref_2623_, v_msg_2624_, v___y_2625_, v___y_2626_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v_ref_2623_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_2629_, lean_object* v_msg_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2630_, v___y_2631_, v___y_2632_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_2635_, lean_object* v_msg_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_2635_, v_msg_2636_, v___y_2637_, v___y_2638_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object* v_id_2641_, lean_object* v_expectedType_x3f_2642_, lean_object* v_as_x27_2643_, lean_object* v_b_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
if (lean_obj_tag(v_as_x27_2643_) == 0)
{
lean_object* v___x_2648_; 
lean_dec(v_expectedType_x3f_2642_);
lean_dec(v_id_2641_);
v___x_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2648_, 0, v_b_2644_);
return v___x_2648_;
}
else
{
lean_object* v_head_2649_; lean_object* v_tail_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v_head_2649_ = lean_ctor_get(v_as_x27_2643_, 0);
v_tail_2650_ = lean_ctor_get(v_as_x27_2643_, 1);
v___x_2651_ = lean_box(0);
lean_inc(v_expectedType_x3f_2642_);
lean_inc(v_head_2649_);
lean_inc(v_id_2641_);
v___x_2652_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2641_, v_head_2649_, v_expectedType_x3f_2642_, v___y_2645_, v___y_2646_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_dec_ref_known(v___x_2652_, 1);
v_as_x27_2643_ = v_tail_2650_;
v_b_2644_ = v___x_2651_;
goto _start;
}
else
{
lean_dec(v_expectedType_x3f_2642_);
lean_dec(v_id_2641_);
return v___x_2652_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object* v_id_2654_, lean_object* v_expectedType_x3f_2655_, lean_object* v_as_x27_2656_, lean_object* v_b_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2654_, v_expectedType_x3f_2655_, v_as_x27_2656_, v_b_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v_as_x27_2656_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object* v_id_2662_, lean_object* v_expectedType_x3f_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v___x_2667_; 
lean_inc(v_id_2662_);
v___x_2667_ = l_Lean_realizeGlobalConst(v_id_2662_, v_a_2664_, v_a_2665_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2696_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2696_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2696_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; lean_object* v_infoState_2673_; uint8_t v_enabled_2674_; 
v___x_2672_ = lean_st_ref_get(v_a_2665_);
v_infoState_2673_ = lean_ctor_get(v___x_2672_, 8);
lean_inc_ref(v_infoState_2673_);
lean_dec(v___x_2672_);
v_enabled_2674_ = lean_ctor_get_uint8(v_infoState_2673_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2673_);
if (v_enabled_2674_ == 0)
{
lean_object* v___x_2676_; 
lean_dec(v_expectedType_x3f_2663_);
lean_dec(v_id_2662_);
if (v_isShared_2671_ == 0)
{
v___x_2676_ = v___x_2670_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2668_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
else
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_del_object(v___x_2670_);
v___x_2678_ = lean_box(0);
v___x_2679_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2662_, v_expectedType_x3f_2663_, v_a_2668_, v___x_2678_, v_a_2664_, v_a_2665_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2686_ == 0)
{
lean_object* v_unused_2687_; 
v_unused_2687_ = lean_ctor_get(v___x_2679_, 0);
lean_dec(v_unused_2687_);
v___x_2681_ = v___x_2679_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_dec(v___x_2679_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v_a_2668_);
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2668_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec(v_a_2668_);
v_a_2688_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2679_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2679_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2663_);
lean_dec(v_id_2662_);
return v___x_2667_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object* v_id_2697_, lean_object* v_expectedType_x3f_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_2697_, v_expectedType_x3f_2698_, v_a_2699_, v_a_2700_);
lean_dec(v_a_2700_);
lean_dec_ref(v_a_2699_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object* v_id_2703_, lean_object* v_expectedType_x3f_2704_, lean_object* v_as_2705_, lean_object* v_as_x27_2706_, lean_object* v_b_2707_, lean_object* v_a_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2703_, v_expectedType_x3f_2704_, v_as_x27_2706_, v_b_2707_, v___y_2709_, v___y_2710_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object* v_id_2713_, lean_object* v_expectedType_x3f_2714_, lean_object* v_as_2715_, lean_object* v_as_x27_2716_, lean_object* v_b_2717_, lean_object* v_a_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_2713_, v_expectedType_x3f_2714_, v_as_2715_, v_as_x27_2716_, v_b_2717_, v_a_2718_, v___y_2719_, v___y_2720_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v_as_x27_2716_);
lean_dec(v_as_2715_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object* v_ref_2723_, lean_object* v_as_x27_2724_, lean_object* v_b_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
if (lean_obj_tag(v_as_x27_2724_) == 0)
{
lean_object* v___x_2729_; 
lean_dec(v_ref_2723_);
v___x_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2729_, 0, v_b_2725_);
return v___x_2729_;
}
else
{
lean_object* v_head_2730_; lean_object* v_tail_2731_; lean_object* v_fst_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v_head_2730_ = lean_ctor_get(v_as_x27_2724_, 0);
v_tail_2731_ = lean_ctor_get(v_as_x27_2724_, 1);
v_fst_2732_ = lean_ctor_get(v_head_2730_, 0);
v___x_2733_ = lean_box(0);
v___x_2734_ = lean_box(0);
lean_inc(v_fst_2732_);
lean_inc(v_ref_2723_);
v___x_2735_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_2723_, v_fst_2732_, v___x_2734_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_dec_ref_known(v___x_2735_, 1);
v_as_x27_2724_ = v_tail_2731_;
v_b_2725_ = v___x_2733_;
goto _start;
}
else
{
lean_dec(v_ref_2723_);
return v___x_2735_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object* v_ref_2737_, lean_object* v_as_x27_2738_, lean_object* v_b_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2737_, v_as_x27_2738_, v_b_2739_, v___y_2740_, v___y_2741_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v_as_x27_2738_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object* v_ref_2744_, lean_object* v_id_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Lean_realizeGlobalName(v_id_2745_, v_a_2746_, v_a_2747_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2778_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2752_ = v___x_2749_;
v_isShared_2753_ = v_isSharedCheck_2778_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2749_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2778_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2754_; lean_object* v_infoState_2755_; uint8_t v_enabled_2756_; 
v___x_2754_ = lean_st_ref_get(v_a_2747_);
v_infoState_2755_ = lean_ctor_get(v___x_2754_, 8);
lean_inc_ref(v_infoState_2755_);
lean_dec(v___x_2754_);
v_enabled_2756_ = lean_ctor_get_uint8(v_infoState_2755_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2755_);
if (v_enabled_2756_ == 0)
{
lean_object* v___x_2758_; 
lean_dec(v_ref_2744_);
if (v_isShared_2753_ == 0)
{
v___x_2758_ = v___x_2752_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2750_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
else
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
lean_del_object(v___x_2752_);
v___x_2760_ = lean_box(0);
v___x_2761_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2744_, v_a_2750_, v___x_2760_, v_a_2746_, v_a_2747_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2768_ == 0)
{
lean_object* v_unused_2769_; 
v_unused_2769_ = lean_ctor_get(v___x_2761_, 0);
lean_dec(v_unused_2769_);
v___x_2763_ = v___x_2761_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_dec(v___x_2761_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v_a_2750_);
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2750_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v_a_2750_);
v_a_2770_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2761_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2761_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
}
}
else
{
lean_dec(v_ref_2744_);
return v___x_2749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object* v_ref_2779_, lean_object* v_id_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_2779_, v_id_2780_, v_a_2781_, v_a_2782_);
lean_dec(v_a_2782_);
lean_dec_ref(v_a_2781_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object* v_ref_2785_, lean_object* v_as_2786_, lean_object* v_as_x27_2787_, lean_object* v_b_2788_, lean_object* v_a_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2785_, v_as_x27_2787_, v_b_2788_, v___y_2790_, v___y_2791_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object* v_ref_2794_, lean_object* v_as_2795_, lean_object* v_as_x27_2796_, lean_object* v_b_2797_, lean_object* v_a_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_2794_, v_as_2795_, v_as_x27_2796_, v_b_2797_, v_a_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v_as_x27_2796_);
lean_dec(v_as_2795_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object* v_self_2803_){
_start:
{
lean_object* v_fst_2804_; 
v_fst_2804_ = lean_ctor_get(v_self_2803_, 0);
lean_inc(v_fst_2804_);
return v_fst_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object* v_self_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_2805_);
lean_dec_ref(v_self_2805_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object* v_info_2807_, lean_object* v_treesSaved_2808_, lean_object* v_s_2809_){
_start:
{
if (lean_obj_tag(v_info_2807_) == 0)
{
uint8_t v_enabled_2810_; lean_object* v_assignment_2811_; lean_object* v_lazyAssignment_2812_; lean_object* v_trees_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2823_; 
v_enabled_2810_ = lean_ctor_get_uint8(v_s_2809_, sizeof(void*)*3);
v_assignment_2811_ = lean_ctor_get(v_s_2809_, 0);
v_lazyAssignment_2812_ = lean_ctor_get(v_s_2809_, 1);
v_trees_2813_ = lean_ctor_get(v_s_2809_, 2);
v_isSharedCheck_2823_ = !lean_is_exclusive(v_s_2809_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2815_ = v_s_2809_;
v_isShared_2816_ = v_isSharedCheck_2823_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_trees_2813_);
lean_inc(v_lazyAssignment_2812_);
lean_inc(v_assignment_2811_);
lean_dec(v_s_2809_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2823_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v_val_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2821_; 
v_val_2817_ = lean_ctor_get(v_info_2807_, 0);
lean_inc(v_val_2817_);
lean_dec_ref_known(v_info_2807_, 1);
v___x_2818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2818_, 0, v_val_2817_);
lean_ctor_set(v___x_2818_, 1, v_trees_2813_);
v___x_2819_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2808_, v___x_2818_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 2, v___x_2819_);
v___x_2821_ = v___x_2815_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_assignment_2811_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_lazyAssignment_2812_);
lean_ctor_set(v_reuseFailAlloc_2822_, 2, v___x_2819_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, sizeof(void*)*3, v_enabled_2810_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
else
{
uint8_t v_enabled_2824_; lean_object* v_assignment_2825_; lean_object* v_lazyAssignment_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2842_; 
v_enabled_2824_ = lean_ctor_get_uint8(v_s_2809_, sizeof(void*)*3);
v_assignment_2825_ = lean_ctor_get(v_s_2809_, 0);
v_lazyAssignment_2826_ = lean_ctor_get(v_s_2809_, 1);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_s_2809_);
if (v_isSharedCheck_2842_ == 0)
{
lean_object* v_unused_2843_; 
v_unused_2843_ = lean_ctor_get(v_s_2809_, 2);
lean_dec(v_unused_2843_);
v___x_2828_ = v_s_2809_;
v_isShared_2829_ = v_isSharedCheck_2842_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_lazyAssignment_2826_);
lean_inc(v_assignment_2825_);
lean_dec(v_s_2809_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2842_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v_val_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2841_; 
v_val_2830_ = lean_ctor_get(v_info_2807_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_info_2807_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2832_ = v_info_2807_;
v_isShared_2833_ = v_isSharedCheck_2841_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_val_2830_);
lean_dec(v_info_2807_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2841_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
lean_ctor_set_tag(v___x_2832_, 2);
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_val_2830_);
v___x_2835_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
lean_object* v___x_2836_; lean_object* v___x_2838_; 
v___x_2836_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2808_, v___x_2835_);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 2, v___x_2836_);
v___x_2838_ = v___x_2828_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_assignment_2825_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_lazyAssignment_2826_);
lean_ctor_set(v_reuseFailAlloc_2839_, 2, v___x_2836_);
lean_ctor_set_uint8(v_reuseFailAlloc_2839_, sizeof(void*)*3, v_enabled_2824_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object* v_treesSaved_2844_, lean_object* v_modifyInfoState_2845_, lean_object* v_info_2846_){
_start:
{
lean_object* v___f_2847_; lean_object* v___x_2848_; 
v___f_2847_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2847_, 0, v_info_2846_);
lean_closure_set(v___f_2847_, 1, v_treesSaved_2844_);
v___x_2848_ = lean_apply_1(v_modifyInfoState_2845_, v___f_2847_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object* v___f_2849_, lean_object* v_info_2850_){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = lean_apply_1(v___f_2849_, v_info_2850_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object* v_toPure_2852_, lean_object* v_toBind_2853_, lean_object* v___f_2854_, lean_object* v_____do__lift_2855_){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2856_, 0, v_____do__lift_2855_);
v___x_2857_ = lean_apply_2(v_toPure_2852_, lean_box(0), v___x_2856_);
v___x_2858_ = lean_apply_4(v_toBind_2853_, lean_box(0), lean_box(0), v___x_2857_, v___f_2854_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object* v_toBind_2859_, lean_object* v_mkInfoOnError_2860_, lean_object* v___f_2861_, lean_object* v_mkInfo_2862_, lean_object* v___f_2863_, lean_object* v_a_x3f_2864_){
_start:
{
if (lean_obj_tag(v_a_x3f_2864_) == 0)
{
lean_object* v___x_2865_; 
lean_dec(v___f_2863_);
lean_dec(v_mkInfo_2862_);
v___x_2865_ = lean_apply_4(v_toBind_2859_, lean_box(0), lean_box(0), v_mkInfoOnError_2860_, v___f_2861_);
return v___x_2865_;
}
else
{
lean_object* v_val_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
lean_dec(v___f_2861_);
lean_dec(v_mkInfoOnError_2860_);
v_val_2866_ = lean_ctor_get(v_a_x3f_2864_, 0);
lean_inc(v_val_2866_);
lean_dec_ref_known(v_a_x3f_2864_, 1);
v___x_2867_ = lean_apply_1(v_mkInfo_2862_, v_val_2866_);
v___x_2868_ = lean_apply_4(v_toBind_2859_, lean_box(0), lean_box(0), v___x_2867_, v___f_2863_);
return v___x_2868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object* v_toFunctor_2869_, lean_object* v_modifyInfoState_2870_, lean_object* v_toPure_2871_, lean_object* v_toBind_2872_, lean_object* v_mkInfoOnError_2873_, lean_object* v_mkInfo_2874_, lean_object* v_inst_2875_, lean_object* v_x_2876_, lean_object* v___f_2877_, lean_object* v_treesSaved_2878_){
_start:
{
lean_object* v_map_2879_; lean_object* v___f_2880_; lean_object* v___f_2881_; lean_object* v___f_2882_; lean_object* v___f_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v_map_2879_ = lean_ctor_get(v_toFunctor_2869_, 0);
lean_inc(v_map_2879_);
lean_dec_ref(v_toFunctor_2869_);
v___f_2880_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2880_, 0, v_treesSaved_2878_);
lean_closure_set(v___f_2880_, 1, v_modifyInfoState_2870_);
v___f_2881_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2881_, 0, v___f_2880_);
lean_inc_ref(v___f_2881_);
lean_inc(v_toBind_2872_);
v___f_2882_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_2882_, 0, v_toPure_2871_);
lean_closure_set(v___f_2882_, 1, v_toBind_2872_);
lean_closure_set(v___f_2882_, 2, v___f_2881_);
v___f_2883_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__6), 6, 5);
lean_closure_set(v___f_2883_, 0, v_toBind_2872_);
lean_closure_set(v___f_2883_, 1, v_mkInfoOnError_2873_);
lean_closure_set(v___f_2883_, 2, v___f_2882_);
lean_closure_set(v___f_2883_, 3, v_mkInfo_2874_);
lean_closure_set(v___f_2883_, 4, v___f_2881_);
v___x_2884_ = lean_apply_4(v_inst_2875_, lean_box(0), lean_box(0), v_x_2876_, v___f_2883_);
v___x_2885_ = lean_apply_4(v_map_2879_, lean_box(0), lean_box(0), v___f_2877_, v___x_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object* v_x_2886_, lean_object* v_inst_2887_, lean_object* v_inst_2888_, lean_object* v_toBind_2889_, lean_object* v___f_2890_, lean_object* v_____do__lift_2891_){
_start:
{
uint8_t v_enabled_2892_; 
v_enabled_2892_ = lean_ctor_get_uint8(v_____do__lift_2891_, sizeof(void*)*3);
if (v_enabled_2892_ == 0)
{
lean_dec(v___f_2890_);
lean_dec(v_toBind_2889_);
lean_dec_ref(v_inst_2888_);
lean_dec_ref(v_inst_2887_);
lean_inc(v_x_2886_);
return v_x_2886_;
}
else
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2893_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2887_, v_inst_2888_);
v___x_2894_ = lean_apply_4(v_toBind_2889_, lean_box(0), lean_box(0), v___x_2893_, v___f_2890_);
return v___x_2894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object* v_x_2895_, lean_object* v_inst_2896_, lean_object* v_inst_2897_, lean_object* v_toBind_2898_, lean_object* v___f_2899_, lean_object* v_____do__lift_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__7(v_x_2895_, v_inst_2896_, v_inst_2897_, v_toBind_2898_, v___f_2899_, v_____do__lift_2900_);
lean_dec_ref(v_____do__lift_2900_);
lean_dec(v_x_2895_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object* v_inst_2903_, lean_object* v_inst_2904_, lean_object* v_inst_2905_, lean_object* v_x_2906_, lean_object* v_mkInfo_2907_, lean_object* v_mkInfoOnError_2908_){
_start:
{
lean_object* v_toApplicative_2909_; lean_object* v_toBind_2910_; lean_object* v_getInfoState_2911_; lean_object* v_modifyInfoState_2912_; lean_object* v_toFunctor_2913_; lean_object* v_toPure_2914_; lean_object* v___f_2915_; lean_object* v___f_2916_; lean_object* v___f_2917_; lean_object* v___x_2918_; 
v_toApplicative_2909_ = lean_ctor_get(v_inst_2903_, 0);
v_toBind_2910_ = lean_ctor_get(v_inst_2903_, 1);
lean_inc_n(v_toBind_2910_, 3);
v_getInfoState_2911_ = lean_ctor_get(v_inst_2904_, 0);
lean_inc(v_getInfoState_2911_);
v_modifyInfoState_2912_ = lean_ctor_get(v_inst_2904_, 1);
v_toFunctor_2913_ = lean_ctor_get(v_toApplicative_2909_, 0);
v_toPure_2914_ = lean_ctor_get(v_toApplicative_2909_, 1);
v___f_2915_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2906_);
lean_inc(v_toPure_2914_);
lean_inc(v_modifyInfoState_2912_);
lean_inc_ref(v_toFunctor_2913_);
v___f_2916_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__5), 10, 9);
lean_closure_set(v___f_2916_, 0, v_toFunctor_2913_);
lean_closure_set(v___f_2916_, 1, v_modifyInfoState_2912_);
lean_closure_set(v___f_2916_, 2, v_toPure_2914_);
lean_closure_set(v___f_2916_, 3, v_toBind_2910_);
lean_closure_set(v___f_2916_, 4, v_mkInfoOnError_2908_);
lean_closure_set(v___f_2916_, 5, v_mkInfo_2907_);
lean_closure_set(v___f_2916_, 6, v_inst_2905_);
lean_closure_set(v___f_2916_, 7, v_x_2906_);
lean_closure_set(v___f_2916_, 8, v___f_2915_);
v___f_2917_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2917_, 0, v_x_2906_);
lean_closure_set(v___f_2917_, 1, v_inst_2903_);
lean_closure_set(v___f_2917_, 2, v_inst_2904_);
lean_closure_set(v___f_2917_, 3, v_toBind_2910_);
lean_closure_set(v___f_2917_, 4, v___f_2916_);
v___x_2918_ = lean_apply_4(v_toBind_2910_, lean_box(0), lean_box(0), v_getInfoState_2911_, v___f_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* v_m_2919_, lean_object* v_inst_2920_, lean_object* v_inst_2921_, lean_object* v_00_u03b1_2922_, lean_object* v_inst_2923_, lean_object* v_x_2924_, lean_object* v_mkInfo_2925_, lean_object* v_mkInfoOnError_2926_){
_start:
{
lean_object* v___x_2927_; 
v___x_2927_ = l_Lean_Elab_withInfoContext_x27___redArg(v_inst_2920_, v_inst_2921_, v_inst_2923_, v_x_2924_, v_mkInfo_2925_, v_mkInfoOnError_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object* v_treesSaved_2928_, lean_object* v_tree_2929_, lean_object* v_s_2930_){
_start:
{
uint8_t v_enabled_2931_; lean_object* v_assignment_2932_; lean_object* v_lazyAssignment_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2941_; 
v_enabled_2931_ = lean_ctor_get_uint8(v_s_2930_, sizeof(void*)*3);
v_assignment_2932_ = lean_ctor_get(v_s_2930_, 0);
v_lazyAssignment_2933_ = lean_ctor_get(v_s_2930_, 1);
v_isSharedCheck_2941_ = !lean_is_exclusive(v_s_2930_);
if (v_isSharedCheck_2941_ == 0)
{
lean_object* v_unused_2942_; 
v_unused_2942_ = lean_ctor_get(v_s_2930_, 2);
lean_dec(v_unused_2942_);
v___x_2935_ = v_s_2930_;
v_isShared_2936_ = v_isSharedCheck_2941_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_lazyAssignment_2933_);
lean_inc(v_assignment_2932_);
lean_dec(v_s_2930_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2941_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2937_; lean_object* v___x_2939_; 
v___x_2937_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2928_, v_tree_2929_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 2, v___x_2937_);
v___x_2939_ = v___x_2935_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_assignment_2932_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_lazyAssignment_2933_);
lean_ctor_set(v_reuseFailAlloc_2940_, 2, v___x_2937_);
lean_ctor_set_uint8(v_reuseFailAlloc_2940_, sizeof(void*)*3, v_enabled_2931_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object* v_treesSaved_2943_, lean_object* v_modifyInfoState_2944_, lean_object* v_tree_2945_){
_start:
{
lean_object* v___f_2946_; lean_object* v___x_2947_; 
v___f_2946_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2946_, 0, v_treesSaved_2943_);
lean_closure_set(v___f_2946_, 1, v_tree_2945_);
v___x_2947_ = lean_apply_1(v_modifyInfoState_2944_, v___f_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object* v_mkInfoTree_2948_, lean_object* v_toBind_2949_, lean_object* v___f_2950_, lean_object* v_st_2951_){
_start:
{
lean_object* v_trees_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v_trees_2952_ = lean_ctor_get(v_st_2951_, 2);
lean_inc_ref(v_trees_2952_);
lean_dec_ref(v_st_2951_);
v___x_2953_ = lean_apply_1(v_mkInfoTree_2948_, v_trees_2952_);
v___x_2954_ = lean_apply_4(v_toBind_2949_, lean_box(0), lean_box(0), v___x_2953_, v___f_2950_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object* v_toBind_2955_, lean_object* v_getInfoState_2956_, lean_object* v___f_2957_, lean_object* v_x_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = lean_apply_4(v_toBind_2955_, lean_box(0), lean_box(0), v_getInfoState_2956_, v___f_2957_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object* v_toBind_2960_, lean_object* v_getInfoState_2961_, lean_object* v___f_2962_, lean_object* v_x_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(v_toBind_2960_, v_getInfoState_2961_, v___f_2962_, v_x_2963_);
lean_dec(v_x_2963_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object* v_toFunctor_2965_, lean_object* v_modifyInfoState_2966_, lean_object* v_mkInfoTree_2967_, lean_object* v_toBind_2968_, lean_object* v_getInfoState_2969_, lean_object* v_inst_2970_, lean_object* v_x_2971_, lean_object* v___f_2972_, lean_object* v_treesSaved_2973_){
_start:
{
lean_object* v_map_2974_; lean_object* v___f_2975_; lean_object* v___f_2976_; lean_object* v___f_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v_map_2974_ = lean_ctor_get(v_toFunctor_2965_, 0);
lean_inc(v_map_2974_);
lean_dec_ref(v_toFunctor_2965_);
v___f_2975_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2975_, 0, v_treesSaved_2973_);
lean_closure_set(v___f_2975_, 1, v_modifyInfoState_2966_);
lean_inc(v_toBind_2968_);
v___f_2976_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2976_, 0, v_mkInfoTree_2967_);
lean_closure_set(v___f_2976_, 1, v_toBind_2968_);
lean_closure_set(v___f_2976_, 2, v___f_2975_);
v___f_2977_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_2977_, 0, v_toBind_2968_);
lean_closure_set(v___f_2977_, 1, v_getInfoState_2969_);
lean_closure_set(v___f_2977_, 2, v___f_2976_);
v___x_2978_ = lean_apply_4(v_inst_2970_, lean_box(0), lean_box(0), v_x_2971_, v___f_2977_);
v___x_2979_ = lean_apply_4(v_map_2974_, lean_box(0), lean_box(0), v___f_2972_, v___x_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object* v_inst_2980_, lean_object* v_inst_2981_, lean_object* v_inst_2982_, lean_object* v_x_2983_, lean_object* v_mkInfoTree_2984_){
_start:
{
lean_object* v_toApplicative_2985_; lean_object* v_toBind_2986_; lean_object* v_getInfoState_2987_; lean_object* v_modifyInfoState_2988_; lean_object* v_toFunctor_2989_; lean_object* v___f_2990_; lean_object* v___f_2991_; lean_object* v___f_2992_; lean_object* v___x_2993_; 
v_toApplicative_2985_ = lean_ctor_get(v_inst_2980_, 0);
v_toBind_2986_ = lean_ctor_get(v_inst_2980_, 1);
lean_inc_n(v_toBind_2986_, 3);
v_getInfoState_2987_ = lean_ctor_get(v_inst_2981_, 0);
lean_inc_n(v_getInfoState_2987_, 2);
v_modifyInfoState_2988_ = lean_ctor_get(v_inst_2981_, 1);
v_toFunctor_2989_ = lean_ctor_get(v_toApplicative_2985_, 0);
v___f_2990_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2983_);
lean_inc(v_modifyInfoState_2988_);
lean_inc_ref(v_toFunctor_2989_);
v___f_2991_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2991_, 0, v_toFunctor_2989_);
lean_closure_set(v___f_2991_, 1, v_modifyInfoState_2988_);
lean_closure_set(v___f_2991_, 2, v_mkInfoTree_2984_);
lean_closure_set(v___f_2991_, 3, v_toBind_2986_);
lean_closure_set(v___f_2991_, 4, v_getInfoState_2987_);
lean_closure_set(v___f_2991_, 5, v_inst_2982_);
lean_closure_set(v___f_2991_, 6, v_x_2983_);
lean_closure_set(v___f_2991_, 7, v___f_2990_);
v___f_2992_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2992_, 0, v_x_2983_);
lean_closure_set(v___f_2992_, 1, v_inst_2980_);
lean_closure_set(v___f_2992_, 2, v_inst_2981_);
lean_closure_set(v___f_2992_, 3, v_toBind_2986_);
lean_closure_set(v___f_2992_, 4, v___f_2991_);
v___x_2993_ = lean_apply_4(v_toBind_2986_, lean_box(0), lean_box(0), v_getInfoState_2987_, v___f_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object* v_m_2994_, lean_object* v_inst_2995_, lean_object* v_inst_2996_, lean_object* v_00_u03b1_2997_, lean_object* v_inst_2998_, lean_object* v_x_2999_, lean_object* v_mkInfoTree_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_2995_, v_inst_2996_, v_inst_2998_, v_x_2999_, v_mkInfoTree_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object* v_trees_3002_, lean_object* v_toPure_3003_, lean_object* v_____do__lift_3004_){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3005_, 0, v_____do__lift_3004_);
lean_ctor_set(v___x_3005_, 1, v_trees_3002_);
v___x_3006_ = lean_apply_2(v_toPure_3003_, lean_box(0), v___x_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object* v_toPure_3007_, lean_object* v_toBind_3008_, lean_object* v_mkInfo_3009_, lean_object* v_trees_3010_){
_start:
{
lean_object* v___f_3011_; lean_object* v___x_3012_; 
v___f_3011_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3011_, 0, v_trees_3010_);
lean_closure_set(v___f_3011_, 1, v_toPure_3007_);
v___x_3012_ = lean_apply_4(v_toBind_3008_, lean_box(0), lean_box(0), v_mkInfo_3009_, v___f_3011_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object* v_inst_3013_, lean_object* v_inst_3014_, lean_object* v_inst_3015_, lean_object* v_x_3016_, lean_object* v_mkInfo_3017_){
_start:
{
lean_object* v_toApplicative_3018_; lean_object* v_toBind_3019_; lean_object* v_toPure_3020_; lean_object* v___f_3021_; lean_object* v___x_3022_; 
v_toApplicative_3018_ = lean_ctor_get(v_inst_3013_, 0);
v_toBind_3019_ = lean_ctor_get(v_inst_3013_, 1);
v_toPure_3020_ = lean_ctor_get(v_toApplicative_3018_, 1);
lean_inc(v_toBind_3019_);
lean_inc(v_toPure_3020_);
v___f_3021_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3021_, 0, v_toPure_3020_);
lean_closure_set(v___f_3021_, 1, v_toBind_3019_);
lean_closure_set(v___f_3021_, 2, v_mkInfo_3017_);
v___x_3022_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3013_, v_inst_3014_, v_inst_3015_, v_x_3016_, v___f_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object* v_m_3023_, lean_object* v_inst_3024_, lean_object* v_inst_3025_, lean_object* v_00_u03b1_3026_, lean_object* v_inst_3027_, lean_object* v_x_3028_, lean_object* v_mkInfo_3029_){
_start:
{
lean_object* v_toApplicative_3030_; lean_object* v_toBind_3031_; lean_object* v_toPure_3032_; lean_object* v___f_3033_; lean_object* v___x_3034_; 
v_toApplicative_3030_ = lean_ctor_get(v_inst_3024_, 0);
v_toBind_3031_ = lean_ctor_get(v_inst_3024_, 1);
v_toPure_3032_ = lean_ctor_get(v_toApplicative_3030_, 1);
lean_inc(v_toBind_3031_);
lean_inc(v_toPure_3032_);
v___f_3033_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3033_, 0, v_toPure_3032_);
lean_closure_set(v___f_3033_, 1, v_toBind_3031_);
lean_closure_set(v___f_3033_, 2, v_mkInfo_3029_);
v___x_3034_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3024_, v_inst_3025_, v_inst_3027_, v_x_3028_, v___f_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object* v_treesSaved_3035_, lean_object* v_trees_3036_, lean_object* v_s_3037_){
_start:
{
uint8_t v_enabled_3038_; lean_object* v_assignment_3039_; lean_object* v_lazyAssignment_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3048_; 
v_enabled_3038_ = lean_ctor_get_uint8(v_s_3037_, sizeof(void*)*3);
v_assignment_3039_ = lean_ctor_get(v_s_3037_, 0);
v_lazyAssignment_3040_ = lean_ctor_get(v_s_3037_, 1);
v_isSharedCheck_3048_ = !lean_is_exclusive(v_s_3037_);
if (v_isSharedCheck_3048_ == 0)
{
lean_object* v_unused_3049_; 
v_unused_3049_ = lean_ctor_get(v_s_3037_, 2);
lean_dec(v_unused_3049_);
v___x_3042_ = v_s_3037_;
v_isShared_3043_ = v_isSharedCheck_3048_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_lazyAssignment_3040_);
lean_inc(v_assignment_3039_);
lean_dec(v_s_3037_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3048_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3044_ = l_Lean_PersistentArray_append___redArg(v_treesSaved_3035_, v_trees_3036_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 2, v___x_3044_);
v___x_3046_ = v___x_3042_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_assignment_3039_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v_lazyAssignment_3040_);
lean_ctor_set(v_reuseFailAlloc_3047_, 2, v___x_3044_);
lean_ctor_set_uint8(v_reuseFailAlloc_3047_, sizeof(void*)*3, v_enabled_3038_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object* v_treesSaved_3050_, lean_object* v_trees_3051_, lean_object* v_s_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_3050_, v_trees_3051_, v_s_3052_);
lean_dec_ref(v_trees_3051_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object* v_treesSaved_3054_, lean_object* v_modifyInfoState_3055_, lean_object* v_trees_3056_){
_start:
{
lean_object* v___f_3057_; lean_object* v___x_3058_; 
v___f_3057_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3057_, 0, v_treesSaved_3054_);
lean_closure_set(v___f_3057_, 1, v_trees_3056_);
v___x_3058_ = lean_apply_1(v_modifyInfoState_3055_, v___f_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object* v_toPure_3059_, lean_object* v_tree_3060_, lean_object* v_____do__lift_3061_){
_start:
{
if (lean_obj_tag(v_____do__lift_3061_) == 0)
{
lean_object* v___x_3062_; 
v___x_3062_ = lean_apply_2(v_toPure_3059_, lean_box(0), v_tree_3060_);
return v___x_3062_;
}
else
{
lean_object* v_val_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v_val_3063_ = lean_ctor_get(v_____do__lift_3061_, 0);
lean_inc(v_val_3063_);
v___x_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3064_, 0, v_val_3063_);
lean_ctor_set(v___x_3064_, 1, v_tree_3060_);
v___x_3065_ = lean_apply_2(v_toPure_3059_, lean_box(0), v___x_3064_);
return v___x_3065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object* v_toPure_3066_, lean_object* v_tree_3067_, lean_object* v_____do__lift_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_3066_, v_tree_3067_, v_____do__lift_3068_);
lean_dec(v_____do__lift_3068_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object* v_assignment_3070_, lean_object* v_toPure_3071_, lean_object* v_toBind_3072_, lean_object* v_ctx_x3f_3073_, lean_object* v_tree_3074_){
_start:
{
lean_object* v_tree_3075_; lean_object* v___f_3076_; lean_object* v___x_3077_; 
v_tree_3075_ = l_Lean_Elab_InfoTree_substitute(v_tree_3074_, v_assignment_3070_);
v___f_3076_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3076_, 0, v_toPure_3071_);
lean_closure_set(v___f_3076_, 1, v_tree_3075_);
v___x_3077_ = lean_apply_4(v_toBind_3072_, lean_box(0), lean_box(0), v_ctx_x3f_3073_, v___f_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object* v_assignment_3078_, lean_object* v_toPure_3079_, lean_object* v_toBind_3080_, lean_object* v_ctx_x3f_3081_, lean_object* v_tree_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(v_assignment_3078_, v_toPure_3079_, v_toBind_3080_, v_ctx_x3f_3081_, v_tree_3082_);
lean_dec_ref(v_assignment_3078_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object* v_toPure_3084_, lean_object* v_toBind_3085_, lean_object* v_ctx_x3f_3086_, lean_object* v_inst_3087_, lean_object* v___f_3088_, lean_object* v_st_3089_){
_start:
{
lean_object* v_assignment_3090_; lean_object* v_trees_3091_; lean_object* v___f_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v_assignment_3090_ = lean_ctor_get(v_st_3089_, 0);
lean_inc_ref(v_assignment_3090_);
v_trees_3091_ = lean_ctor_get(v_st_3089_, 2);
lean_inc_ref(v_trees_3091_);
lean_dec_ref(v_st_3089_);
lean_inc(v_toBind_3085_);
v___f_3092_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_3092_, 0, v_assignment_3090_);
lean_closure_set(v___f_3092_, 1, v_toPure_3084_);
lean_closure_set(v___f_3092_, 2, v_toBind_3085_);
lean_closure_set(v___f_3092_, 3, v_ctx_x3f_3086_);
v___x_3093_ = l_Lean_PersistentArray_mapM___redArg(v_inst_3087_, v___f_3092_, v_trees_3091_);
v___x_3094_ = lean_apply_4(v_toBind_3085_, lean_box(0), lean_box(0), v___x_3093_, v___f_3088_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object* v_toFunctor_3095_, lean_object* v_modifyInfoState_3096_, lean_object* v_toPure_3097_, lean_object* v_toBind_3098_, lean_object* v_ctx_x3f_3099_, lean_object* v_inst_3100_, lean_object* v_getInfoState_3101_, lean_object* v_inst_3102_, lean_object* v_x_3103_, lean_object* v___f_3104_, lean_object* v_treesSaved_3105_){
_start:
{
lean_object* v_map_3106_; lean_object* v___f_3107_; lean_object* v___f_3108_; lean_object* v___f_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v_map_3106_ = lean_ctor_get(v_toFunctor_3095_, 0);
lean_inc(v_map_3106_);
lean_dec_ref(v_toFunctor_3095_);
v___f_3107_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3107_, 0, v_treesSaved_3105_);
lean_closure_set(v___f_3107_, 1, v_modifyInfoState_3096_);
lean_inc(v_toBind_3098_);
v___f_3108_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4), 6, 5);
lean_closure_set(v___f_3108_, 0, v_toPure_3097_);
lean_closure_set(v___f_3108_, 1, v_toBind_3098_);
lean_closure_set(v___f_3108_, 2, v_ctx_x3f_3099_);
lean_closure_set(v___f_3108_, 3, v_inst_3100_);
lean_closure_set(v___f_3108_, 4, v___f_3107_);
v___f_3109_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3109_, 0, v_toBind_3098_);
lean_closure_set(v___f_3109_, 1, v_getInfoState_3101_);
lean_closure_set(v___f_3109_, 2, v___f_3108_);
v___x_3110_ = lean_apply_4(v_inst_3102_, lean_box(0), lean_box(0), v_x_3103_, v___f_3109_);
v___x_3111_ = lean_apply_4(v_map_3106_, lean_box(0), lean_box(0), v___f_3104_, v___x_3110_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object* v_inst_3112_, lean_object* v_inst_3113_, lean_object* v_inst_3114_, lean_object* v_x_3115_, lean_object* v_ctx_x3f_3116_){
_start:
{
lean_object* v_toApplicative_3117_; lean_object* v_toBind_3118_; lean_object* v_getInfoState_3119_; lean_object* v_modifyInfoState_3120_; lean_object* v_toFunctor_3121_; lean_object* v_toPure_3122_; lean_object* v___f_3123_; lean_object* v___f_3124_; lean_object* v___f_3125_; lean_object* v___x_3126_; 
v_toApplicative_3117_ = lean_ctor_get(v_inst_3112_, 0);
v_toBind_3118_ = lean_ctor_get(v_inst_3112_, 1);
lean_inc_n(v_toBind_3118_, 3);
v_getInfoState_3119_ = lean_ctor_get(v_inst_3113_, 0);
lean_inc_n(v_getInfoState_3119_, 2);
v_modifyInfoState_3120_ = lean_ctor_get(v_inst_3113_, 1);
v_toFunctor_3121_ = lean_ctor_get(v_toApplicative_3117_, 0);
v_toPure_3122_ = lean_ctor_get(v_toApplicative_3117_, 1);
v___f_3123_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3115_);
lean_inc_ref(v_inst_3112_);
lean_inc(v_toPure_3122_);
lean_inc(v_modifyInfoState_3120_);
lean_inc_ref(v_toFunctor_3121_);
v___f_3124_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6), 11, 10);
lean_closure_set(v___f_3124_, 0, v_toFunctor_3121_);
lean_closure_set(v___f_3124_, 1, v_modifyInfoState_3120_);
lean_closure_set(v___f_3124_, 2, v_toPure_3122_);
lean_closure_set(v___f_3124_, 3, v_toBind_3118_);
lean_closure_set(v___f_3124_, 4, v_ctx_x3f_3116_);
lean_closure_set(v___f_3124_, 5, v_inst_3112_);
lean_closure_set(v___f_3124_, 6, v_getInfoState_3119_);
lean_closure_set(v___f_3124_, 7, v_inst_3114_);
lean_closure_set(v___f_3124_, 8, v_x_3115_);
lean_closure_set(v___f_3124_, 9, v___f_3123_);
v___f_3125_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3125_, 0, v_x_3115_);
lean_closure_set(v___f_3125_, 1, v_inst_3112_);
lean_closure_set(v___f_3125_, 2, v_inst_3113_);
lean_closure_set(v___f_3125_, 3, v_toBind_3118_);
lean_closure_set(v___f_3125_, 4, v___f_3124_);
v___x_3126_ = lean_apply_4(v_toBind_3118_, lean_box(0), lean_box(0), v_getInfoState_3119_, v___f_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object* v_m_3127_, lean_object* v_inst_3128_, lean_object* v_inst_3129_, lean_object* v_00_u03b1_3130_, lean_object* v_inst_3131_, lean_object* v_x_3132_, lean_object* v_ctx_x3f_3133_){
_start:
{
lean_object* v___x_3134_; 
v___x_3134_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3128_, v_inst_3129_, v_inst_3131_, v_x_3132_, v_ctx_x3f_3133_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object* v_toPure_3135_, lean_object* v_____do__lift_3136_){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3137_, 0, v_____do__lift_3136_);
v___x_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
v___x_3139_ = lean_apply_2(v_toPure_3135_, lean_box(0), v___x_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object* v_inst_3140_, lean_object* v_inst_3141_, lean_object* v_inst_3142_, lean_object* v_inst_3143_, lean_object* v_inst_3144_, lean_object* v_inst_3145_, lean_object* v_inst_3146_, lean_object* v_inst_3147_, lean_object* v_inst_3148_, lean_object* v_x_3149_){
_start:
{
lean_object* v_toApplicative_3150_; lean_object* v_toBind_3151_; lean_object* v_toPure_3152_; lean_object* v___x_3153_; lean_object* v___f_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v_toApplicative_3150_ = lean_ctor_get(v_inst_3140_, 0);
v_toBind_3151_ = lean_ctor_get(v_inst_3140_, 1);
v_toPure_3152_ = lean_ctor_get(v_toApplicative_3150_, 1);
lean_inc_ref(v_inst_3140_);
v___x_3153_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_3140_, v_inst_3144_, v_inst_3146_, v_inst_3145_, v_inst_3147_, v_inst_3142_, v_inst_3148_);
lean_inc(v_toPure_3152_);
v___f_3154_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3154_, 0, v_toPure_3152_);
lean_inc(v_toBind_3151_);
v___x_3155_ = lean_apply_4(v_toBind_3151_, lean_box(0), lean_box(0), v___x_3153_, v___f_3154_);
v___x_3156_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3140_, v_inst_3141_, v_inst_3143_, v_x_3149_, v___x_3155_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object* v_m_3157_, lean_object* v_inst_3158_, lean_object* v_inst_3159_, lean_object* v_00_u03b1_3160_, lean_object* v_inst_3161_, lean_object* v_inst_3162_, lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_inst_3165_, lean_object* v_inst_3166_, lean_object* v_inst_3167_, lean_object* v_x_3168_){
_start:
{
lean_object* v___x_3169_; 
v___x_3169_ = l_Lean_Elab_withSaveInfoContext___redArg(v_inst_3158_, v_inst_3159_, v_inst_3161_, v_inst_3162_, v_inst_3163_, v_inst_3164_, v_inst_3165_, v_inst_3166_, v_inst_3167_, v_x_3168_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object* v_toPure_3170_, lean_object* v_____x_3171_){
_start:
{
if (lean_obj_tag(v_____x_3171_) == 1)
{
lean_object* v_val_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3181_; 
v_val_3172_ = lean_ctor_get(v_____x_3171_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v_____x_3171_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3174_ = v_____x_3171_;
v_isShared_3175_ = v_isSharedCheck_3181_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_val_3172_);
lean_dec(v_____x_3171_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3181_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v___x_3178_; 
v___x_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3176_, 0, v_val_3172_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v___x_3176_);
v___x_3178_ = v___x_3174_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v___x_3176_);
v___x_3178_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
lean_object* v___x_3179_; 
v___x_3179_ = lean_apply_2(v_toPure_3170_, lean_box(0), v___x_3178_);
return v___x_3179_;
}
}
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
lean_dec(v_____x_3171_);
v___x_3182_ = lean_box(0);
v___x_3183_ = lean_apply_2(v_toPure_3170_, lean_box(0), v___x_3182_);
return v___x_3183_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object* v_inst_3184_, lean_object* v_inst_3185_, lean_object* v_inst_3186_, lean_object* v_inst_3187_, lean_object* v_x_3188_){
_start:
{
lean_object* v_toApplicative_3189_; lean_object* v_toBind_3190_; lean_object* v_toPure_3191_; lean_object* v___f_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v_toApplicative_3189_ = lean_ctor_get(v_inst_3184_, 0);
v_toBind_3190_ = lean_ctor_get(v_inst_3184_, 1);
v_toPure_3191_ = lean_ctor_get(v_toApplicative_3189_, 1);
lean_inc(v_toPure_3191_);
v___f_3192_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3192_, 0, v_toPure_3191_);
lean_inc(v_toBind_3190_);
v___x_3193_ = lean_apply_4(v_toBind_3190_, lean_box(0), lean_box(0), v_inst_3187_, v___f_3192_);
v___x_3194_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3184_, v_inst_3185_, v_inst_3186_, v_x_3188_, v___x_3193_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object* v_m_3195_, lean_object* v_inst_3196_, lean_object* v_inst_3197_, lean_object* v_00_u03b1_3198_, lean_object* v_inst_3199_, lean_object* v_inst_3200_, lean_object* v_x_3201_){
_start:
{
lean_object* v___x_3202_; 
v___x_3202_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(v_inst_3196_, v_inst_3197_, v_inst_3199_, v_inst_3200_, v_x_3201_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object* v_toPure_3203_, lean_object* v_autoImplicits_3204_){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3205_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3205_, 0, v_autoImplicits_3204_);
v___x_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
v___x_3207_ = lean_apply_2(v_toPure_3203_, lean_box(0), v___x_3206_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object* v_inst_3208_, lean_object* v_inst_3209_, lean_object* v_inst_3210_, lean_object* v_inst_3211_, lean_object* v_x_3212_){
_start:
{
lean_object* v_toApplicative_3213_; lean_object* v_toBind_3214_; lean_object* v_toPure_3215_; lean_object* v___f_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v_toApplicative_3213_ = lean_ctor_get(v_inst_3208_, 0);
v_toBind_3214_ = lean_ctor_get(v_inst_3208_, 1);
v_toPure_3215_ = lean_ctor_get(v_toApplicative_3213_, 1);
lean_inc(v_toPure_3215_);
v___f_3216_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3216_, 0, v_toPure_3215_);
lean_inc(v_toBind_3214_);
v___x_3217_ = lean_apply_4(v_toBind_3214_, lean_box(0), lean_box(0), v_inst_3211_, v___f_3216_);
v___x_3218_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3208_, v_inst_3209_, v_inst_3210_, v_x_3212_, v___x_3217_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object* v_m_3219_, lean_object* v_inst_3220_, lean_object* v_inst_3221_, lean_object* v_00_u03b1_3222_, lean_object* v_inst_3223_, lean_object* v_inst_3224_, lean_object* v_x_3225_){
_start:
{
lean_object* v___x_3226_; 
v___x_3226_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(v_inst_3220_, v_inst_3221_, v_inst_3223_, v_inst_3224_, v_x_3225_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object* v___x_3227_, lean_object* v___x_3228_, lean_object* v_mvarId_3229_, lean_object* v_toPure_3230_, lean_object* v_____do__lift_3231_){
_start:
{
lean_object* v_assignment_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v_assignment_3232_ = lean_ctor_get(v_____do__lift_3231_, 0);
v___x_3233_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_3227_, v___x_3228_, v_assignment_3232_, v_mvarId_3229_);
v___x_3234_ = lean_apply_2(v_toPure_3230_, lean_box(0), v___x_3233_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object* v___x_3235_, lean_object* v___x_3236_, lean_object* v_mvarId_3237_, lean_object* v_toPure_3238_, lean_object* v_____do__lift_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(v___x_3235_, v___x_3236_, v_mvarId_3237_, v_toPure_3238_, v_____do__lift_3239_);
lean_dec_ref(v_____do__lift_3239_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object* v_inst_3243_, lean_object* v_inst_3244_, lean_object* v_mvarId_3245_){
_start:
{
lean_object* v_toApplicative_3246_; lean_object* v_toBind_3247_; lean_object* v_getInfoState_3248_; lean_object* v_toPure_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___f_3252_; lean_object* v___x_3253_; 
v_toApplicative_3246_ = lean_ctor_get(v_inst_3243_, 0);
lean_inc_ref(v_toApplicative_3246_);
v_toBind_3247_ = lean_ctor_get(v_inst_3243_, 1);
lean_inc(v_toBind_3247_);
lean_dec_ref(v_inst_3243_);
v_getInfoState_3248_ = lean_ctor_get(v_inst_3244_, 0);
lean_inc(v_getInfoState_3248_);
lean_dec_ref(v_inst_3244_);
v_toPure_3249_ = lean_ctor_get(v_toApplicative_3246_, 1);
lean_inc(v_toPure_3249_);
lean_dec_ref(v_toApplicative_3246_);
v___x_3250_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3251_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___f_3252_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3252_, 0, v___x_3250_);
lean_closure_set(v___f_3252_, 1, v___x_3251_);
lean_closure_set(v___f_3252_, 2, v_mvarId_3245_);
lean_closure_set(v___f_3252_, 3, v_toPure_3249_);
v___x_3253_ = lean_apply_4(v_toBind_3247_, lean_box(0), lean_box(0), v_getInfoState_3248_, v___f_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* v_m_3254_, lean_object* v_inst_3255_, lean_object* v_inst_3256_, lean_object* v_mvarId_3257_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3255_, v_inst_3256_, v_mvarId_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object* v___x_3259_, lean_object* v___x_3260_, lean_object* v_mvarId_3261_, lean_object* v_infoTree_3262_, lean_object* v_s_3263_){
_start:
{
uint8_t v_enabled_3264_; lean_object* v_assignment_3265_; lean_object* v_lazyAssignment_3266_; lean_object* v_trees_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3275_; 
v_enabled_3264_ = lean_ctor_get_uint8(v_s_3263_, sizeof(void*)*3);
v_assignment_3265_ = lean_ctor_get(v_s_3263_, 0);
v_lazyAssignment_3266_ = lean_ctor_get(v_s_3263_, 1);
v_trees_3267_ = lean_ctor_get(v_s_3263_, 2);
v_isSharedCheck_3275_ = !lean_is_exclusive(v_s_3263_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3269_ = v_s_3263_;
v_isShared_3270_ = v_isSharedCheck_3275_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_trees_3267_);
lean_inc(v_lazyAssignment_3266_);
lean_inc(v_assignment_3265_);
lean_dec(v_s_3263_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3275_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3271_; lean_object* v___x_3273_; 
v___x_3271_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3259_, v___x_3260_, v_assignment_3265_, v_mvarId_3261_, v_infoTree_3262_);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 0, v___x_3271_);
v___x_3273_ = v___x_3269_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3271_);
lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_lazyAssignment_3266_);
lean_ctor_set(v_reuseFailAlloc_3274_, 2, v_trees_3267_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, sizeof(void*)*3, v_enabled_3264_);
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
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3279_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2));
v___x_3280_ = lean_unsigned_to_nat(2u);
v___x_3281_ = lean_unsigned_to_nat(384u);
v___x_3282_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1));
v___x_3283_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0));
v___x_3284_ = l_mkPanicMessageWithDecl(v___x_3283_, v___x_3282_, v___x_3281_, v___x_3280_, v___x_3279_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object* v_inst_3285_, lean_object* v___f_3286_, lean_object* v___x_3287_, lean_object* v_____do__lift_3288_){
_start:
{
if (lean_obj_tag(v_____do__lift_3288_) == 0)
{
lean_object* v_modifyInfoState_3289_; lean_object* v___x_3290_; 
v_modifyInfoState_3289_ = lean_ctor_get(v_inst_3285_, 1);
lean_inc(v_modifyInfoState_3289_);
lean_dec_ref(v_inst_3285_);
v___x_3290_ = lean_apply_1(v_modifyInfoState_3289_, v___f_3286_);
return v___x_3290_;
}
else
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
lean_dec_ref(v___f_3286_);
lean_dec_ref(v_inst_3285_);
v___x_3291_ = lean_obj_once(&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3, &l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3_once, _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3);
v___x_3292_ = l_panic___redArg(v___x_3287_, v___x_3291_);
return v___x_3292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object* v_inst_3293_, lean_object* v___f_3294_, lean_object* v___x_3295_, lean_object* v_____do__lift_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(v_inst_3293_, v___f_3294_, v___x_3295_, v_____do__lift_3296_);
lean_dec(v_____do__lift_3296_);
lean_dec(v___x_3295_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object* v_inst_3298_, lean_object* v_inst_3299_, lean_object* v_mvarId_3300_, lean_object* v_infoTree_3301_){
_start:
{
lean_object* v_toBind_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___f_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___f_3309_; lean_object* v___x_3310_; 
v_toBind_3302_ = lean_ctor_get(v_inst_3298_, 1);
lean_inc(v_toBind_3302_);
v___x_3303_ = lean_box(0);
v___x_3304_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3305_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
lean_inc(v_mvarId_3300_);
v___f_3306_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__0), 5, 4);
lean_closure_set(v___f_3306_, 0, v___x_3304_);
lean_closure_set(v___f_3306_, 1, v___x_3305_);
lean_closure_set(v___f_3306_, 2, v_mvarId_3300_);
lean_closure_set(v___f_3306_, 3, v_infoTree_3301_);
lean_inc_ref(v_inst_3299_);
lean_inc_ref(v_inst_3298_);
v___x_3307_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3298_, v_inst_3299_, v_mvarId_3300_);
v___x_3308_ = l_instInhabitedOfMonad___redArg(v_inst_3298_, v___x_3303_);
v___f_3309_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3309_, 0, v_inst_3299_);
lean_closure_set(v___f_3309_, 1, v___f_3306_);
lean_closure_set(v___f_3309_, 2, v___x_3308_);
v___x_3310_ = lean_apply_4(v_toBind_3302_, lean_box(0), lean_box(0), v___x_3307_, v___f_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* v_m_3311_, lean_object* v_inst_3312_, lean_object* v_inst_3313_, lean_object* v_mvarId_3314_, lean_object* v_infoTree_3315_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l_Lean_Elab_assignInfoHoleId___redArg(v_inst_3312_, v_inst_3313_, v_mvarId_3314_, v_infoTree_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object* v_stx_3317_, lean_object* v_output_3318_, lean_object* v_toPure_3319_, lean_object* v_____do__lift_3320_){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3321_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3321_, 0, v_____do__lift_3320_);
lean_ctor_set(v___x_3321_, 1, v_stx_3317_);
lean_ctor_set(v___x_3321_, 2, v_output_3318_);
v___x_3322_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
v___x_3323_ = lean_apply_2(v_toPure_3319_, lean_box(0), v___x_3322_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object* v_inst_3324_, lean_object* v_inst_3325_, lean_object* v_inst_3326_, lean_object* v_inst_3327_, lean_object* v_stx_3328_, lean_object* v_output_3329_, lean_object* v_x_3330_){
_start:
{
lean_object* v_toApplicative_3331_; lean_object* v_toBind_3332_; lean_object* v_toPure_3333_; lean_object* v___f_3334_; lean_object* v_mkInfo_3335_; lean_object* v___f_3336_; lean_object* v___x_3337_; 
v_toApplicative_3331_ = lean_ctor_get(v_inst_3325_, 0);
v_toBind_3332_ = lean_ctor_get(v_inst_3325_, 1);
v_toPure_3333_ = lean_ctor_get(v_toApplicative_3331_, 1);
lean_inc_n(v_toPure_3333_, 2);
v___f_3334_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3334_, 0, v_stx_3328_);
lean_closure_set(v___f_3334_, 1, v_output_3329_);
lean_closure_set(v___f_3334_, 2, v_toPure_3333_);
lean_inc_n(v_toBind_3332_, 2);
v_mkInfo_3335_ = lean_apply_4(v_toBind_3332_, lean_box(0), lean_box(0), v_inst_3327_, v___f_3334_);
v___f_3336_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3336_, 0, v_toPure_3333_);
lean_closure_set(v___f_3336_, 1, v_toBind_3332_);
lean_closure_set(v___f_3336_, 2, v_mkInfo_3335_);
v___x_3337_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3325_, v_inst_3326_, v_inst_3324_, v_x_3330_, v___f_3336_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* v_m_3338_, lean_object* v_00_u03b1_3339_, lean_object* v_inst_3340_, lean_object* v_inst_3341_, lean_object* v_inst_3342_, lean_object* v_inst_3343_, lean_object* v_stx_3344_, lean_object* v_output_3345_, lean_object* v_x_3346_){
_start:
{
lean_object* v___x_3347_; 
v___x_3347_ = l_Lean_Elab_withMacroExpansionInfo___redArg(v_inst_3340_, v_inst_3341_, v_inst_3342_, v_inst_3343_, v_stx_3344_, v_output_3345_, v_x_3346_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object* v_treesSaved_3348_, lean_object* v___x_3349_, lean_object* v___x_3350_, lean_object* v___x_3351_, lean_object* v_mvarId_3352_, lean_object* v_s_3353_){
_start:
{
lean_object* v_trees_3354_; uint8_t v_enabled_3355_; lean_object* v_assignment_3356_; lean_object* v_lazyAssignment_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3374_; 
v_trees_3354_ = lean_ctor_get(v_s_3353_, 2);
v_enabled_3355_ = lean_ctor_get_uint8(v_s_3353_, sizeof(void*)*3);
v_assignment_3356_ = lean_ctor_get(v_s_3353_, 0);
v_lazyAssignment_3357_ = lean_ctor_get(v_s_3353_, 1);
v_isSharedCheck_3374_ = !lean_is_exclusive(v_s_3353_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3359_ = v_s_3353_;
v_isShared_3360_ = v_isSharedCheck_3374_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_trees_3354_);
lean_inc(v_lazyAssignment_3357_);
lean_inc(v_assignment_3356_);
lean_dec(v_s_3353_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3374_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v_size_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v_size_3361_ = lean_ctor_get(v_trees_3354_, 2);
v___x_3362_ = lean_unsigned_to_nat(0u);
v___x_3363_ = lean_nat_dec_lt(v___x_3362_, v_size_3361_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3365_; 
lean_dec_ref(v_trees_3354_);
lean_dec(v_mvarId_3352_);
lean_dec_ref(v___x_3351_);
lean_dec_ref(v___x_3350_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 2, v_treesSaved_3348_);
v___x_3365_ = v___x_3359_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_assignment_3356_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v_lazyAssignment_3357_);
lean_ctor_set(v_reuseFailAlloc_3366_, 2, v_treesSaved_3348_);
lean_ctor_set_uint8(v_reuseFailAlloc_3366_, sizeof(void*)*3, v_enabled_3355_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
else
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3372_; 
v___x_3367_ = lean_unsigned_to_nat(1u);
v___x_3368_ = lean_nat_sub(v_size_3361_, v___x_3367_);
v___x_3369_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3349_, v_trees_3354_, v___x_3368_);
lean_dec(v___x_3368_);
lean_dec_ref(v_trees_3354_);
v___x_3370_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3350_, v___x_3351_, v_assignment_3356_, v_mvarId_3352_, v___x_3369_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 2, v_treesSaved_3348_);
lean_ctor_set(v___x_3359_, 0, v___x_3370_);
v___x_3372_ = v___x_3359_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3370_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v_lazyAssignment_3357_);
lean_ctor_set(v_reuseFailAlloc_3373_, 2, v_treesSaved_3348_);
lean_ctor_set_uint8(v_reuseFailAlloc_3373_, sizeof(void*)*3, v_enabled_3355_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1___boxed(lean_object* v_treesSaved_3375_, lean_object* v___x_3376_, lean_object* v___x_3377_, lean_object* v___x_3378_, lean_object* v_mvarId_3379_, lean_object* v_s_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_Elab_withInfoHole___redArg___lam__1(v_treesSaved_3375_, v___x_3376_, v___x_3377_, v___x_3378_, v_mvarId_3379_, v_s_3380_);
lean_dec_ref(v___x_3376_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object* v_modifyInfoState_3382_, lean_object* v___f_3383_, lean_object* v_x_3384_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = lean_apply_1(v_modifyInfoState_3382_, v___f_3383_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object* v_modifyInfoState_3386_, lean_object* v___f_3387_, lean_object* v_x_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_3386_, v___f_3387_, v_x_3388_);
lean_dec(v_x_3388_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object* v_toFunctor_3390_, lean_object* v___x_3391_, lean_object* v___x_3392_, lean_object* v___x_3393_, lean_object* v_mvarId_3394_, lean_object* v_modifyInfoState_3395_, lean_object* v_inst_3396_, lean_object* v_x_3397_, lean_object* v___f_3398_, lean_object* v_treesSaved_3399_){
_start:
{
lean_object* v_map_3400_; lean_object* v___f_3401_; lean_object* v___f_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v_map_3400_ = lean_ctor_get(v_toFunctor_3390_, 0);
lean_inc(v_map_3400_);
lean_dec_ref(v_toFunctor_3390_);
v___f_3401_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_3401_, 0, v_treesSaved_3399_);
lean_closure_set(v___f_3401_, 1, v___x_3391_);
lean_closure_set(v___f_3401_, 2, v___x_3392_);
lean_closure_set(v___f_3401_, 3, v___x_3393_);
lean_closure_set(v___f_3401_, 4, v_mvarId_3394_);
v___f_3402_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3402_, 0, v_modifyInfoState_3395_);
lean_closure_set(v___f_3402_, 1, v___f_3401_);
v___x_3403_ = lean_apply_4(v_inst_3396_, lean_box(0), lean_box(0), v_x_3397_, v___f_3402_);
v___x_3404_ = lean_apply_4(v_map_3400_, lean_box(0), lean_box(0), v___f_3398_, v___x_3403_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object* v_inst_3405_, lean_object* v_inst_3406_, lean_object* v_inst_3407_, lean_object* v_mvarId_3408_, lean_object* v_x_3409_){
_start:
{
lean_object* v_toApplicative_3410_; lean_object* v_toBind_3411_; lean_object* v_getInfoState_3412_; lean_object* v_modifyInfoState_3413_; lean_object* v_toFunctor_3414_; lean_object* v___f_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___f_3419_; lean_object* v___f_3420_; lean_object* v___x_3421_; 
v_toApplicative_3410_ = lean_ctor_get(v_inst_3406_, 0);
v_toBind_3411_ = lean_ctor_get(v_inst_3406_, 1);
lean_inc_n(v_toBind_3411_, 2);
v_getInfoState_3412_ = lean_ctor_get(v_inst_3407_, 0);
lean_inc(v_getInfoState_3412_);
v_modifyInfoState_3413_ = lean_ctor_get(v_inst_3407_, 1);
v_toFunctor_3414_ = lean_ctor_get(v_toApplicative_3410_, 0);
v___f_3415_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
v___x_3416_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3417_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3418_ = l_Lean_Elab_instInhabitedInfoTree_default;
lean_inc(v_x_3409_);
lean_inc(v_modifyInfoState_3413_);
lean_inc_ref(v_toFunctor_3414_);
v___f_3419_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3419_, 0, v_toFunctor_3414_);
lean_closure_set(v___f_3419_, 1, v___x_3418_);
lean_closure_set(v___f_3419_, 2, v___x_3416_);
lean_closure_set(v___f_3419_, 3, v___x_3417_);
lean_closure_set(v___f_3419_, 4, v_mvarId_3408_);
lean_closure_set(v___f_3419_, 5, v_modifyInfoState_3413_);
lean_closure_set(v___f_3419_, 6, v_inst_3405_);
lean_closure_set(v___f_3419_, 7, v_x_3409_);
lean_closure_set(v___f_3419_, 8, v___f_3415_);
v___f_3420_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3420_, 0, v_x_3409_);
lean_closure_set(v___f_3420_, 1, v_inst_3406_);
lean_closure_set(v___f_3420_, 2, v_inst_3407_);
lean_closure_set(v___f_3420_, 3, v_toBind_3411_);
lean_closure_set(v___f_3420_, 4, v___f_3419_);
v___x_3421_ = lean_apply_4(v_toBind_3411_, lean_box(0), lean_box(0), v_getInfoState_3412_, v___f_3420_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object* v_m_3422_, lean_object* v_00_u03b1_3423_, lean_object* v_inst_3424_, lean_object* v_inst_3425_, lean_object* v_inst_3426_, lean_object* v_mvarId_3427_, lean_object* v_x_3428_){
_start:
{
lean_object* v_toApplicative_3429_; lean_object* v_toBind_3430_; lean_object* v_getInfoState_3431_; lean_object* v_modifyInfoState_3432_; lean_object* v_toFunctor_3433_; lean_object* v___f_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___f_3438_; lean_object* v___f_3439_; lean_object* v___x_3440_; 
v_toApplicative_3429_ = lean_ctor_get(v_inst_3425_, 0);
v_toBind_3430_ = lean_ctor_get(v_inst_3425_, 1);
lean_inc_n(v_toBind_3430_, 2);
v_getInfoState_3431_ = lean_ctor_get(v_inst_3426_, 0);
lean_inc(v_getInfoState_3431_);
v_modifyInfoState_3432_ = lean_ctor_get(v_inst_3426_, 1);
v_toFunctor_3433_ = lean_ctor_get(v_toApplicative_3429_, 0);
v___f_3434_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
v___x_3435_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3436_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3437_ = l_Lean_Elab_instInhabitedInfoTree_default;
lean_inc(v_x_3428_);
lean_inc(v_modifyInfoState_3432_);
lean_inc_ref(v_toFunctor_3433_);
v___f_3438_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3438_, 0, v_toFunctor_3433_);
lean_closure_set(v___f_3438_, 1, v___x_3437_);
lean_closure_set(v___f_3438_, 2, v___x_3435_);
lean_closure_set(v___f_3438_, 3, v___x_3436_);
lean_closure_set(v___f_3438_, 4, v_mvarId_3427_);
lean_closure_set(v___f_3438_, 5, v_modifyInfoState_3432_);
lean_closure_set(v___f_3438_, 6, v_inst_3424_);
lean_closure_set(v___f_3438_, 7, v_x_3428_);
lean_closure_set(v___f_3438_, 8, v___f_3434_);
v___f_3439_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3439_, 0, v_x_3428_);
lean_closure_set(v___f_3439_, 1, v_inst_3425_);
lean_closure_set(v___f_3439_, 2, v_inst_3426_);
lean_closure_set(v___f_3439_, 3, v_toBind_3430_);
lean_closure_set(v___f_3439_, 4, v___f_3438_);
v___x_3440_ = lean_apply_4(v_toBind_3430_, lean_box(0), lean_box(0), v_getInfoState_3431_, v___f_3439_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t v_flag_3441_, lean_object* v_s_3442_){
_start:
{
lean_object* v_assignment_3443_; lean_object* v_lazyAssignment_3444_; lean_object* v_trees_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
v_assignment_3443_ = lean_ctor_get(v_s_3442_, 0);
v_lazyAssignment_3444_ = lean_ctor_get(v_s_3442_, 1);
v_trees_3445_ = lean_ctor_get(v_s_3442_, 2);
v_isSharedCheck_3452_ = !lean_is_exclusive(v_s_3442_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v_s_3442_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_trees_3445_);
lean_inc(v_lazyAssignment_3444_);
lean_inc(v_assignment_3443_);
lean_dec(v_s_3442_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_assignment_3443_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_lazyAssignment_3444_);
lean_ctor_set(v_reuseFailAlloc_3451_, 2, v_trees_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_ctor_set_uint8(v___x_3450_, sizeof(void*)*3, v_flag_3441_);
return v___x_3450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object* v_flag_3453_, lean_object* v_s_3454_){
_start:
{
uint8_t v_flag_boxed_3455_; lean_object* v_res_3456_; 
v_flag_boxed_3455_ = lean_unbox(v_flag_3453_);
v_res_3456_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_3455_, v_s_3454_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object* v_inst_3457_, uint8_t v_flag_3458_){
_start:
{
lean_object* v_modifyInfoState_3459_; lean_object* v___x_3460_; lean_object* v___f_3461_; lean_object* v___x_3462_; 
v_modifyInfoState_3459_ = lean_ctor_get(v_inst_3457_, 1);
lean_inc(v_modifyInfoState_3459_);
lean_dec_ref(v_inst_3457_);
v___x_3460_ = lean_box(v_flag_3458_);
v___f_3461_ = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3461_, 0, v___x_3460_);
v___x_3462_ = lean_apply_1(v_modifyInfoState_3459_, v___f_3461_);
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object* v_inst_3463_, lean_object* v_flag_3464_){
_start:
{
uint8_t v_flag_boxed_3465_; lean_object* v_res_3466_; 
v_flag_boxed_3465_ = lean_unbox(v_flag_3464_);
v_res_3466_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3463_, v_flag_boxed_3465_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object* v_m_3467_, lean_object* v_inst_3468_, uint8_t v_flag_3469_){
_start:
{
lean_object* v___x_3470_; 
v___x_3470_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3468_, v_flag_3469_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object* v_m_3471_, lean_object* v_inst_3472_, lean_object* v_flag_3473_){
_start:
{
uint8_t v_flag_boxed_3474_; lean_object* v_res_3475_; 
v_flag_boxed_3474_ = lean_unbox(v_flag_3473_);
v_res_3475_ = l_Lean_Elab_enableInfoTree(v_m_3471_, v_inst_3472_, v_flag_boxed_3474_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object* v_x_3476_){
_start:
{
lean_object* v_fst_3477_; 
v_fst_3477_ = lean_ctor_get(v_x_3476_, 0);
lean_inc(v_fst_3477_);
return v_fst_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object* v_x_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_3478_);
lean_dec_ref(v_x_3478_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object* v_x_3480_, lean_object* v_____r_3481_){
_start:
{
lean_inc(v_x_3480_);
return v_x_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object* v_x_3482_, lean_object* v_____r_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_3482_, v_____r_3483_);
lean_dec(v_x_3482_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object* v___x_3485_, lean_object* v_x_3486_){
_start:
{
lean_inc(v___x_3485_);
return v___x_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object* v___x_3487_, lean_object* v_x_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_3487_, v_x_3488_);
lean_dec(v_x_3488_);
lean_dec(v___x_3487_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object* v_toFunctor_3490_, lean_object* v_inst_3491_, uint8_t v_flag_3492_, lean_object* v_toBind_3493_, lean_object* v___f_3494_, lean_object* v_inst_3495_, lean_object* v___f_3496_, lean_object* v_____do__lift_3497_){
_start:
{
uint8_t v_enabled_3498_; lean_object* v_map_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___f_3503_; lean_object* v_y_3504_; lean_object* v___x_3505_; 
v_enabled_3498_ = lean_ctor_get_uint8(v_____do__lift_3497_, sizeof(void*)*3);
v_map_3499_ = lean_ctor_get(v_toFunctor_3490_, 0);
lean_inc(v_map_3499_);
lean_dec_ref(v_toFunctor_3490_);
lean_inc_ref(v_inst_3491_);
v___x_3500_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3491_, v_flag_3492_);
v___x_3501_ = lean_apply_4(v_toBind_3493_, lean_box(0), lean_box(0), v___x_3500_, v___f_3494_);
v___x_3502_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3491_, v_enabled_3498_);
v___f_3503_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_3503_, 0, v___x_3502_);
v_y_3504_ = lean_apply_4(v_inst_3495_, lean_box(0), lean_box(0), v___x_3501_, v___f_3503_);
v___x_3505_ = lean_apply_4(v_map_3499_, lean_box(0), lean_box(0), v___f_3496_, v_y_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object* v_toFunctor_3506_, lean_object* v_inst_3507_, lean_object* v_flag_3508_, lean_object* v_toBind_3509_, lean_object* v___f_3510_, lean_object* v_inst_3511_, lean_object* v___f_3512_, lean_object* v_____do__lift_3513_){
_start:
{
uint8_t v_flag_boxed_3514_; lean_object* v_res_3515_; 
v_flag_boxed_3514_ = lean_unbox(v_flag_3508_);
v_res_3515_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_3506_, v_inst_3507_, v_flag_boxed_3514_, v_toBind_3509_, v___f_3510_, v_inst_3511_, v___f_3512_, v_____do__lift_3513_);
lean_dec_ref(v_____do__lift_3513_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object* v_inst_3517_, lean_object* v_inst_3518_, lean_object* v_inst_3519_, uint8_t v_flag_3520_, lean_object* v_x_3521_){
_start:
{
lean_object* v_toApplicative_3522_; lean_object* v_toBind_3523_; lean_object* v_getInfoState_3524_; lean_object* v_toFunctor_3525_; lean_object* v___f_3526_; lean_object* v___f_3527_; lean_object* v___x_3528_; lean_object* v___f_3529_; lean_object* v___x_3530_; 
v_toApplicative_3522_ = lean_ctor_get(v_inst_3517_, 0);
lean_inc_ref(v_toApplicative_3522_);
v_toBind_3523_ = lean_ctor_get(v_inst_3517_, 1);
lean_inc_n(v_toBind_3523_, 2);
lean_dec_ref(v_inst_3517_);
v_getInfoState_3524_ = lean_ctor_get(v_inst_3518_, 0);
lean_inc(v_getInfoState_3524_);
v_toFunctor_3525_ = lean_ctor_get(v_toApplicative_3522_, 0);
lean_inc_ref(v_toFunctor_3525_);
lean_dec_ref(v_toApplicative_3522_);
v___f_3526_ = ((lean_object*)(l_Lean_Elab_withEnableInfoTree___redArg___closed__0));
v___f_3527_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3527_, 0, v_x_3521_);
v___x_3528_ = lean_box(v_flag_3520_);
v___f_3529_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_3529_, 0, v_toFunctor_3525_);
lean_closure_set(v___f_3529_, 1, v_inst_3518_);
lean_closure_set(v___f_3529_, 2, v___x_3528_);
lean_closure_set(v___f_3529_, 3, v_toBind_3523_);
lean_closure_set(v___f_3529_, 4, v___f_3527_);
lean_closure_set(v___f_3529_, 5, v_inst_3519_);
lean_closure_set(v___f_3529_, 6, v___f_3526_);
v___x_3530_ = lean_apply_4(v_toBind_3523_, lean_box(0), lean_box(0), v_getInfoState_3524_, v___f_3529_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object* v_inst_3531_, lean_object* v_inst_3532_, lean_object* v_inst_3533_, lean_object* v_flag_3534_, lean_object* v_x_3535_){
_start:
{
uint8_t v_flag_boxed_3536_; lean_object* v_res_3537_; 
v_flag_boxed_3536_ = lean_unbox(v_flag_3534_);
v_res_3537_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3531_, v_inst_3532_, v_inst_3533_, v_flag_boxed_3536_, v_x_3535_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object* v_m_3538_, lean_object* v_00_u03b1_3539_, lean_object* v_inst_3540_, lean_object* v_inst_3541_, lean_object* v_inst_3542_, uint8_t v_flag_3543_, lean_object* v_x_3544_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3540_, v_inst_3541_, v_inst_3542_, v_flag_3543_, v_x_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object* v_m_3546_, lean_object* v_00_u03b1_3547_, lean_object* v_inst_3548_, lean_object* v_inst_3549_, lean_object* v_inst_3550_, lean_object* v_flag_3551_, lean_object* v_x_3552_){
_start:
{
uint8_t v_flag_boxed_3553_; lean_object* v_res_3554_; 
v_flag_boxed_3553_ = lean_unbox(v_flag_3551_);
v_res_3554_ = l_Lean_Elab_withEnableInfoTree(v_m_3546_, v_00_u03b1_3547_, v_inst_3548_, v_inst_3549_, v_inst_3550_, v_flag_boxed_3553_, v_x_3552_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object* v_toPure_3555_, lean_object* v_____do__lift_3556_){
_start:
{
lean_object* v_trees_3557_; lean_object* v___x_3558_; 
v_trees_3557_ = lean_ctor_get(v_____do__lift_3556_, 2);
lean_inc_ref(v_trees_3557_);
lean_dec_ref(v_____do__lift_3556_);
v___x_3558_ = lean_apply_2(v_toPure_3555_, lean_box(0), v_trees_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object* v_inst_3559_, lean_object* v_inst_3560_){
_start:
{
lean_object* v_toApplicative_3561_; lean_object* v_toBind_3562_; lean_object* v_getInfoState_3563_; lean_object* v_toPure_3564_; lean_object* v___f_3565_; lean_object* v___x_3566_; 
v_toApplicative_3561_ = lean_ctor_get(v_inst_3560_, 0);
lean_inc_ref(v_toApplicative_3561_);
v_toBind_3562_ = lean_ctor_get(v_inst_3560_, 1);
lean_inc(v_toBind_3562_);
lean_dec_ref(v_inst_3560_);
v_getInfoState_3563_ = lean_ctor_get(v_inst_3559_, 0);
lean_inc(v_getInfoState_3563_);
lean_dec_ref(v_inst_3559_);
v_toPure_3564_ = lean_ctor_get(v_toApplicative_3561_, 1);
lean_inc(v_toPure_3564_);
lean_dec_ref(v_toApplicative_3561_);
v___f_3565_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3565_, 0, v_toPure_3564_);
v___x_3566_ = lean_apply_4(v_toBind_3562_, lean_box(0), lean_box(0), v_getInfoState_3563_, v___f_3565_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object* v_m_3567_, lean_object* v_inst_3568_, lean_object* v_inst_3569_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_3568_, v_inst_3569_);
return v___x_3570_;
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
