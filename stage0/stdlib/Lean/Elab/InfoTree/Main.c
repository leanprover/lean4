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
extern lean_object* l_Lean_maxRecDepth;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
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
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__19;
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
v___x_198_ = l_Lean_NameSet_empty;
v___x_199_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6);
v___x_200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
lean_ctor_set(v___x_200_, 2, v___x_198_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; lean_object* v___x_204_; 
v___x_201_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6);
v___x_202_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9);
v___x_203_ = 1;
v___x_204_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_204_, 0, v___x_202_);
lean_ctor_set(v___x_204_, 1, v___x_202_);
lean_ctor_set(v___x_204_, 2, v___x_201_);
lean_ctor_set_uint8(v___x_204_, sizeof(void*)*3, v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = l_Lean_maxRecDepth;
v___x_209_ = l_Lean_Options_empty;
v___x_210_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v___x_209_, v___x_208_);
return v___x_210_;
}
}
static uint16_t _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18(void){
_start:
{
uint16_t v___x_211_; uint16_t v___x_212_; uint16_t v___x_213_; 
v___x_211_ = 512;
v___x_212_ = lean_uint16_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2);
v___x_213_ = lean_uint16_land(v___x_212_, v___x_211_);
return v___x_213_;
}
}
static uint8_t _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__19(void){
_start:
{
uint16_t v___x_214_; uint16_t v___x_215_; uint8_t v___x_216_; 
v___x_214_ = 0;
v___x_215_ = lean_uint16_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__18);
v___x_216_ = lean_uint16_dec_eq(v___x_215_, v___x_214_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg(lean_object* v_info_217_, lean_object* v_x_218_){
_start:
{
lean_object* v_a_221_; lean_object* v_toCommandContextInfo_224_; lean_object* v_env_225_; lean_object* v_options_226_; lean_object* v_currNamespace_227_; lean_object* v_openDecls_228_; lean_object* v_ngen_229_; uint8_t v___x_230_; lean_object* v_env_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint16_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___y_254_; uint16_t v___y_255_; lean_object* v_fileName_256_; lean_object* v_fileMap_257_; lean_object* v_currNamespace_258_; lean_object* v_openDecls_259_; lean_object* v_initHeartbeats_260_; lean_object* v_maxHeartbeats_261_; lean_object* v_quotContext_262_; lean_object* v_currMacroScope_263_; lean_object* v_cancelTk_x3f_264_; lean_object* v_inheritedTraceOptions_265_; lean_object* v_currRecDepth_266_; lean_object* v_ref_267_; uint8_t v_suppressElabErrors_268_; uint8_t v_isRecordingDeps_269_; lean_object* v___y_270_; uint8_t v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; uint16_t v___y_311_; lean_object* v_fileName_348_; lean_object* v_fileMap_349_; lean_object* v_currNamespace_350_; lean_object* v_openDecls_351_; lean_object* v_initHeartbeats_352_; lean_object* v_maxHeartbeats_353_; lean_object* v_quotContext_354_; lean_object* v_currMacroScope_355_; lean_object* v_cancelTk_x3f_356_; lean_object* v_inheritedTraceOptions_357_; lean_object* v_currRecDepth_358_; lean_object* v_ref_359_; uint8_t v_suppressElabErrors_360_; uint8_t v_isRecordingDeps_361_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___y_378_; lean_object* v_env_399_; uint8_t v___x_400_; uint8_t v___x_401_; 
v_toCommandContextInfo_224_ = lean_ctor_get(v_info_217_, 0);
lean_inc_ref(v_toCommandContextInfo_224_);
lean_dec_ref(v_info_217_);
v_env_225_ = lean_ctor_get(v_toCommandContextInfo_224_, 0);
lean_inc_ref(v_env_225_);
v_options_226_ = lean_ctor_get(v_toCommandContextInfo_224_, 4);
lean_inc_ref(v_options_226_);
v_currNamespace_227_ = lean_ctor_get(v_toCommandContextInfo_224_, 5);
lean_inc(v_currNamespace_227_);
v_openDecls_228_ = lean_ctor_get(v_toCommandContextInfo_224_, 6);
lean_inc(v_openDecls_228_);
v_ngen_229_ = lean_ctor_get(v_toCommandContextInfo_224_, 7);
lean_inc_ref(v_ngen_229_);
lean_dec_ref(v_toCommandContextInfo_224_);
v___x_230_ = 0;
v_env_231_ = l_Lean_Environment_setExporting(v_env_225_, v___x_230_);
v___x_232_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0));
v___x_233_ = l_Lean_instInhabitedFileMap_default;
v___x_234_ = l_Lean_Options_empty;
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_237_ = lean_box(0);
v___x_238_ = l_Lean_firstFrontendMacroScope;
v___x_239_ = lean_box(0);
v___x_240_ = lean_box(0);
v___x_241_ = lean_uint16_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2);
v___x_242_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3);
v___x_243_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4));
v___x_244_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7);
v___x_245_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10);
v___x_246_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11));
v___x_247_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12);
v___x_248_ = 1;
v___x_249_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13);
v___x_250_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_250_, 0, v_env_231_);
lean_ctor_set(v___x_250_, 1, v___x_242_);
lean_ctor_set(v___x_250_, 2, v_ngen_229_);
lean_ctor_set(v___x_250_, 3, v___x_243_);
lean_ctor_set(v___x_250_, 4, v___x_244_);
lean_ctor_set(v___x_250_, 5, v___x_245_);
lean_ctor_set(v___x_250_, 6, v___x_246_);
lean_ctor_set(v___x_250_, 7, v___x_247_);
lean_ctor_set(v___x_250_, 8, v___x_249_);
lean_ctor_set(v___x_250_, 9, v___x_246_);
v___x_251_ = lean_io_get_num_heartbeats();
v___x_252_ = lean_st_mk_ref(v___x_250_);
v___x_374_ = l_Lean_inheritedTraceOptions;
v___x_375_ = lean_st_ref_get(v___x_374_);
v___x_376_ = lean_st_ref_get(v___x_252_);
v_env_399_ = lean_ctor_get(v___x_376_, 0);
lean_inc_ref(v_env_399_);
lean_dec(v___x_376_);
v___x_400_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_399_);
lean_dec_ref(v_env_399_);
v___x_401_ = lean_uint8_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__19, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__19_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__19);
if (v___x_401_ == 0)
{
if (v___x_400_ == 0)
{
v___y_378_ = v___x_248_;
goto v___jp_377_;
}
else
{
v_fileName_348_ = v___x_232_;
v_fileMap_349_ = v___x_233_;
v_currNamespace_350_ = v_currNamespace_227_;
v_openDecls_351_ = v_openDecls_228_;
v_initHeartbeats_352_ = v___x_251_;
v_maxHeartbeats_353_ = v___x_236_;
v_quotContext_354_ = v___x_237_;
v_currMacroScope_355_ = v___x_238_;
v_cancelTk_x3f_356_ = v___x_239_;
v_inheritedTraceOptions_357_ = v___x_375_;
v_currRecDepth_358_ = v___x_235_;
v_ref_359_ = v___x_240_;
v_suppressElabErrors_360_ = v___x_230_;
v_isRecordingDeps_361_ = v___x_230_;
goto v___jp_347_;
}
}
else
{
if (v___x_400_ == 0)
{
v_fileName_348_ = v___x_232_;
v_fileMap_349_ = v___x_233_;
v_currNamespace_350_ = v_currNamespace_227_;
v_openDecls_351_ = v_openDecls_228_;
v_initHeartbeats_352_ = v___x_251_;
v_maxHeartbeats_353_ = v___x_236_;
v_quotContext_354_ = v___x_237_;
v_currMacroScope_355_ = v___x_238_;
v_cancelTk_x3f_356_ = v___x_239_;
v_inheritedTraceOptions_357_ = v___x_375_;
v_currRecDepth_358_ = v___x_235_;
v_ref_359_ = v___x_240_;
v_suppressElabErrors_360_ = v___x_230_;
v_isRecordingDeps_361_ = v___x_230_;
goto v___jp_347_;
}
else
{
v___y_378_ = v___x_230_;
goto v___jp_377_;
}
}
v___jp_220_:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_mk_io_user_error(v_a_221_);
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
return v___x_223_;
}
v___jp_253_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_271_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v_options_226_, v___y_254_);
v___x_272_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_272_, 0, v_fileName_256_);
lean_ctor_set(v___x_272_, 1, v_fileMap_257_);
lean_ctor_set(v___x_272_, 2, v_options_226_);
lean_ctor_set(v___x_272_, 3, v___x_271_);
lean_ctor_set(v___x_272_, 4, v_currNamespace_258_);
lean_ctor_set(v___x_272_, 5, v_openDecls_259_);
lean_ctor_set(v___x_272_, 6, v_initHeartbeats_260_);
lean_ctor_set(v___x_272_, 7, v_maxHeartbeats_261_);
lean_ctor_set(v___x_272_, 8, v_quotContext_262_);
lean_ctor_set(v___x_272_, 9, v_currMacroScope_263_);
lean_ctor_set(v___x_272_, 10, v_cancelTk_x3f_264_);
lean_ctor_set(v___x_272_, 11, v_inheritedTraceOptions_265_);
v___x_273_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v_currRecDepth_266_);
lean_ctor_set(v___x_273_, 2, v_ref_267_);
lean_ctor_set_uint16(v___x_273_, sizeof(void*)*3, v___y_255_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*3 + 2, v_suppressElabErrors_268_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*3 + 3, v_isRecordingDeps_269_);
v___x_274_ = lean_apply_3(v_x_218_, v___x_273_, v___y_270_, lean_box(0));
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_283_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_283_ == 0)
{
v___x_277_ = v___x_274_;
v_isShared_278_ = v_isSharedCheck_283_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_283_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_279_ = lean_st_ref_get(v___x_252_);
lean_dec(v___x_252_);
lean_dec(v___x_279_);
if (v_isShared_278_ == 0)
{
v___x_281_ = v___x_277_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_275_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_305_; 
lean_dec(v___x_252_);
v_a_284_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_305_ == 0)
{
v___x_286_ = v___x_274_;
v_isShared_287_ = v_isSharedCheck_305_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_274_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_305_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
if (lean_obj_tag(v_a_284_) == 0)
{
lean_object* v_msg_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
v_msg_288_ = lean_ctor_get(v_a_284_, 1);
lean_inc_ref(v_msg_288_);
lean_dec_ref_known(v_a_284_, 2);
v___x_289_ = l_Lean_MessageData_toString(v_msg_288_);
v___x_290_ = lean_mk_io_user_error(v___x_289_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_290_);
v___x_292_ = v___x_286_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
else
{
lean_object* v_id_294_; lean_object* v___x_295_; 
lean_del_object(v___x_286_);
v_id_294_ = lean_ctor_get(v_a_284_, 0);
lean_inc(v_id_294_);
lean_dec_ref_known(v_a_284_, 2);
v___x_295_ = l_Lean_InternalExceptionId_getName(v_id_294_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v_id_294_);
v_a_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_a_296_);
lean_dec_ref_known(v___x_295_, 1);
v___x_297_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14));
v___x_298_ = l_Lean_Name_toString(v_a_296_, v___x_248_);
v___x_299_ = lean_string_append(v___x_297_, v___x_298_);
lean_dec_ref(v___x_298_);
v_a_221_ = v___x_299_;
goto v___jp_220_;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec_ref_known(v___x_295_, 1);
v___x_300_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15));
v___x_301_ = l_Nat_reprFast(v_id_294_);
v___x_302_ = lean_string_append(v___x_300_, v___x_301_);
lean_dec_ref(v___x_301_);
v___x_303_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16));
v___x_304_ = lean_string_append(v___x_302_, v___x_303_);
v_a_221_ = v___x_304_;
goto v___jp_220_;
}
}
}
}
}
v___jp_306_:
{
lean_object* v___x_312_; lean_object* v_env_313_; lean_object* v_nextMacroScope_314_; lean_object* v_ngen_315_; lean_object* v_auxDeclNGen_316_; lean_object* v_traceState_317_; lean_object* v_recordedDeps_318_; lean_object* v_messages_319_; lean_object* v_infoState_320_; lean_object* v_snapshotTasks_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_345_; 
v___x_312_ = lean_st_ref_take(v___y_310_);
v_env_313_ = lean_ctor_get(v___x_312_, 0);
v_nextMacroScope_314_ = lean_ctor_get(v___x_312_, 1);
v_ngen_315_ = lean_ctor_get(v___x_312_, 2);
v_auxDeclNGen_316_ = lean_ctor_get(v___x_312_, 3);
v_traceState_317_ = lean_ctor_get(v___x_312_, 4);
v_recordedDeps_318_ = lean_ctor_get(v___x_312_, 6);
v_messages_319_ = lean_ctor_get(v___x_312_, 7);
v_infoState_320_ = lean_ctor_get(v___x_312_, 8);
v_snapshotTasks_321_ = lean_ctor_get(v___x_312_, 9);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_345_ == 0)
{
lean_object* v_unused_346_; 
v_unused_346_ = lean_ctor_get(v___x_312_, 5);
lean_dec(v_unused_346_);
v___x_323_ = v___x_312_;
v_isShared_324_ = v_isSharedCheck_345_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_snapshotTasks_321_);
lean_inc(v_infoState_320_);
lean_inc(v_messages_319_);
lean_inc(v_recordedDeps_318_);
lean_inc(v_traceState_317_);
lean_inc(v_auxDeclNGen_316_);
lean_inc(v_ngen_315_);
lean_inc(v_nextMacroScope_314_);
lean_inc(v_env_313_);
lean_dec(v___x_312_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_345_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = l_Lean_Kernel_enableDiag(v_env_313_, v___y_307_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 5, v___x_245_);
lean_ctor_set(v___x_323_, 0, v___x_325_);
v___x_327_ = v___x_323_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_nextMacroScope_314_);
lean_ctor_set(v_reuseFailAlloc_344_, 2, v_ngen_315_);
lean_ctor_set(v_reuseFailAlloc_344_, 3, v_auxDeclNGen_316_);
lean_ctor_set(v_reuseFailAlloc_344_, 4, v_traceState_317_);
lean_ctor_set(v_reuseFailAlloc_344_, 5, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_344_, 6, v_recordedDeps_318_);
lean_ctor_set(v_reuseFailAlloc_344_, 7, v_messages_319_);
lean_ctor_set(v_reuseFailAlloc_344_, 8, v_infoState_320_);
lean_ctor_set(v_reuseFailAlloc_344_, 9, v_snapshotTasks_321_);
v___x_327_ = v_reuseFailAlloc_344_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v_toCold_329_; lean_object* v_currRecDepth_330_; lean_object* v_ref_331_; uint8_t v_suppressElabErrors_332_; uint8_t v_isRecordingDeps_333_; lean_object* v_fileName_334_; lean_object* v_fileMap_335_; lean_object* v_currNamespace_336_; lean_object* v_openDecls_337_; lean_object* v_initHeartbeats_338_; lean_object* v_maxHeartbeats_339_; lean_object* v_quotContext_340_; lean_object* v_currMacroScope_341_; lean_object* v_cancelTk_x3f_342_; lean_object* v_inheritedTraceOptions_343_; 
v___x_328_ = lean_st_ref_put(v___y_310_, v___x_327_);
v_toCold_329_ = lean_ctor_get(v___y_309_, 0);
lean_inc_ref(v_toCold_329_);
v_currRecDepth_330_ = lean_ctor_get(v___y_309_, 1);
lean_inc(v_currRecDepth_330_);
v_ref_331_ = lean_ctor_get(v___y_309_, 2);
lean_inc(v_ref_331_);
v_suppressElabErrors_332_ = lean_ctor_get_uint8(v___y_309_, sizeof(void*)*3 + 2);
v_isRecordingDeps_333_ = lean_ctor_get_uint8(v___y_309_, sizeof(void*)*3 + 3);
lean_dec_ref(v___y_309_);
v_fileName_334_ = lean_ctor_get(v_toCold_329_, 0);
lean_inc_ref(v_fileName_334_);
v_fileMap_335_ = lean_ctor_get(v_toCold_329_, 1);
lean_inc_ref(v_fileMap_335_);
v_currNamespace_336_ = lean_ctor_get(v_toCold_329_, 4);
lean_inc(v_currNamespace_336_);
v_openDecls_337_ = lean_ctor_get(v_toCold_329_, 5);
lean_inc(v_openDecls_337_);
v_initHeartbeats_338_ = lean_ctor_get(v_toCold_329_, 6);
lean_inc(v_initHeartbeats_338_);
v_maxHeartbeats_339_ = lean_ctor_get(v_toCold_329_, 7);
lean_inc(v_maxHeartbeats_339_);
v_quotContext_340_ = lean_ctor_get(v_toCold_329_, 8);
lean_inc(v_quotContext_340_);
v_currMacroScope_341_ = lean_ctor_get(v_toCold_329_, 9);
lean_inc(v_currMacroScope_341_);
v_cancelTk_x3f_342_ = lean_ctor_get(v_toCold_329_, 10);
lean_inc(v_cancelTk_x3f_342_);
v_inheritedTraceOptions_343_ = lean_ctor_get(v_toCold_329_, 11);
lean_inc_ref(v_inheritedTraceOptions_343_);
lean_dec_ref(v_toCold_329_);
v___y_254_ = v___y_308_;
v___y_255_ = v___y_311_;
v_fileName_256_ = v_fileName_334_;
v_fileMap_257_ = v_fileMap_335_;
v_currNamespace_258_ = v_currNamespace_336_;
v_openDecls_259_ = v_openDecls_337_;
v_initHeartbeats_260_ = v_initHeartbeats_338_;
v_maxHeartbeats_261_ = v_maxHeartbeats_339_;
v_quotContext_262_ = v_quotContext_340_;
v_currMacroScope_263_ = v_currMacroScope_341_;
v_cancelTk_x3f_264_ = v_cancelTk_x3f_342_;
v_inheritedTraceOptions_265_ = v_inheritedTraceOptions_343_;
v_currRecDepth_266_ = v_currRecDepth_330_;
v_ref_267_ = v_ref_331_;
v_suppressElabErrors_268_ = v_suppressElabErrors_332_;
v_isRecordingDeps_269_ = v_isRecordingDeps_333_;
v___y_270_ = v___y_310_;
goto v___jp_253_;
}
}
}
v___jp_347_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint16_t v___x_366_; lean_object* v___x_367_; lean_object* v_env_368_; uint8_t v___x_369_; uint16_t v___x_370_; uint16_t v___x_371_; uint16_t v___x_372_; uint8_t v___x_373_; 
v___x_362_ = l_Lean_maxRecDepth;
v___x_363_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17);
lean_inc_ref(v_inheritedTraceOptions_357_);
lean_inc(v_cancelTk_x3f_356_);
lean_inc(v_currMacroScope_355_);
lean_inc(v_quotContext_354_);
lean_inc(v_maxHeartbeats_353_);
lean_inc(v_initHeartbeats_352_);
lean_inc(v_openDecls_351_);
lean_inc(v_currNamespace_350_);
lean_inc_ref(v_fileMap_349_);
lean_inc_ref(v_fileName_348_);
v___x_364_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_364_, 0, v_fileName_348_);
lean_ctor_set(v___x_364_, 1, v_fileMap_349_);
lean_ctor_set(v___x_364_, 2, v___x_234_);
lean_ctor_set(v___x_364_, 3, v___x_363_);
lean_ctor_set(v___x_364_, 4, v_currNamespace_350_);
lean_ctor_set(v___x_364_, 5, v_openDecls_351_);
lean_ctor_set(v___x_364_, 6, v_initHeartbeats_352_);
lean_ctor_set(v___x_364_, 7, v_maxHeartbeats_353_);
lean_ctor_set(v___x_364_, 8, v_quotContext_354_);
lean_ctor_set(v___x_364_, 9, v_currMacroScope_355_);
lean_ctor_set(v___x_364_, 10, v_cancelTk_x3f_356_);
lean_ctor_set(v___x_364_, 11, v_inheritedTraceOptions_357_);
lean_inc(v_ref_359_);
lean_inc(v_currRecDepth_358_);
v___x_365_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v_currRecDepth_358_);
lean_ctor_set(v___x_365_, 2, v_ref_359_);
lean_ctor_set_uint16(v___x_365_, sizeof(void*)*3, v___x_241_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*3 + 2, v_suppressElabErrors_360_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*3 + 3, v_isRecordingDeps_361_);
v___x_366_ = l_Lean_OptionFlags_ofOptions(v_options_226_);
v___x_367_ = lean_st_ref_get(v___x_252_);
v_env_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc_ref(v_env_368_);
lean_dec(v___x_367_);
v___x_369_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_368_);
lean_dec_ref(v_env_368_);
v___x_370_ = 512;
v___x_371_ = lean_uint16_land(v___x_366_, v___x_370_);
v___x_372_ = 0;
v___x_373_ = lean_uint16_dec_eq(v___x_371_, v___x_372_);
if (v___x_373_ == 0)
{
if (v___x_369_ == 0)
{
lean_dec(v_currRecDepth_358_);
lean_dec_ref(v_inheritedTraceOptions_357_);
lean_dec(v_initHeartbeats_352_);
lean_dec(v_openDecls_351_);
lean_dec(v_currNamespace_350_);
lean_inc(v___x_252_);
v___y_307_ = v___x_248_;
v___y_308_ = v___x_362_;
v___y_309_ = v___x_365_;
v___y_310_ = v___x_252_;
v___y_311_ = v___x_366_;
goto v___jp_306_;
}
else
{
lean_dec_ref_known(v___x_365_, 3);
lean_inc(v___x_252_);
lean_inc(v_ref_359_);
lean_inc(v_cancelTk_x3f_356_);
lean_inc(v_currMacroScope_355_);
lean_inc(v_quotContext_354_);
lean_inc(v_maxHeartbeats_353_);
lean_inc_ref(v_fileMap_349_);
lean_inc_ref(v_fileName_348_);
v___y_254_ = v___x_362_;
v___y_255_ = v___x_366_;
v_fileName_256_ = v_fileName_348_;
v_fileMap_257_ = v_fileMap_349_;
v_currNamespace_258_ = v_currNamespace_350_;
v_openDecls_259_ = v_openDecls_351_;
v_initHeartbeats_260_ = v_initHeartbeats_352_;
v_maxHeartbeats_261_ = v_maxHeartbeats_353_;
v_quotContext_262_ = v_quotContext_354_;
v_currMacroScope_263_ = v_currMacroScope_355_;
v_cancelTk_x3f_264_ = v_cancelTk_x3f_356_;
v_inheritedTraceOptions_265_ = v_inheritedTraceOptions_357_;
v_currRecDepth_266_ = v_currRecDepth_358_;
v_ref_267_ = v_ref_359_;
v_suppressElabErrors_268_ = v_suppressElabErrors_360_;
v_isRecordingDeps_269_ = v_isRecordingDeps_361_;
v___y_270_ = v___x_252_;
goto v___jp_253_;
}
}
else
{
if (v___x_369_ == 0)
{
lean_dec_ref_known(v___x_365_, 3);
lean_inc(v___x_252_);
lean_inc(v_ref_359_);
lean_inc(v_cancelTk_x3f_356_);
lean_inc(v_currMacroScope_355_);
lean_inc(v_quotContext_354_);
lean_inc(v_maxHeartbeats_353_);
lean_inc_ref(v_fileMap_349_);
lean_inc_ref(v_fileName_348_);
v___y_254_ = v___x_362_;
v___y_255_ = v___x_366_;
v_fileName_256_ = v_fileName_348_;
v_fileMap_257_ = v_fileMap_349_;
v_currNamespace_258_ = v_currNamespace_350_;
v_openDecls_259_ = v_openDecls_351_;
v_initHeartbeats_260_ = v_initHeartbeats_352_;
v_maxHeartbeats_261_ = v_maxHeartbeats_353_;
v_quotContext_262_ = v_quotContext_354_;
v_currMacroScope_263_ = v_currMacroScope_355_;
v_cancelTk_x3f_264_ = v_cancelTk_x3f_356_;
v_inheritedTraceOptions_265_ = v_inheritedTraceOptions_357_;
v_currRecDepth_266_ = v_currRecDepth_358_;
v_ref_267_ = v_ref_359_;
v_suppressElabErrors_268_ = v_suppressElabErrors_360_;
v_isRecordingDeps_269_ = v_isRecordingDeps_361_;
v___y_270_ = v___x_252_;
goto v___jp_253_;
}
else
{
lean_dec(v_currRecDepth_358_);
lean_dec_ref(v_inheritedTraceOptions_357_);
lean_dec(v_initHeartbeats_352_);
lean_dec(v_openDecls_351_);
lean_dec(v_currNamespace_350_);
lean_inc(v___x_252_);
v___y_307_ = v___x_230_;
v___y_308_ = v___x_362_;
v___y_309_ = v___x_365_;
v___y_310_ = v___x_252_;
v___y_311_ = v___x_366_;
goto v___jp_306_;
}
}
}
v___jp_377_:
{
lean_object* v___x_379_; lean_object* v_env_380_; lean_object* v_nextMacroScope_381_; lean_object* v_ngen_382_; lean_object* v_auxDeclNGen_383_; lean_object* v_traceState_384_; lean_object* v_recordedDeps_385_; lean_object* v_messages_386_; lean_object* v_infoState_387_; lean_object* v_snapshotTasks_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_397_; 
v___x_379_ = lean_st_ref_take(v___x_252_);
v_env_380_ = lean_ctor_get(v___x_379_, 0);
v_nextMacroScope_381_ = lean_ctor_get(v___x_379_, 1);
v_ngen_382_ = lean_ctor_get(v___x_379_, 2);
v_auxDeclNGen_383_ = lean_ctor_get(v___x_379_, 3);
v_traceState_384_ = lean_ctor_get(v___x_379_, 4);
v_recordedDeps_385_ = lean_ctor_get(v___x_379_, 6);
v_messages_386_ = lean_ctor_get(v___x_379_, 7);
v_infoState_387_ = lean_ctor_get(v___x_379_, 8);
v_snapshotTasks_388_ = lean_ctor_get(v___x_379_, 9);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v___x_379_, 5);
lean_dec(v_unused_398_);
v___x_390_ = v___x_379_;
v_isShared_391_ = v_isSharedCheck_397_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_snapshotTasks_388_);
lean_inc(v_infoState_387_);
lean_inc(v_messages_386_);
lean_inc(v_recordedDeps_385_);
lean_inc(v_traceState_384_);
lean_inc(v_auxDeclNGen_383_);
lean_inc(v_ngen_382_);
lean_inc(v_nextMacroScope_381_);
lean_inc(v_env_380_);
lean_dec(v___x_379_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_397_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = l_Lean_Kernel_enableDiag(v_env_380_, v___y_378_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 5, v___x_245_);
lean_ctor_set(v___x_390_, 0, v___x_392_);
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_nextMacroScope_381_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_ngen_382_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v_auxDeclNGen_383_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v_traceState_384_);
lean_ctor_set(v_reuseFailAlloc_396_, 5, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_396_, 6, v_recordedDeps_385_);
lean_ctor_set(v_reuseFailAlloc_396_, 7, v_messages_386_);
lean_ctor_set(v_reuseFailAlloc_396_, 8, v_infoState_387_);
lean_ctor_set(v_reuseFailAlloc_396_, 9, v_snapshotTasks_388_);
v___x_394_ = v_reuseFailAlloc_396_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_395_; 
v___x_395_ = lean_st_ref_put(v___x_252_, v___x_394_);
v_fileName_348_ = v___x_232_;
v_fileMap_349_ = v___x_233_;
v_currNamespace_350_ = v_currNamespace_227_;
v_openDecls_351_ = v_openDecls_228_;
v_initHeartbeats_352_ = v___x_251_;
v_maxHeartbeats_353_ = v___x_236_;
v_quotContext_354_ = v___x_237_;
v_currMacroScope_355_ = v___x_238_;
v_cancelTk_x3f_356_ = v___x_239_;
v_inheritedTraceOptions_357_ = v___x_375_;
v_currRecDepth_358_ = v___x_235_;
v_ref_359_ = v___x_240_;
v_suppressElabErrors_360_ = v___x_230_;
v_isRecordingDeps_361_ = v___x_230_;
goto v___jp_347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___boxed(lean_object* v_info_402_, lean_object* v_x_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_402_, v_x_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM(lean_object* v_00_u03b1_406_, lean_object* v_info_407_, lean_object* v_x_408_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_407_, v_x_408_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___boxed(lean_object* v_00_u03b1_411_, lean_object* v_info_412_, lean_object* v_x_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Elab_ContextInfo_runCoreM(v_00_u03b1_411_, v_info_412_, v_x_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(lean_object* v___x_416_, lean_object* v_x_417_, lean_object* v___x_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_st_mk_ref(v___x_416_);
lean_inc(v___x_422_);
v___x_423_ = lean_apply_5(v_x_417_, v___x_418_, v___x_422_, v___y_419_, v___y_420_, lean_box(0));
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_433_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_433_ == 0)
{
v___x_426_ = v___x_423_;
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_428_ = lean_st_ref_get(v___x_422_);
lean_dec(v___x_422_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v_a_424_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_429_);
v___x_431_ = v___x_426_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec(v___x_422_);
v_a_434_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_423_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_423_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed(lean_object* v___x_442_, lean_object* v_x_443_, lean_object* v___x_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(v___x_442_, v_x_443_, v___x_444_, v___y_445_, v___y_446_);
return v_res_448_;
}
}
static uint64_t _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1(void){
_start:
{
lean_object* v___x_455_; uint64_t v___x_456_; 
v___x_455_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_456_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2(void){
_start:
{
uint64_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = lean_uint64_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1);
v___x_458_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_459_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set_uint64(v___x_459_, sizeof(void*)*1, v___x_457_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_465_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
lean_ctor_set(v___x_465_, 2, v___x_464_);
lean_ctor_set(v___x_465_, 3, v___x_464_);
lean_ctor_set(v___x_465_, 4, v___x_464_);
lean_ctor_set(v___x_465_, 5, v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = lean_unsigned_to_nat(32u);
v___x_467_ = lean_mk_empty_array_with_capacity(v___x_466_);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7(void){
_start:
{
size_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_469_ = ((size_t)5ULL);
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_unsigned_to_nat(32u);
v___x_472_ = lean_mk_empty_array_with_capacity(v___x_471_);
v___x_473_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6);
v___x_474_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v___x_472_);
lean_ctor_set(v___x_474_, 2, v___x_470_);
lean_ctor_set(v___x_474_, 3, v___x_470_);
lean_ctor_set_usize(v___x_474_, 4, v___x_469_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
lean_ctor_set(v___x_476_, 2, v___x_475_);
lean_ctor_set(v___x_476_, 3, v___x_475_);
lean_ctor_set(v___x_476_, 4, v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object* v_info_477_, lean_object* v_lctx_478_, lean_object* v_x_479_){
_start:
{
lean_object* v___x_481_; uint8_t v___x_482_; uint8_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v_toCommandContextInfo_489_; lean_object* v_mctx_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___f_495_; lean_object* v___x_496_; 
v___x_481_ = lean_box(1);
v___x_482_ = 0;
v___x_483_ = 1;
v___x_484_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2);
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3));
v___x_487_ = lean_box(0);
v___x_488_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_488_, 0, v___x_484_);
lean_ctor_set(v___x_488_, 1, v___x_481_);
lean_ctor_set(v___x_488_, 2, v_lctx_478_);
lean_ctor_set(v___x_488_, 3, v___x_486_);
lean_ctor_set(v___x_488_, 4, v___x_487_);
lean_ctor_set(v___x_488_, 5, v___x_485_);
lean_ctor_set(v___x_488_, 6, v___x_487_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*7, v___x_482_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*7 + 1, v___x_482_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*7 + 2, v___x_482_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*7 + 3, v___x_483_);
v_toCommandContextInfo_489_ = lean_ctor_get(v_info_477_, 0);
v_mctx_490_ = lean_ctor_get(v_toCommandContextInfo_489_, 3);
v___x_491_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_492_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7);
v___x_493_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8);
lean_inc_ref(v_mctx_490_);
v___x_494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_494_, 0, v_mctx_490_);
lean_ctor_set(v___x_494_, 1, v___x_491_);
lean_ctor_set(v___x_494_, 2, v___x_481_);
lean_ctor_set(v___x_494_, 3, v___x_492_);
lean_ctor_set(v___x_494_, 4, v___x_493_);
v___f_495_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_495_, 0, v___x_494_);
lean_closure_set(v___f_495_, 1, v_x_479_);
lean_closure_set(v___f_495_, 2, v___x_488_);
v___x_496_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_477_, v___f_495_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_505_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_505_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v_fst_501_; lean_object* v___x_503_; 
v_fst_501_ = lean_ctor_get(v_a_497_, 0);
lean_inc(v_fst_501_);
lean_dec(v_a_497_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v_fst_501_);
v___x_503_ = v___x_499_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_fst_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
v_a_506_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_496_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_496_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object* v_info_514_, lean_object* v_lctx_515_, lean_object* v_x_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_514_, v_lctx_515_, v_x_516_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object* v_00_u03b1_519_, lean_object* v_info_520_, lean_object* v_lctx_521_, lean_object* v_x_522_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_520_, v_lctx_521_, v_x_522_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object* v_00_u03b1_525_, lean_object* v_info_526_, lean_object* v_lctx_527_, lean_object* v_x_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_Elab_ContextInfo_runMetaM(v_00_u03b1_525_, v_info_526_, v_lctx_527_, v_x_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object* v_info_531_, lean_object* v_lctx_532_){
_start:
{
lean_object* v_toCommandContextInfo_533_; lean_object* v_env_534_; lean_object* v_mctx_535_; lean_object* v_options_536_; lean_object* v_currNamespace_537_; lean_object* v_openDecls_538_; lean_object* v___x_539_; 
v_toCommandContextInfo_533_ = lean_ctor_get(v_info_531_, 0);
v_env_534_ = lean_ctor_get(v_toCommandContextInfo_533_, 0);
v_mctx_535_ = lean_ctor_get(v_toCommandContextInfo_533_, 3);
v_options_536_ = lean_ctor_get(v_toCommandContextInfo_533_, 4);
v_currNamespace_537_ = lean_ctor_get(v_toCommandContextInfo_533_, 5);
v_openDecls_538_ = lean_ctor_get(v_toCommandContextInfo_533_, 6);
lean_inc(v_openDecls_538_);
lean_inc(v_currNamespace_537_);
lean_inc_ref(v_options_536_);
lean_inc_ref(v_mctx_535_);
lean_inc_ref(v_env_534_);
v___x_539_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_539_, 0, v_env_534_);
lean_ctor_set(v___x_539_, 1, v_mctx_535_);
lean_ctor_set(v___x_539_, 2, v_lctx_532_);
lean_ctor_set(v___x_539_, 3, v_options_536_);
lean_ctor_set(v___x_539_, 4, v_currNamespace_537_);
lean_ctor_set(v___x_539_, 5, v_openDecls_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object* v_info_540_, lean_object* v_lctx_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_540_, v_lctx_541_);
lean_dec_ref(v_info_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object* v_info_543_, lean_object* v_lctx_544_, lean_object* v_stx_545_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_543_, v_lctx_544_);
v___x_548_ = l_Lean_ppTerm(v___x_547_, v_stx_545_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object* v_info_550_, lean_object* v_lctx_551_, lean_object* v_stx_552_, lean_object* v_a_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Elab_ContextInfo_ppSyntax(v_info_550_, v_lctx_551_, v_stx_552_);
lean_dec_ref(v_info_550_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(lean_object* v_ctx_570_, lean_object* v_pos_571_, lean_object* v_info_572_){
_start:
{
lean_object* v_toCommandContextInfo_573_; lean_object* v_fileMap_574_; lean_object* v___x_575_; lean_object* v_line_576_; lean_object* v_column_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_600_; 
v_toCommandContextInfo_573_ = lean_ctor_get(v_ctx_570_, 0);
lean_inc_ref(v_toCommandContextInfo_573_);
lean_dec_ref(v_ctx_570_);
v_fileMap_574_ = lean_ctor_get(v_toCommandContextInfo_573_, 2);
lean_inc_ref(v_fileMap_574_);
lean_dec_ref(v_toCommandContextInfo_573_);
v___x_575_ = l_Lean_FileMap_toPosition(v_fileMap_574_, v_pos_571_);
v_line_576_ = lean_ctor_get(v___x_575_, 0);
v_column_577_ = lean_ctor_get(v___x_575_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_600_ == 0)
{
v___x_579_ = v___x_575_;
v_isShared_580_ = v_isSharedCheck_600_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_column_577_);
lean_inc(v_line_576_);
lean_dec(v___x_575_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_600_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_581_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_582_ = l_Nat_reprFast(v_line_576_);
v___x_583_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
if (v_isShared_580_ == 0)
{
lean_ctor_set_tag(v___x_579_, 5);
lean_ctor_set(v___x_579_, 1, v___x_583_);
lean_ctor_set(v___x_579_, 0, v___x_581_);
v___x_585_ = v___x_579_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v___x_583_);
v___x_585_ = v_reuseFailAlloc_599_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v_pos_592_; 
v___x_586_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
v___x_587_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = l_Nat_reprFast(v_column_577_);
v___x_589_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
v___x_590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_587_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v_pos_592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_pos_592_, 0, v___x_590_);
lean_ctor_set(v_pos_592_, 1, v___x_591_);
switch(lean_obj_tag(v_info_572_))
{
case 0:
{
return v_pos_592_;
}
case 1:
{
uint8_t v_canonical_596_; 
v_canonical_596_ = lean_ctor_get_uint8(v_info_572_, sizeof(void*)*2);
if (v_canonical_596_ == 1)
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9));
v___x_598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_598_, 0, v_pos_592_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
return v___x_598_;
}
else
{
goto v___jp_593_;
}
}
default: 
{
goto v___jp_593_;
}
}
v___jp_593_:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7));
v___x_595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_595_, 0, v_pos_592_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
return v___x_595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(lean_object* v_ctx_601_, lean_object* v_pos_602_, lean_object* v_info_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_601_, v_pos_602_, v_info_603_);
lean_dec(v_info_603_);
lean_dec(v_pos_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(lean_object* v_ctx_608_, lean_object* v_stx_609_){
_start:
{
lean_object* v___y_611_; lean_object* v___y_612_; uint8_t v___x_620_; lean_object* v___y_622_; lean_object* v___x_625_; 
v___x_620_ = 0;
v___x_625_ = l_Lean_Syntax_getPos_x3f(v_stx_609_, v___x_620_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v___x_626_; 
v___x_626_ = lean_unsigned_to_nat(0u);
v___y_622_ = v___x_626_;
goto v___jp_621_;
}
else
{
lean_object* v_val_627_; 
v_val_627_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_val_627_);
lean_dec_ref_known(v___x_625_, 1);
v___y_622_ = v_val_627_;
goto v___jp_621_;
}
v___jp_610_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_613_ = l_Lean_Syntax_getHeadInfo(v_stx_609_);
lean_inc_ref(v_ctx_608_);
v___x_614_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_608_, v___y_611_, v___x_613_);
lean_dec(v___x_613_);
lean_dec(v___y_611_);
v___x_615_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = l_Lean_Syntax_getTailInfo(v_stx_609_);
v___x_618_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_608_, v___y_612_, v___x_617_);
lean_dec(v___x_617_);
lean_dec(v___y_612_);
v___x_619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_616_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
return v___x_619_;
}
v___jp_621_:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_Syntax_getTailPos_x3f(v_stx_609_, v___x_620_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_inc(v___y_622_);
v___y_611_ = v___y_622_;
v___y_612_ = v___y_622_;
goto v___jp_610_;
}
else
{
lean_object* v_val_624_; 
v_val_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_val_624_);
lean_dec_ref_known(v___x_623_, 1);
v___y_611_ = v___y_622_;
v___y_612_ = v_val_624_;
goto v___jp_610_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(lean_object* v_ctx_628_, lean_object* v_stx_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_628_, v_stx_629_);
lean_dec(v_stx_629_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(lean_object* v_ctx_634_, lean_object* v_info_635_){
_start:
{
lean_object* v_elaborator_636_; lean_object* v_stx_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_652_; 
v_elaborator_636_ = lean_ctor_get(v_info_635_, 0);
v_stx_637_ = lean_ctor_get(v_info_635_, 1);
v_isSharedCheck_652_ = !lean_is_exclusive(v_info_635_);
if (v_isSharedCheck_652_ == 0)
{
v___x_639_ = v_info_635_;
v_isShared_640_ = v_isSharedCheck_652_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_stx_637_);
lean_inc(v_elaborator_636_);
lean_dec(v_info_635_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_652_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
uint8_t v___x_641_; 
v___x_641_ = l_Lean_Name_isAnonymous(v_elaborator_636_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_642_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_634_, v_stx_637_);
lean_dec(v_stx_637_);
v___x_643_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
if (v_isShared_640_ == 0)
{
lean_ctor_set_tag(v___x_639_, 5);
lean_ctor_set(v___x_639_, 1, v___x_643_);
lean_ctor_set(v___x_639_, 0, v___x_642_);
v___x_645_ = v___x_639_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___x_643_);
v___x_645_ = v_reuseFailAlloc_650_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
uint8_t v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_646_ = 1;
v___x_647_ = l_Lean_Name_toString(v_elaborator_636_, v___x_646_);
v___x_648_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
v___x_649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_645_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
return v___x_649_;
}
}
else
{
lean_object* v___x_651_; 
lean_del_object(v___x_639_);
lean_dec(v_elaborator_636_);
v___x_651_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_634_, v_stx_637_);
lean_dec(v_stx_637_);
return v___x_651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object* v_info_653_, lean_object* v_ctx_654_, lean_object* v_x_655_){
_start:
{
lean_object* v_lctx_657_; lean_object* v___x_658_; 
v_lctx_657_ = lean_ctor_get(v_info_653_, 1);
lean_inc_ref(v_lctx_657_);
lean_dec_ref(v_info_653_);
v___x_658_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_654_, v_lctx_657_, v_x_655_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(lean_object* v_info_659_, lean_object* v_ctx_660_, lean_object* v_x_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_659_, v_ctx_660_, v_x_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM(lean_object* v_00_u03b1_664_, lean_object* v_info_665_, lean_object* v_ctx_666_, lean_object* v_x_667_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_665_, v_ctx_666_, v_x_667_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___boxed(lean_object* v_00_u03b1_670_, lean_object* v_info_671_, lean_object* v_ctx_672_, lean_object* v_x_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_Elab_TermInfo_runMetaM(v_00_u03b1_670_, v_info_671_, v_ctx_672_, v_x_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0(lean_object* v_ctx_690_, lean_object* v_toElabInfo_691_, lean_object* v_expr_692_, uint8_t v_isBinder_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v_a_714_; lean_object* v___y_724_; uint8_t v___y_725_; lean_object* v___y_728_; lean_object* v_a_729_; lean_object* v___x_732_; 
lean_inc(v___y_697_);
lean_inc_ref(v___y_696_);
lean_inc(v___y_695_);
lean_inc_ref(v___y_694_);
lean_inc_ref(v_expr_692_);
v___x_732_ = lean_infer_type(v_expr_692_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___x_732_, 1);
v___x_734_ = l_Lean_Meta_ppExpr(v_a_733_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
v_a_714_ = v_a_735_;
goto v___jp_713_;
}
else
{
lean_object* v_a_736_; 
v_a_736_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_736_);
v___y_728_ = v___x_734_;
v_a_729_ = v_a_736_;
goto v___jp_727_;
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
v_a_737_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_732_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_732_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
lean_inc(v_a_737_);
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
v___y_728_ = v___x_742_;
v_a_729_ = v_a_737_;
goto v___jp_727_;
}
}
}
v___jp_699_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
lean_inc_ref(v___y_702_);
v___x_703_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_703_, 0, v___y_702_);
v___x_704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_704_, 0, v___y_700_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_704_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v___y_701_);
v___x_708_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_690_, v_toElabInfo_691_);
v___x_711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
return v___x_712_;
}
v___jp_713_:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Meta_ppExpr(v_expr_692_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
lean_dec_ref_known(v___x_715_, 1);
v___x_717_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__3));
v___x_718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v_a_716_);
v___x_719_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
v___x_720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
if (v_isBinder_693_ == 0)
{
lean_object* v___x_721_; 
v___x_721_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__6));
v___y_700_ = v___x_720_;
v___y_701_ = v_a_714_;
v___y_702_ = v___x_721_;
goto v___jp_699_;
}
else
{
lean_object* v___x_722_; 
v___x_722_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__7));
v___y_700_ = v___x_720_;
v___y_701_ = v_a_714_;
v___y_702_ = v___x_722_;
goto v___jp_699_;
}
}
else
{
lean_dec(v_a_714_);
lean_dec_ref(v_toElabInfo_691_);
lean_dec_ref(v_ctx_690_);
return v___x_715_;
}
}
v___jp_723_:
{
if (v___y_725_ == 0)
{
lean_object* v___x_726_; 
lean_dec_ref(v___y_724_);
v___x_726_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__9));
v_a_714_ = v___x_726_;
goto v___jp_713_;
}
else
{
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec_ref(v_expr_692_);
lean_dec_ref(v_toElabInfo_691_);
lean_dec_ref(v_ctx_690_);
return v___y_724_;
}
}
v___jp_727_:
{
uint8_t v___x_730_; 
v___x_730_ = l_Lean_Exception_isInterrupt(v_a_729_);
if (v___x_730_ == 0)
{
uint8_t v___x_731_; 
v___x_731_ = l_Lean_Exception_isRuntime(v_a_729_);
v___y_724_ = v___y_728_;
v___y_725_ = v___x_731_;
goto v___jp_723_;
}
else
{
lean_dec_ref(v_a_729_);
v___y_724_ = v___y_728_;
v___y_725_ = v___x_730_;
goto v___jp_723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0___boxed(lean_object* v_ctx_745_, lean_object* v_toElabInfo_746_, lean_object* v_expr_747_, lean_object* v_isBinder_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
uint8_t v_isBinder_boxed_754_; lean_object* v_res_755_; 
v_isBinder_boxed_754_ = lean_unbox(v_isBinder_748_);
v_res_755_ = l_Lean_Elab_TermInfo_format___lam__0(v_ctx_745_, v_toElabInfo_746_, v_expr_747_, v_isBinder_boxed_754_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format(lean_object* v_ctx_756_, lean_object* v_info_757_){
_start:
{
lean_object* v_toElabInfo_759_; lean_object* v_expr_760_; uint8_t v_isBinder_761_; lean_object* v___x_762_; lean_object* v___f_763_; lean_object* v___x_764_; 
v_toElabInfo_759_ = lean_ctor_get(v_info_757_, 0);
v_expr_760_ = lean_ctor_get(v_info_757_, 3);
v_isBinder_761_ = lean_ctor_get_uint8(v_info_757_, sizeof(void*)*4);
v___x_762_ = lean_box(v_isBinder_761_);
lean_inc_ref(v_expr_760_);
lean_inc_ref(v_toElabInfo_759_);
lean_inc_ref(v_ctx_756_);
v___f_763_ = lean_alloc_closure((void*)(l_Lean_Elab_TermInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_763_, 0, v_ctx_756_);
lean_closure_set(v___f_763_, 1, v_toElabInfo_759_);
lean_closure_set(v___f_763_, 2, v_expr_760_);
lean_closure_set(v___f_763_, 3, v___x_762_);
v___x_764_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_757_, v_ctx_756_, v___f_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___boxed(lean_object* v_ctx_765_, lean_object* v_info_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Elab_TermInfo_format(v_ctx_765_, v_info_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialTermInfo_format(lean_object* v_ctx_772_, lean_object* v_info_773_){
_start:
{
lean_object* v_toElabInfo_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v_toElabInfo_774_ = lean_ctor_get(v_info_773_, 0);
lean_inc_ref(v_toElabInfo_774_);
lean_dec_ref(v_info_773_);
v___x_775_ = ((lean_object*)(l_Lean_Elab_PartialTermInfo_format___closed__1));
v___x_776_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_772_, v_toElabInfo_774_);
v___x_777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_775_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(lean_object* v_x_784_){
_start:
{
if (lean_obj_tag(v_x_784_) == 0)
{
lean_object* v___x_785_; 
v___x_785_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_785_;
}
else
{
lean_object* v_val_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_796_; 
v_val_786_ = lean_ctor_get(v_x_784_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_x_784_);
if (v_isSharedCheck_796_ == 0)
{
v___x_788_ = v_x_784_;
v_isShared_789_ = v_isSharedCheck_796_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_val_786_);
lean_dec(v_x_784_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_796_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_790_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_791_ = lean_expr_dbg_to_string(v_val_786_);
lean_dec(v_val_786_);
if (v_isShared_789_ == 0)
{
lean_ctor_set_tag(v___x_788_, 3);
lean_ctor_set(v___x_788_, 0, v___x_791_);
v___x_793_ = v___x_788_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_795_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_794_; 
v___x_794_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_790_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
return v___x_794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0(lean_object* v_ctx_803_, lean_object* v_lctx_804_, lean_object* v_stx_805_, lean_object* v_expectedType_x3f_806_, lean_object* v_info_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_832_; 
v___x_813_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_803_, v_lctx_804_, v_stx_805_);
v_a_814_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_832_ == 0)
{
v___x_816_ = v___x_813_;
v_isShared_817_ = v_isSharedCheck_832_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_832_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_818_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__1));
v___x_819_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
lean_ctor_set(v___x_819_, 1, v_a_814_);
v___x_820_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_821_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_806_);
v___x_823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = l_Lean_Elab_CompletionInfo_stx(v_info_807_);
v___x_827_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_803_, v___x_826_);
lean_dec(v___x_826_);
v___x_828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_825_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_828_);
v___x_830_ = v___x_816_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___boxed(lean_object* v_ctx_833_, lean_object* v_lctx_834_, lean_object* v_stx_835_, lean_object* v_expectedType_x3f_836_, lean_object* v_info_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_Elab_CompletionInfo_format___lam__0(v_ctx_833_, v_lctx_834_, v_stx_835_, v_expectedType_x3f_836_, v_info_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec_ref(v_info_837_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format(lean_object* v_ctx_850_, lean_object* v_info_851_){
_start:
{
switch(lean_obj_tag(v_info_851_))
{
case 0:
{
lean_object* v_termInfo_853_; lean_object* v_expectedType_x3f_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_875_; 
v_termInfo_853_ = lean_ctor_get(v_info_851_, 0);
v_expectedType_x3f_854_ = lean_ctor_get(v_info_851_, 1);
v_isSharedCheck_875_ = !lean_is_exclusive(v_info_851_);
if (v_isSharedCheck_875_ == 0)
{
v___x_856_ = v_info_851_;
v_isShared_857_ = v_isSharedCheck_875_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_expectedType_x3f_854_);
lean_inc(v_termInfo_853_);
lean_dec(v_info_851_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_875_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Elab_TermInfo_format(v_ctx_850_, v_termInfo_853_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_874_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_874_ == 0)
{
v___x_861_ = v___x_858_;
v_isShared_862_ = v_isSharedCheck_874_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_874_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_863_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__1));
if (v_isShared_857_ == 0)
{
lean_ctor_set_tag(v___x_856_, 5);
lean_ctor_set(v___x_856_, 1, v_a_859_);
lean_ctor_set(v___x_856_, 0, v___x_863_);
v___x_865_ = v___x_856_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_a_859_);
v___x_865_ = v_reuseFailAlloc_873_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_866_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_867_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_854_);
v___x_869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_869_);
v___x_871_ = v___x_861_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
lean_del_object(v___x_856_);
lean_dec(v_expectedType_x3f_854_);
return v___x_858_;
}
}
}
case 1:
{
lean_object* v_stx_876_; lean_object* v_lctx_877_; lean_object* v_expectedType_x3f_878_; lean_object* v___f_879_; lean_object* v___x_880_; 
v_stx_876_ = lean_ctor_get(v_info_851_, 0);
lean_inc(v_stx_876_);
v_lctx_877_ = lean_ctor_get(v_info_851_, 2);
lean_inc_ref_n(v_lctx_877_, 2);
v_expectedType_x3f_878_ = lean_ctor_get(v_info_851_, 3);
lean_inc(v_expectedType_x3f_878_);
lean_inc_ref(v_ctx_850_);
v___f_879_ = lean_alloc_closure((void*)(l_Lean_Elab_CompletionInfo_format___lam__0___boxed), 10, 5);
lean_closure_set(v___f_879_, 0, v_ctx_850_);
lean_closure_set(v___f_879_, 1, v_lctx_877_);
lean_closure_set(v___f_879_, 2, v_stx_876_);
lean_closure_set(v___f_879_, 3, v_expectedType_x3f_878_);
lean_closure_set(v___f_879_, 4, v_info_851_);
v___x_880_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_850_, v_lctx_877_, v___f_879_);
return v___x_880_;
}
default: 
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_881_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__3));
v___x_882_ = l_Lean_Elab_CompletionInfo_stx(v_info_851_);
lean_dec_ref(v_info_851_);
v___x_883_ = lean_box(0);
v___x_884_ = 0;
lean_inc(v___x_882_);
v___x_885_ = l_Lean_Syntax_formatStx(v___x_882_, v___x_883_, v___x_884_);
v___x_886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_881_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_850_, v___x_882_);
lean_dec(v___x_882_);
v___x_890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___boxed(lean_object* v_ctx_892_, lean_object* v_info_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_Elab_CompletionInfo_format(v_ctx_892_, v_info_893_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format(lean_object* v_ctx_899_, lean_object* v_info_900_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_902_ = ((lean_object*)(l_Lean_Elab_CommandInfo_format___closed__1));
v___x_903_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_899_, v_info_900_);
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format___boxed(lean_object* v_ctx_906_, lean_object* v_info_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_Elab_CommandInfo_format(v_ctx_906_, v_info_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format(lean_object* v_ctx_913_, lean_object* v_info_914_){
_start:
{
lean_object* v_stx_916_; lean_object* v_optionName_917_; lean_object* v___x_918_; uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_stx_916_ = lean_ctor_get(v_info_914_, 0);
lean_inc(v_stx_916_);
v_optionName_917_ = lean_ctor_get(v_info_914_, 1);
lean_inc(v_optionName_917_);
lean_dec_ref(v_info_914_);
v___x_918_ = ((lean_object*)(l_Lean_Elab_OptionInfo_format___closed__1));
v___x_919_ = 1;
v___x_920_ = l_Lean_Name_toString(v_optionName_917_, v___x_919_);
v___x_921_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
v___x_922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_918_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_913_, v_stx_916_);
lean_dec(v_stx_916_);
v___x_926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format___boxed(lean_object* v_ctx_928_, lean_object* v_info_929_, lean_object* v_a_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_Elab_OptionInfo_format(v_ctx_928_, v_info_929_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format(lean_object* v_ctx_935_, lean_object* v_info_936_){
_start:
{
lean_object* v_stx_938_; lean_object* v_errorName_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_955_; 
v_stx_938_ = lean_ctor_get(v_info_936_, 0);
v_errorName_939_ = lean_ctor_get(v_info_936_, 1);
v_isSharedCheck_955_ = !lean_is_exclusive(v_info_936_);
if (v_isSharedCheck_955_ == 0)
{
v___x_941_ = v_info_936_;
v_isShared_942_ = v_isSharedCheck_955_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_errorName_939_);
lean_inc(v_stx_938_);
lean_dec(v_info_936_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_955_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; uint8_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_943_ = ((lean_object*)(l_Lean_Elab_ErrorNameInfo_format___closed__1));
v___x_944_ = 1;
v___x_945_ = l_Lean_Name_toString(v_errorName_939_, v___x_944_);
v___x_946_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
if (v_isShared_942_ == 0)
{
lean_ctor_set_tag(v___x_941_, 5);
lean_ctor_set(v___x_941_, 1, v___x_946_);
lean_ctor_set(v___x_941_, 0, v___x_943_);
v___x_948_ = v___x_941_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v___x_946_);
v___x_948_ = v_reuseFailAlloc_954_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_949_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_948_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_935_, v_stx_938_);
lean_dec(v_stx_938_);
v___x_952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format___boxed(lean_object* v_ctx_956_, lean_object* v_info_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_956_, v_info_957_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0(lean_object* v_val_966_, lean_object* v_fieldName_967_, lean_object* v_ctx_968_, lean_object* v_stx_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; 
lean_inc(v___y_973_);
lean_inc_ref(v___y_972_);
lean_inc(v___y_971_);
lean_inc_ref(v___y_970_);
lean_inc_ref(v_val_966_);
v___x_975_ = lean_infer_type(v_val_966_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v___x_977_ = l_Lean_Meta_ppExpr(v_a_976_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1008_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_1008_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1008_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_Meta_ppExpr(v_val_966_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1007_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_1007_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1007_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; uint8_t v___x_988_; lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_987_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__1));
v___x_988_ = 1;
v___x_989_ = l_Lean_Name_toString(v_fieldName_967_, v___x_988_);
if (v_isShared_981_ == 0)
{
lean_ctor_set_tag(v___x_980_, 3);
lean_ctor_set(v___x_980_, 0, v___x_989_);
v___x_991_ = v___x_980_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_989_);
v___x_991_ = v_reuseFailAlloc_1006_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_987_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v_a_978_);
v___x_996_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__3));
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v_a_983_);
v___x_999_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_968_, v_stx_969_);
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v___x_1002_);
v___x_1004_ = v___x_985_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
else
{
lean_del_object(v___x_980_);
lean_dec(v_a_978_);
lean_dec_ref(v_ctx_968_);
lean_dec(v_fieldName_967_);
return v___x_982_;
}
}
}
else
{
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec_ref(v_ctx_968_);
lean_dec(v_fieldName_967_);
lean_dec_ref(v_val_966_);
return v___x_977_;
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec_ref(v_ctx_968_);
lean_dec(v_fieldName_967_);
lean_dec_ref(v_val_966_);
v_a_1009_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_975_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_975_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0___boxed(lean_object* v_val_1017_, lean_object* v_fieldName_1018_, lean_object* v_ctx_1019_, lean_object* v_stx_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_Elab_FieldInfo_format___lam__0(v_val_1017_, v_fieldName_1018_, v_ctx_1019_, v_stx_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
lean_dec(v_stx_1020_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format(lean_object* v_ctx_1027_, lean_object* v_info_1028_){
_start:
{
lean_object* v_fieldName_1030_; lean_object* v_lctx_1031_; lean_object* v_val_1032_; lean_object* v_stx_1033_; lean_object* v___f_1034_; lean_object* v___x_1035_; 
v_fieldName_1030_ = lean_ctor_get(v_info_1028_, 1);
lean_inc(v_fieldName_1030_);
v_lctx_1031_ = lean_ctor_get(v_info_1028_, 2);
lean_inc_ref(v_lctx_1031_);
v_val_1032_ = lean_ctor_get(v_info_1028_, 3);
lean_inc_ref(v_val_1032_);
v_stx_1033_ = lean_ctor_get(v_info_1028_, 4);
lean_inc(v_stx_1033_);
lean_dec_ref(v_info_1028_);
lean_inc_ref(v_ctx_1027_);
v___f_1034_ = lean_alloc_closure((void*)(l_Lean_Elab_FieldInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1034_, 0, v_val_1032_);
lean_closure_set(v___f_1034_, 1, v_fieldName_1030_);
lean_closure_set(v___f_1034_, 2, v_ctx_1027_);
lean_closure_set(v___f_1034_, 3, v_stx_1033_);
v___x_1035_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1027_, v_lctx_1031_, v___f_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___boxed(lean_object* v_ctx_1036_, lean_object* v_info_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_Elab_FieldInfo_format(v_ctx_1036_, v_info_1037_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(lean_object* v_pre_1040_, lean_object* v_x_1041_, lean_object* v_x_1042_){
_start:
{
if (lean_obj_tag(v_x_1042_) == 0)
{
lean_dec(v_pre_1040_);
return v_x_1041_;
}
else
{
lean_object* v_head_1043_; lean_object* v_tail_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1053_; 
v_head_1043_ = lean_ctor_get(v_x_1042_, 0);
v_tail_1044_ = lean_ctor_get(v_x_1042_, 1);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_x_1042_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1046_ = v_x_1042_;
v_isShared_1047_ = v_isSharedCheck_1053_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_tail_1044_);
lean_inc(v_head_1043_);
lean_dec(v_x_1042_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1053_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
lean_inc(v_pre_1040_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 5);
lean_ctor_set(v___x_1046_, 1, v_pre_1040_);
lean_ctor_set(v___x_1046_, 0, v_x_1041_);
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_x_1041_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_pre_1040_);
v___x_1049_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v_head_1043_);
v_x_1041_ = v___x_1050_;
v_x_1042_ = v_tail_1044_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(lean_object* v_pre_1054_, lean_object* v_x_1055_){
_start:
{
if (lean_obj_tag(v_x_1055_) == 0)
{
lean_object* v___x_1056_; 
lean_dec(v_pre_1054_);
v___x_1056_ = lean_box(0);
return v___x_1056_;
}
else
{
lean_object* v_head_1057_; lean_object* v_tail_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1066_; 
v_head_1057_ = lean_ctor_get(v_x_1055_, 0);
v_tail_1058_ = lean_ctor_get(v_x_1055_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_x_1055_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1060_ = v_x_1055_;
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_tail_1058_);
lean_inc(v_head_1057_);
lean_dec(v_x_1055_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
lean_inc(v_pre_1054_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set_tag(v___x_1060_, 5);
lean_ctor_set(v___x_1060_, 1, v_head_1057_);
lean_ctor_set(v___x_1060_, 0, v_pre_1054_);
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_pre_1054_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_head_1057_);
v___x_1063_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(v_pre_1054_, v___x_1063_, v_tail_1058_);
return v___x_1064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(lean_object* v_x_1067_, lean_object* v_x_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
if (lean_obj_tag(v_x_1067_) == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = l_List_reverse___redArg(v_x_1068_);
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
else
{
lean_object* v_head_1076_; lean_object* v_tail_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1095_; 
v_head_1076_ = lean_ctor_get(v_x_1067_, 0);
v_tail_1077_ = lean_ctor_get(v_x_1067_, 1);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_x_1067_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1079_ = v_x_1067_;
v_isShared_1080_ = v_isSharedCheck_1095_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_tail_1077_);
lean_inc(v_head_1076_);
lean_dec(v_x_1067_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1095_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_Meta_ppGoal(v_head_1076_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v_head_1076_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1084_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 1, v_x_1068_);
lean_ctor_set(v___x_1079_, 0, v_a_1082_);
v___x_1084_ = v___x_1079_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1082_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_x_1068_);
v___x_1084_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
v_x_1067_ = v_tail_1077_;
v_x_1068_ = v___x_1084_;
goto _start;
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_del_object(v___x_1079_);
lean_dec(v_tail_1077_);
lean_dec(v_x_1068_);
v_a_1087_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1081_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1081_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_x_1096_, v_x_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0(lean_object* v_goals_1107_, lean_object* v___x_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_goals_1107_, v___x_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1124_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1124_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1124_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1119_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1120_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1119_, v_a_1115_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1120_);
v___x_1122_ = v___x_1117_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
v_a_1125_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1114_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1114_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(lean_object* v_goals_1133_, lean_object* v___x_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0(v_goals_1133_, v___x_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
return v_res_1140_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = lean_unsigned_to_nat(32u);
v___x_1144_ = lean_mk_empty_array_with_capacity(v___x_1143_);
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2(void){
_start:
{
size_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1146_ = ((size_t)5ULL);
v___x_1147_ = lean_unsigned_to_nat(0u);
v___x_1148_ = lean_unsigned_to_nat(32u);
v___x_1149_ = lean_mk_empty_array_with_capacity(v___x_1148_);
v___x_1150_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__1, &l_Lean_Elab_ContextInfo_ppGoals___closed__1_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1);
v___x_1151_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
lean_ctor_set(v___x_1151_, 1, v___x_1149_);
lean_ctor_set(v___x_1151_, 2, v___x_1147_);
lean_ctor_set(v___x_1151_, 3, v___x_1147_);
lean_ctor_set_usize(v___x_1151_, 4, v___x_1146_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1152_ = lean_box(1);
v___x_1153_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_1154_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__0, &l_Lean_Elab_ContextInfo_ppGoals___closed__0_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0);
v___x_1155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
lean_ctor_set(v___x_1155_, 1, v___x_1153_);
lean_ctor_set(v___x_1155_, 2, v___x_1152_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object* v_ctx_1159_, lean_object* v_goals_1160_){
_start:
{
uint8_t v___x_1162_; 
v___x_1162_ = l_List_isEmpty___redArg(v_goals_1160_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___f_1165_; lean_object* v___x_1166_; 
v___x_1163_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_1164_ = lean_box(0);
v___f_1165_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1165_, 0, v_goals_1160_);
lean_closure_set(v___f_1165_, 1, v___x_1164_);
v___x_1166_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1159_, v___x_1163_, v___f_1165_);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec(v_goals_1160_);
lean_dec_ref(v_ctx_1159_);
v___x_1167_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___closed__5));
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object* v_ctx_1169_, lean_object* v_goals_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctx_1169_, v_goals_1170_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format(lean_object* v_ctx_1182_, lean_object* v_info_1183_){
_start:
{
lean_object* v_toCommandContextInfo_1185_; lean_object* v_parentDecl_x3f_1186_; lean_object* v_autoImplicits_1187_; lean_object* v_env_1188_; lean_object* v_cmdEnv_x3f_1189_; lean_object* v_fileMap_1190_; lean_object* v_options_1191_; lean_object* v_currNamespace_1192_; lean_object* v_openDecls_1193_; lean_object* v_ngen_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1236_; 
v_toCommandContextInfo_1185_ = lean_ctor_get(v_ctx_1182_, 0);
lean_inc_ref(v_toCommandContextInfo_1185_);
v_parentDecl_x3f_1186_ = lean_ctor_get(v_ctx_1182_, 1);
v_autoImplicits_1187_ = lean_ctor_get(v_ctx_1182_, 2);
v_env_1188_ = lean_ctor_get(v_toCommandContextInfo_1185_, 0);
v_cmdEnv_x3f_1189_ = lean_ctor_get(v_toCommandContextInfo_1185_, 1);
v_fileMap_1190_ = lean_ctor_get(v_toCommandContextInfo_1185_, 2);
v_options_1191_ = lean_ctor_get(v_toCommandContextInfo_1185_, 4);
v_currNamespace_1192_ = lean_ctor_get(v_toCommandContextInfo_1185_, 5);
v_openDecls_1193_ = lean_ctor_get(v_toCommandContextInfo_1185_, 6);
v_ngen_1194_ = lean_ctor_get(v_toCommandContextInfo_1185_, 7);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_toCommandContextInfo_1185_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; 
v_unused_1237_ = lean_ctor_get(v_toCommandContextInfo_1185_, 3);
lean_dec(v_unused_1237_);
v___x_1196_ = v_toCommandContextInfo_1185_;
v_isShared_1197_ = v_isSharedCheck_1236_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_ngen_1194_);
lean_inc(v_openDecls_1193_);
lean_inc(v_currNamespace_1192_);
lean_inc(v_options_1191_);
lean_inc(v_fileMap_1190_);
lean_inc(v_cmdEnv_x3f_1189_);
lean_inc(v_env_1188_);
lean_dec(v_toCommandContextInfo_1185_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1236_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v_toElabInfo_1198_; lean_object* v_mctxBefore_1199_; lean_object* v_goalsBefore_1200_; lean_object* v_mctxAfter_1201_; lean_object* v_goalsAfter_1202_; lean_object* v___x_1204_; 
v_toElabInfo_1198_ = lean_ctor_get(v_info_1183_, 0);
lean_inc_ref(v_toElabInfo_1198_);
v_mctxBefore_1199_ = lean_ctor_get(v_info_1183_, 1);
lean_inc_ref(v_mctxBefore_1199_);
v_goalsBefore_1200_ = lean_ctor_get(v_info_1183_, 2);
lean_inc(v_goalsBefore_1200_);
v_mctxAfter_1201_ = lean_ctor_get(v_info_1183_, 3);
lean_inc_ref(v_mctxAfter_1201_);
v_goalsAfter_1202_ = lean_ctor_get(v_info_1183_, 4);
lean_inc(v_goalsAfter_1202_);
lean_dec_ref(v_info_1183_);
lean_inc_ref(v_ngen_1194_);
lean_inc(v_openDecls_1193_);
lean_inc(v_currNamespace_1192_);
lean_inc_ref(v_options_1191_);
lean_inc_ref(v_fileMap_1190_);
lean_inc(v_cmdEnv_x3f_1189_);
lean_inc_ref(v_env_1188_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 3, v_mctxBefore_1199_);
v___x_1204_ = v___x_1196_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_env_1188_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_cmdEnv_x3f_1189_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v_fileMap_1190_);
lean_ctor_set(v_reuseFailAlloc_1235_, 3, v_mctxBefore_1199_);
lean_ctor_set(v_reuseFailAlloc_1235_, 4, v_options_1191_);
lean_ctor_set(v_reuseFailAlloc_1235_, 5, v_currNamespace_1192_);
lean_ctor_set(v_reuseFailAlloc_1235_, 6, v_openDecls_1193_);
lean_ctor_set(v_reuseFailAlloc_1235_, 7, v_ngen_1194_);
v___x_1204_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v_ctxB_1205_; lean_object* v___x_1206_; lean_object* v_ctxA_1207_; lean_object* v___x_1208_; 
lean_inc_ref_n(v_autoImplicits_1187_, 2);
lean_inc_n(v_parentDecl_x3f_1186_, 2);
v_ctxB_1205_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxB_1205_, 0, v___x_1204_);
lean_ctor_set(v_ctxB_1205_, 1, v_parentDecl_x3f_1186_);
lean_ctor_set(v_ctxB_1205_, 2, v_autoImplicits_1187_);
v___x_1206_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1206_, 0, v_env_1188_);
lean_ctor_set(v___x_1206_, 1, v_cmdEnv_x3f_1189_);
lean_ctor_set(v___x_1206_, 2, v_fileMap_1190_);
lean_ctor_set(v___x_1206_, 3, v_mctxAfter_1201_);
lean_ctor_set(v___x_1206_, 4, v_options_1191_);
lean_ctor_set(v___x_1206_, 5, v_currNamespace_1192_);
lean_ctor_set(v___x_1206_, 6, v_openDecls_1193_);
lean_ctor_set(v___x_1206_, 7, v_ngen_1194_);
v_ctxA_1207_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxA_1207_, 0, v___x_1206_);
lean_ctor_set(v_ctxA_1207_, 1, v_parentDecl_x3f_1186_);
lean_ctor_set(v_ctxA_1207_, 2, v_autoImplicits_1187_);
v___x_1208_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxB_1205_, v_goalsBefore_1200_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1210_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1209_);
lean_dec_ref_known(v___x_1208_, 1);
v___x_1210_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxA_1207_, v_goalsAfter_1202_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1234_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1213_ = v___x_1210_;
v_isShared_1214_ = v_isSharedCheck_1234_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1234_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v_stx_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; 
v_stx_1215_ = lean_ctor_get(v_toElabInfo_1198_, 1);
lean_inc(v_stx_1215_);
v___x_1216_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__1));
v___x_1217_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1182_, v_toElabInfo_1198_);
v___x_1218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1216_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1218_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v___x_1221_ = lean_box(0);
v___x_1222_ = 0;
v___x_1223_ = l_Lean_Syntax_formatStx(v_stx_1215_, v___x_1221_, v___x_1222_);
v___x_1224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1220_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__3));
v___x_1226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v_a_1209_);
v___x_1228_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__5));
v___x_1229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1227_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v___x_1230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v_a_1211_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1230_);
v___x_1232_ = v___x_1213_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
else
{
lean_dec(v_a_1209_);
lean_dec_ref(v_toElabInfo_1198_);
lean_dec_ref(v_ctx_1182_);
return v___x_1210_;
}
}
else
{
lean_dec_ref_known(v_ctxA_1207_, 3);
lean_dec(v_goalsAfter_1202_);
lean_dec_ref(v_toElabInfo_1198_);
lean_dec_ref(v_ctx_1182_);
return v___x_1208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format___boxed(lean_object* v_ctx_1238_, lean_object* v_info_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Elab_TacticInfo_format(v_ctx_1238_, v_info_1239_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object* v_ctx_1248_, lean_object* v_info_1249_){
_start:
{
lean_object* v_lctx_1251_; lean_object* v_stx_1252_; lean_object* v_output_1253_; lean_object* v___x_1254_; lean_object* v_a_1255_; lean_object* v___x_1256_; lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1269_; 
v_lctx_1251_ = lean_ctor_get(v_info_1249_, 0);
lean_inc_ref_n(v_lctx_1251_, 2);
v_stx_1252_ = lean_ctor_get(v_info_1249_, 1);
lean_inc(v_stx_1252_);
v_output_1253_ = lean_ctor_get(v_info_1249_, 2);
lean_inc(v_output_1253_);
lean_dec_ref(v_info_1249_);
v___x_1254_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1248_, v_lctx_1251_, v_stx_1252_);
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref(v___x_1254_);
v___x_1256_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1248_, v_lctx_1251_, v_output_1253_);
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1269_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1269_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1261_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__1));
v___x_1262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v_a_1255_);
v___x_1263_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__3));
v___x_1264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
lean_ctor_set(v___x_1265_, 1, v_a_1257_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1265_);
v___x_1267_ = v___x_1259_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object* v_ctx_1270_, lean_object* v_info_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1270_, v_info_1271_);
lean_dec_ref(v_ctx_1270_);
return v_res_1273_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__0(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
return v___x_1275_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__1(void){
_start:
{
uint8_t v___x_1276_; size_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1276_ = 1;
v___x_1277_ = ((size_t)0ULL);
v___x_1278_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__0, &l_Lean_Elab_UserWidgetInfo_format___closed__0_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__0);
v___x_1279_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
lean_ctor_set_usize(v___x_1279_, 2, v___x_1277_);
lean_ctor_set_uint8(v___x_1279_, sizeof(void*)*3, v___x_1276_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_UserWidgetInfo_format(lean_object* v_info_1283_){
_start:
{
lean_object* v_toWidgetInstance_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1313_; 
v_toWidgetInstance_1284_ = lean_ctor_get(v_info_1283_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_info_1283_);
if (v_isSharedCheck_1313_ == 0)
{
lean_object* v_unused_1314_; 
v_unused_1314_ = lean_ctor_get(v_info_1283_, 1);
lean_dec(v_unused_1314_);
v___x_1286_ = v_info_1283_;
v_isShared_1287_ = v_isSharedCheck_1313_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_toWidgetInstance_1284_);
lean_dec(v_info_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1313_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v_id_1288_; lean_object* v_props_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v_fst_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1311_; 
v_id_1288_ = lean_ctor_get(v_toWidgetInstance_1284_, 0);
lean_inc(v_id_1288_);
v_props_1289_ = lean_ctor_get(v_toWidgetInstance_1284_, 1);
lean_inc_ref(v_props_1289_);
lean_dec_ref(v_toWidgetInstance_1284_);
v___x_1290_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__1, &l_Lean_Elab_UserWidgetInfo_format___closed__1_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__1);
v___x_1291_ = lean_apply_1(v_props_1289_, v___x_1290_);
v_fst_1292_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; 
v_unused_1312_ = lean_ctor_get(v___x_1291_, 1);
lean_dec(v_unused_1312_);
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1311_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_fst_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1311_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; uint8_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1296_ = ((lean_object*)(l_Lean_Elab_UserWidgetInfo_format___closed__3));
v___x_1297_ = 1;
v___x_1298_ = l_Lean_Name_toString(v_id_1288_, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set_tag(v___x_1294_, 5);
lean_ctor_set(v___x_1294_, 1, v___x_1299_);
lean_ctor_set(v___x_1294_, 0, v___x_1296_);
v___x_1301_ = v___x_1294_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1302_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
if (v_isShared_1287_ == 0)
{
lean_ctor_set_tag(v___x_1286_, 5);
lean_ctor_set(v___x_1286_, 1, v___x_1302_);
lean_ctor_set(v___x_1286_, 0, v___x_1301_);
v___x_1304_ = v___x_1286_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1305_ = lean_unsigned_to_nat(80u);
v___x_1306_ = l_Lean_Json_pretty(v_fst_1292_, v___x_1305_);
v___x_1307_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
v___x_1308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1304_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
return v___x_1308_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FVarAliasInfo_format(lean_object* v_info_1321_){
_start:
{
lean_object* v_userName_1322_; lean_object* v_id_1323_; lean_object* v_baseId_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_userName_1322_ = lean_ctor_get(v_info_1321_, 0);
lean_inc(v_userName_1322_);
v_id_1323_ = lean_ctor_get(v_info_1321_, 1);
lean_inc(v_id_1323_);
v_baseId_1324_ = lean_ctor_get(v_info_1321_, 2);
lean_inc(v_baseId_1324_);
lean_dec_ref(v_info_1321_);
v___x_1325_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__1));
v___x_1326_ = l_Lean_Name_eraseMacroScopes(v_userName_1322_);
lean_dec(v_userName_1322_);
v___x_1327_ = 1;
v___x_1328_ = l_Lean_Name_toString(v___x_1326_, v___x_1327_);
v___x_1329_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
v___x_1330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1325_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_1332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = l_Lean_Name_toString(v_id_1323_, v___x_1327_);
v___x_1334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
v___x_1335_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1332_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
v___x_1336_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__3));
v___x_1337_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1335_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = l_Lean_Name_toString(v_baseId_1324_, v___x_1327_);
v___x_1339_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
v___x_1340_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1337_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format(lean_object* v_ctx_1344_, lean_object* v_info_1345_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1346_ = ((lean_object*)(l_Lean_Elab_FieldRedeclInfo_format___closed__1));
v___x_1347_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1344_, v_info_1345_);
v___x_1348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format___boxed(lean_object* v_ctx_1349_, lean_object* v_info_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1349_, v_info_1350_);
lean_dec(v_info_1350_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f(lean_object* v_ppCtx_1354_, lean_object* v_info_1355_){
_start:
{
lean_object* v_mkDocString_x3f_1357_; 
v_mkDocString_x3f_1357_ = lean_ctor_get(v_info_1355_, 2);
lean_inc(v_mkDocString_x3f_1357_);
lean_dec_ref(v_info_1355_);
if (lean_obj_tag(v_mkDocString_x3f_1357_) == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_dec_ref(v_ppCtx_1354_);
v___x_1358_ = lean_box(0);
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
return v___x_1359_;
}
else
{
lean_object* v_val_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1392_; 
v_val_1360_ = lean_ctor_get(v_mkDocString_x3f_1357_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_mkDocString_x3f_1357_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1362_ = v_mkDocString_x3f_1357_;
v_isShared_1363_ = v_isSharedCheck_1392_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_val_1360_);
lean_dec(v_mkDocString_x3f_1357_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1392_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_apply_2(v_val_1360_, v_ppCtx_1354_, lean_box(0));
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1375_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1367_ = v___x_1364_;
v_isShared_1368_ = v_isSharedCheck_1375_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1375_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v_a_1365_);
v___x_1370_ = v___x_1362_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1372_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v___x_1370_);
v___x_1372_ = v___x_1367_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1391_; 
v_a_1376_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1378_ = v___x_1364_;
v_isShared_1379_ = v_isSharedCheck_1391_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1364_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1391_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1380_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0));
v___x_1381_ = lean_io_error_to_string(v_a_1376_);
v___x_1382_ = lean_string_append(v___x_1380_, v___x_1381_);
lean_dec_ref(v___x_1381_);
v___x_1383_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1384_ = lean_string_append(v___x_1382_, v___x_1383_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1384_);
v___x_1386_ = v___x_1362_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1388_; 
if (v_isShared_1379_ == 0)
{
lean_ctor_set_tag(v___x_1378_, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1386_);
v___x_1388_ = v___x_1378_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___boxed(lean_object* v_ppCtx_1393_, lean_object* v_info_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_ppCtx_1393_, v_info_1394_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(lean_object* v_x_1397_, lean_object* v_x_1398_){
_start:
{
if (lean_obj_tag(v_x_1397_) == 0)
{
lean_object* v___x_1399_; 
v___x_1399_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_1399_;
}
else
{
lean_object* v_val_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1411_; 
v_val_1400_ = lean_ctor_get(v_x_1397_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_x_1397_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1402_ = v_x_1397_;
v_isShared_1403_ = v_isSharedCheck_1411_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_val_1400_);
lean_dec(v_x_1397_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1411_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1404_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_1405_ = l_String_quote(v_val_1400_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set_tag(v___x_1402_, 3);
lean_ctor_set(v___x_1402_, 0, v___x_1405_);
v___x_1407_ = v___x_1402_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1404_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
v___x_1409_ = l_Repr_addAppParen(v___x_1408_, v_x_1398_);
return v___x_1409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(lean_object* v_x_1412_, lean_object* v_x_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_x_1412_, v_x_1413_);
lean_dec(v_x_1413_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object* v_ctx_1429_, lean_object* v_info_1430_){
_start:
{
lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v_toTermInfo_1438_; lean_object* v_location_x3f_1439_; uint8_t v_explicit_1440_; lean_object* v___y_1442_; 
v_toTermInfo_1438_ = lean_ctor_get(v_info_1430_, 0);
lean_inc_ref(v_toTermInfo_1438_);
v_location_x3f_1439_ = lean_ctor_get(v_info_1430_, 1);
lean_inc(v_location_x3f_1439_);
v_explicit_1440_ = lean_ctor_get_uint8(v_info_1430_, sizeof(void*)*3);
if (lean_obj_tag(v_location_x3f_1439_) == 1)
{
lean_object* v_val_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1524_; 
v_val_1463_ = lean_ctor_get(v_location_x3f_1439_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_location_x3f_1439_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1465_ = v_location_x3f_1439_;
v_isShared_1466_ = v_isSharedCheck_1524_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_val_1463_);
lean_dec(v_location_x3f_1439_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1524_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v_range_1467_; lean_object* v_pos_1468_; lean_object* v_endPos_1469_; lean_object* v_module_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1522_; 
v_range_1467_ = lean_ctor_get(v_val_1463_, 1);
v_pos_1468_ = lean_ctor_get(v_range_1467_, 0);
lean_inc_ref(v_pos_1468_);
v_endPos_1469_ = lean_ctor_get(v_range_1467_, 2);
lean_inc_ref(v_endPos_1469_);
v_module_1470_ = lean_ctor_get(v_val_1463_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_val_1463_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; 
v_unused_1523_ = lean_ctor_get(v_val_1463_, 1);
lean_dec(v_unused_1523_);
v___x_1472_ = v_val_1463_;
v_isShared_1473_ = v_isSharedCheck_1522_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_module_1470_);
lean_dec(v_val_1463_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1522_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v_line_1474_; lean_object* v_column_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1521_; 
v_line_1474_ = lean_ctor_get(v_pos_1468_, 0);
v_column_1475_ = lean_ctor_get(v_pos_1468_, 1);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_pos_1468_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1477_ = v_pos_1468_;
v_isShared_1478_ = v_isSharedCheck_1521_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_column_1475_);
lean_inc(v_line_1474_);
lean_dec(v_pos_1468_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1521_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v_line_1479_; lean_object* v_column_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1520_; 
v_line_1479_ = lean_ctor_get(v_endPos_1469_, 0);
v_column_1480_ = lean_ctor_get(v_endPos_1469_, 1);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_endPos_1469_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1482_ = v_endPos_1469_;
v_isShared_1483_ = v_isSharedCheck_1520_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_column_1480_);
lean_inc(v_line_1479_);
lean_dec(v_endPos_1469_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1520_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
uint8_t v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1484_ = 1;
v___x_1485_ = l_Lean_Name_toString(v_module_1470_, v___x_1484_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set_tag(v___x_1465_, 3);
lean_ctor_set(v___x_1465_, 0, v___x_1485_);
v___x_1487_ = v___x_1465_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1488_; lean_object* v___x_1490_; 
v___x_1488_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
if (v_isShared_1483_ == 0)
{
lean_ctor_set_tag(v___x_1482_, 5);
lean_ctor_set(v___x_1482_, 1, v___x_1488_);
lean_ctor_set(v___x_1482_, 0, v___x_1487_);
v___x_1490_ = v___x_1482_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1491_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_1492_ = l_Nat_reprFast(v_line_1474_);
v___x_1493_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set_tag(v___x_1477_, 5);
lean_ctor_set(v___x_1477_, 1, v___x_1493_);
lean_ctor_set(v___x_1477_, 0, v___x_1491_);
v___x_1495_ = v___x_1477_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1496_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
if (v_isShared_1473_ == 0)
{
lean_ctor_set_tag(v___x_1472_, 5);
lean_ctor_set(v___x_1472_, 1, v___x_1496_);
lean_ctor_set(v___x_1472_, 0, v___x_1495_);
v___x_1498_ = v___x_1472_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1499_ = l_Nat_reprFast(v_column_1475_);
v___x_1500_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
v___x_1501_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1498_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
v___x_1502_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v___x_1503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1501_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___x_1504_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1490_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
v___x_1505_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_1506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1504_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = l_Nat_reprFast(v_line_1479_);
v___x_1508_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
v___x_1509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1491_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v___x_1496_);
v___x_1511_ = l_Nat_reprFast(v_column_1480_);
v___x_1512_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
v___x_1513_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1510_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v___x_1502_);
v___x_1515_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1506_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
v___y_1442_ = v___x_1515_;
goto v___jp_1441_;
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
lean_object* v___x_1525_; 
lean_dec(v_location_x3f_1439_);
v___x_1525_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
v___y_1442_ = v___x_1525_;
goto v___jp_1441_;
}
v___jp_1432_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_inc_ref(v___y_1434_);
v___x_1435_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___y_1434_);
v___x_1436_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___y_1433_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
return v___x_1437_;
}
v___jp_1441_:
{
lean_object* v_lctx_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v_a_1446_; lean_object* v___x_1447_; 
v_lctx_1443_ = lean_ctor_get(v_toTermInfo_1438_, 1);
lean_inc_ref(v_lctx_1443_);
v___x_1444_ = l_Lean_Elab_ContextInfo_toPPContext(v_ctx_1429_, v_lctx_1443_);
v___x_1445_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v___x_1444_, v_info_1430_);
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref(v___x_1445_);
v___x_1447_ = l_Lean_Elab_TermInfo_format(v_ctx_1429_, v_toTermInfo_1438_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1447_, 1);
v___x_1449_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__1));
v___x_1450_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
lean_ctor_set(v___x_1450_, 1, v_a_1448_);
v___x_1451_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__3));
v___x_1452_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
lean_ctor_set(v___x_1453_, 1, v___y_1442_);
v___x_1454_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__5));
v___x_1455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1453_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = lean_unsigned_to_nat(0u);
v___x_1457_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_a_1446_, v___x_1456_);
v___x_1458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1455_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__7));
v___x_1460_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1458_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
if (v_explicit_1440_ == 0)
{
lean_object* v___x_1461_; 
v___x_1461_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__8));
v___y_1433_ = v___x_1460_;
v___y_1434_ = v___x_1461_;
goto v___jp_1432_;
}
else
{
lean_object* v___x_1462_; 
v___x_1462_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__9));
v___y_1433_ = v___x_1460_;
v___y_1434_ = v___x_1462_;
goto v___jp_1432_;
}
}
else
{
lean_dec(v_a_1446_);
lean_dec(v___y_1442_);
return v___x_1447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object* v_ctx_1526_, lean_object* v_info_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1526_, v_info_1527_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object* v_ctx_1533_, lean_object* v_info_1534_){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1535_ = ((lean_object*)(l_Lean_Elab_ChoiceInfo_format___closed__1));
v___x_1536_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1533_, v_info_1534_);
v___x_1537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1535_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceResolutionInfo_format(lean_object* v_ctx_1550_, lean_object* v_info_1551_){
_start:
{
lean_object* v_stx_1552_; lean_object* v_chosenAltIdx_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1581_; 
v_stx_1552_ = lean_ctor_get(v_info_1551_, 0);
v_chosenAltIdx_1553_ = lean_ctor_get(v_info_1551_, 1);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_info_1551_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1555_ = v_info_1551_;
v_isShared_1556_ = v_isSharedCheck_1581_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_chosenAltIdx_1553_);
lean_inc(v_stx_1552_);
lean_dec(v_info_1551_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1581_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1557_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__1));
lean_inc(v_chosenAltIdx_1553_);
v___x_1558_ = l_Nat_reprFast(v_chosenAltIdx_1553_);
v___x_1559_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set_tag(v___x_1555_, 5);
lean_ctor_set(v___x_1555_, 1, v___x_1559_);
lean_ctor_set(v___x_1555_, 0, v___x_1557_);
v___x_1561_ = v___x_1555_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1557_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1562_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__3));
v___x_1563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = l_Lean_Syntax_getNumArgs(v_stx_1552_);
v___x_1565_ = l_Nat_reprFast(v___x_1564_);
v___x_1566_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
v___x_1567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1563_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__5));
v___x_1569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1567_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___x_1570_ = l_Lean_Syntax_getArg(v_stx_1552_, v_chosenAltIdx_1553_);
lean_dec(v_chosenAltIdx_1553_);
v___x_1571_ = l_Lean_Syntax_getKind(v___x_1570_);
v___x_1572_ = 1;
v___x_1573_ = l_Lean_Name_toString(v___x_1571_, v___x_1572_);
v___x_1574_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
v___x_1575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1569_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__7));
v___x_1577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1550_, v_stx_1552_);
lean_dec(v_stx_1552_);
v___x_1579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
return v___x_1579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object* v_ctx_1585_, lean_object* v_info_1586_){
_start:
{
lean_object* v_stx_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v_stx_1587_ = lean_ctor_get(v_info_1586_, 1);
v___x_1588_ = ((lean_object*)(l_Lean_Elab_DocInfo_format___closed__1));
lean_inc(v_stx_1587_);
v___x_1589_ = l_Lean_Syntax_getKind(v_stx_1587_);
v___x_1590_ = 1;
v___x_1591_ = l_Lean_Name_toString(v___x_1589_, v___x_1590_);
v___x_1592_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
v___x_1593_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1588_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1585_, v_info_1586_);
v___x_1597_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object* v_ctx_1601_, lean_object* v_info_1602_){
_start:
{
lean_object* v_toElabInfo_1603_; lean_object* v_name_1604_; uint8_t v_kind_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v_toElabInfo_1603_ = lean_ctor_get(v_info_1602_, 0);
lean_inc_ref(v_toElabInfo_1603_);
v_name_1604_ = lean_ctor_get(v_info_1602_, 1);
lean_inc(v_name_1604_);
v_kind_1605_ = lean_ctor_get_uint8(v_info_1602_, sizeof(void*)*2);
lean_dec_ref(v_info_1602_);
v___x_1606_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__1));
v___x_1607_ = 1;
v___x_1608_ = l_Lean_Name_toString(v_name_1604_, v___x_1607_);
v___x_1609_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
v___x_1610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1606_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__5));
v___x_1612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_unsigned_to_nat(0u);
v___x_1614_ = l_Lean_Elab_instReprDocElabKind_repr(v_kind_1605_, v___x_1613_);
v___x_1615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1612_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__7));
v___x_1617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1615_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
v___x_1618_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1601_, v_toElabInfo_1603_);
v___x_1619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1617_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object* v_ctx_1620_, lean_object* v_x_1621_){
_start:
{
switch(lean_obj_tag(v_x_1621_))
{
case 0:
{
lean_object* v_i_1623_; lean_object* v___x_1624_; 
v_i_1623_ = lean_ctor_get(v_x_1621_, 0);
lean_inc_ref(v_i_1623_);
lean_dec_ref_known(v_x_1621_, 1);
v___x_1624_ = l_Lean_Elab_TacticInfo_format(v_ctx_1620_, v_i_1623_);
return v___x_1624_;
}
case 1:
{
lean_object* v_i_1625_; lean_object* v___x_1626_; 
v_i_1625_ = lean_ctor_get(v_x_1621_, 0);
lean_inc_ref(v_i_1625_);
lean_dec_ref_known(v_x_1621_, 1);
v___x_1626_ = l_Lean_Elab_TermInfo_format(v_ctx_1620_, v_i_1625_);
return v___x_1626_;
}
case 2:
{
lean_object* v_i_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1635_; 
v_i_1627_ = lean_ctor_get(v_x_1621_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_x_1621_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1629_ = v_x_1621_;
v_isShared_1630_ = v_isSharedCheck_1635_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_i_1627_);
lean_dec(v_x_1621_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1635_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1631_ = l_Lean_Elab_PartialTermInfo_format(v_ctx_1620_, v_i_1627_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set_tag(v___x_1629_, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1631_);
v___x_1633_ = v___x_1629_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
case 3:
{
lean_object* v_i_1636_; lean_object* v___x_1637_; 
v_i_1636_ = lean_ctor_get(v_x_1621_, 0);
lean_inc_ref(v_i_1636_);
lean_dec_ref_known(v_x_1621_, 1);
v___x_1637_ = l_Lean_Elab_CommandInfo_format(v_ctx_1620_, v_i_1636_);
return v___x_1637_;
}
case 4:
{
lean_object* v_i_1638_; lean_object* v___x_1639_; 
v_i_1638_ = lean_ctor_get(v_x_1621_, 0);
lean_inc_ref(v_i_1638_);
lean_dec_ref_known(v_x_1621_, 1);
v___x_1639_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1620_, v_i_1638_);
lean_dec_ref(v_ctx_1620_);
return v___x_1639_;
}
case 5:
{
lean_object* v_i_1640_; lean_object* v___x_1641_; 
v_i_1640_ = lean_ctor_get(v_x_1621_, 0);
lean_inc_ref(v_i_1640_);
lean_dec_ref_known(v_x_1621_, 1);
v___x_1641_ = l_Lean_Elab_OptionInfo_format(v_ctx_1620_, v_i_1640_);
return v___x_1641_;
}
case 6:
{
lean_object* v_i_1642_; lean_object* v___x_1643_; 
v_i_1642_ = lean_ctor_get(v_x_1621_, 0);
lean_inc_ref(v_i_1642_);
lean_dec_ref_known(v_x_1621_, 1);
v___x_1643_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_1620_, v_i_1642_);
return v___x_1643_;
}
case 7:
{
lean_object* v_i_1644_; lean_object* v___x_1645_; 
v_i_1644_ = lean_ctor_get(v_x_1621_, 0);
lean_inc_ref(v_i_1644_);
lean_dec_ref_known(v_x_1621_, 1);
v___x_1645_ = l_Lean_Elab_FieldInfo_format(v_ctx_1620_, v_i_1644_);
return v___x_1645_;
}
case 8:
{
lean_object* v_i_1646_; lean_object* v___x_1647_; 
v_i_1646_ = lean_ctor_get(v_x_1621_, 0);
lean_inc_ref(v_i_1646_);
lean_dec_ref_known(v_x_1621_, 1);
v___x_1647_ = l_Lean_Elab_CompletionInfo_format(v_ctx_1620_, v_i_1646_);
return v___x_1647_;
}
case 9:
{
lean_object* v_i_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1656_; 
lean_dec_ref(v_ctx_1620_);
v_i_1648_ = lean_ctor_get(v_x_1621_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_x_1621_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1650_ = v_x_1621_;
v_isShared_1651_ = v_isSharedCheck_1656_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_i_1648_);
lean_dec(v_x_1621_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1656_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1652_ = l_Lean_Elab_UserWidgetInfo_format(v_i_1648_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set_tag(v___x_1650_, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1652_);
v___x_1654_ = v___x_1650_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
case 10:
{
lean_object* v_i_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1665_; 
lean_dec_ref(v_ctx_1620_);
v_i_1657_ = lean_ctor_get(v_x_1621_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_x_1621_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1659_ = v_x_1621_;
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_i_1657_);
lean_dec(v_x_1621_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = l_Lean_Elab_CustomInfo_format(v_i_1657_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set_tag(v___x_1659_, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1661_);
v___x_1663_ = v___x_1659_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
case 11:
{
lean_object* v_i_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1674_; 
lean_dec_ref(v_ctx_1620_);
v_i_1666_ = lean_ctor_get(v_x_1621_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_x_1621_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1668_ = v_x_1621_;
v_isShared_1669_ = v_isSharedCheck_1674_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_i_1666_);
lean_dec(v_x_1621_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1674_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1670_ = l_Lean_Elab_FVarAliasInfo_format(v_i_1666_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set_tag(v___x_1668_, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1670_);
v___x_1672_ = v___x_1668_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
case 12:
{
lean_object* v_i_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1683_; 
v_i_1675_ = lean_ctor_get(v_x_1621_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_x_1621_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1677_ = v_x_1621_;
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_i_1675_);
lean_dec(v_x_1621_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1620_, v_i_1675_);
lean_dec(v_i_1675_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set_tag(v___x_1677_, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1679_);
v___x_1681_ = v___x_1677_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
case 13:
{
lean_object* v_i_1684_; lean_object* v___x_1685_; 
v_i_1684_ = lean_ctor_get(v_x_1621_, 0);
lean_inc_ref(v_i_1684_);
lean_dec_ref_known(v_x_1621_, 1);
v___x_1685_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1620_, v_i_1684_);
return v___x_1685_;
}
case 14:
{
lean_object* v_i_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1694_; 
v_i_1686_ = lean_ctor_get(v_x_1621_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_x_1621_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1688_ = v_x_1621_;
v_isShared_1689_ = v_isSharedCheck_1694_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_i_1686_);
lean_dec(v_x_1621_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1694_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = l_Lean_Elab_ChoiceInfo_format(v_ctx_1620_, v_i_1686_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set_tag(v___x_1688_, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1690_);
v___x_1692_ = v___x_1688_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
case 15:
{
lean_object* v_i_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1703_; 
v_i_1695_ = lean_ctor_get(v_x_1621_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_x_1621_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1697_ = v_x_1621_;
v_isShared_1698_ = v_isSharedCheck_1703_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_i_1695_);
lean_dec(v_x_1621_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1703_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1699_ = l_Lean_Elab_ChoiceResolutionInfo_format(v_ctx_1620_, v_i_1695_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set_tag(v___x_1697_, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1699_);
v___x_1701_ = v___x_1697_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
case 16:
{
lean_object* v_i_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1712_; 
v_i_1704_ = lean_ctor_get(v_x_1621_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_x_1621_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1706_ = v_x_1621_;
v_isShared_1707_ = v_isSharedCheck_1712_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_i_1704_);
lean_dec(v_x_1621_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1712_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1708_; lean_object* v___x_1710_; 
v___x_1708_ = l_Lean_Elab_DocInfo_format(v_ctx_1620_, v_i_1704_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set_tag(v___x_1706_, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1708_);
v___x_1710_ = v___x_1706_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
default: 
{
lean_object* v_i_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1721_; 
v_i_1713_ = lean_ctor_get(v_x_1621_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_x_1621_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1715_ = v_x_1621_;
v_isShared_1716_ = v_isSharedCheck_1721_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_i_1713_);
lean_dec(v_x_1621_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1721_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1717_ = l_Lean_Elab_DocElabInfo_format(v_ctx_1620_, v_i_1713_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set_tag(v___x_1715_, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1717_);
v___x_1719_ = v___x_1715_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object* v_ctx_1722_, lean_object* v_x_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_Elab_Info_format(v_ctx_1722_, v_x_1723_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object* v_x_1726_, lean_object* v_x_1727_){
_start:
{
if (lean_obj_tag(v_x_1727_) == 0)
{
return v_x_1726_;
}
else
{
lean_object* v_head_1728_; lean_object* v_tail_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_head_1728_ = lean_ctor_get(v_x_1727_, 0);
v_tail_1729_ = lean_ctor_get(v_x_1727_, 1);
v___x_1730_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2));
v___x_1731_ = lean_string_append(v_x_1726_, v___x_1730_);
v___x_1732_ = lean_expr_dbg_to_string(v_head_1728_);
v___x_1733_ = lean_string_append(v___x_1731_, v___x_1732_);
lean_dec_ref(v___x_1732_);
v_x_1726_ = v___x_1733_;
v_x_1727_ = v_tail_1729_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object* v_x_1735_, lean_object* v_x_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v_x_1735_, v_x_1736_);
lean_dec(v_x_1736_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object* v_x_1740_){
_start:
{
if (lean_obj_tag(v_x_1740_) == 0)
{
lean_object* v___x_1741_; 
v___x_1741_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0));
return v___x_1741_;
}
else
{
lean_object* v_tail_1742_; 
v_tail_1742_ = lean_ctor_get(v_x_1740_, 1);
if (lean_obj_tag(v_tail_1742_) == 0)
{
lean_object* v_head_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v_head_1743_ = lean_ctor_get(v_x_1740_, 0);
v___x_1744_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1745_ = lean_expr_dbg_to_string(v_head_1743_);
v___x_1746_ = lean_string_append(v___x_1744_, v___x_1745_);
lean_dec_ref(v___x_1745_);
v___x_1747_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1748_ = lean_string_append(v___x_1746_, v___x_1747_);
return v___x_1748_;
}
else
{
lean_object* v_head_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; uint32_t v___x_1754_; lean_object* v___x_1755_; 
v_head_1749_ = lean_ctor_get(v_x_1740_, 0);
v___x_1750_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1751_ = lean_expr_dbg_to_string(v_head_1749_);
v___x_1752_ = lean_string_append(v___x_1750_, v___x_1751_);
lean_dec_ref(v___x_1751_);
v___x_1753_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v___x_1752_, v_tail_1742_);
v___x_1754_ = 93;
v___x_1755_ = lean_string_push(v___x_1753_, v___x_1754_);
return v___x_1755_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object* v_x_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v_x_1756_);
lean_dec(v_x_1756_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object* v_ctx_1764_){
_start:
{
switch(lean_obj_tag(v_ctx_1764_))
{
case 0:
{
lean_object* v___x_1765_; 
lean_dec_ref_known(v_ctx_1764_, 1);
v___x_1765_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__1));
return v___x_1765_;
}
case 1:
{
lean_object* v_parentDecl_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1779_; 
v_parentDecl_1766_ = lean_ctor_get(v_ctx_1764_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_ctx_1764_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1768_ = v_ctx_1764_;
v_isShared_1769_ = v_isSharedCheck_1779_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_parentDecl_1766_);
lean_dec(v_ctx_1764_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1779_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1770_; uint8_t v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1770_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__2));
v___x_1771_ = 1;
v___x_1772_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_parentDecl_1766_, v___x_1771_);
v___x_1773_ = lean_string_append(v___x_1770_, v___x_1772_);
lean_dec_ref(v___x_1772_);
v___x_1774_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1775_ = lean_string_append(v___x_1773_, v___x_1774_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set_tag(v___x_1768_, 3);
lean_ctor_set(v___x_1768_, 0, v___x_1775_);
v___x_1777_ = v___x_1768_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
default: 
{
lean_object* v_autoImplicits_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1795_; 
v_autoImplicits_1780_ = lean_ctor_get(v_ctx_1764_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_ctx_1764_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1782_ = v_ctx_1764_;
v_isShared_1783_ = v_isSharedCheck_1795_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_autoImplicits_1780_);
lean_dec(v_ctx_1764_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1795_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1784_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__3));
v___x_1785_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__4));
v___x_1786_ = lean_array_to_list(v_autoImplicits_1780_);
v___x_1787_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v___x_1786_);
lean_dec(v___x_1786_);
v___x_1788_ = lean_string_append(v___x_1785_, v___x_1787_);
lean_dec_ref(v___x_1787_);
v___x_1789_ = lean_string_append(v___x_1784_, v___x_1788_);
lean_dec_ref(v___x_1788_);
v___x_1790_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1791_ = lean_string_append(v___x_1789_, v___x_1790_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set_tag(v___x_1782_, 3);
lean_ctor_set(v___x_1782_, 0, v___x_1791_);
v___x_1793_ = v___x_1782_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(3, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format(lean_object* v_tree_1805_, lean_object* v_ctx_x3f_1806_){
_start:
{
switch(lean_obj_tag(v_tree_1805_))
{
case 0:
{
lean_object* v_i_1808_; lean_object* v_t_1809_; lean_object* v___x_1810_; 
v_i_1808_ = lean_ctor_get(v_tree_1805_, 0);
lean_inc_ref(v_i_1808_);
v_t_1809_ = lean_ctor_get(v_tree_1805_, 1);
lean_inc_ref(v_t_1809_);
lean_dec_ref_known(v_tree_1805_, 2);
v___x_1810_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1808_, v_ctx_x3f_1806_);
v_tree_1805_ = v_t_1809_;
v_ctx_x3f_1806_ = v___x_1810_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_ctx_x3f_1806_) == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_dec_ref_known(v_tree_1805_, 2);
v___x_1812_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__1));
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
return v___x_1813_;
}
else
{
lean_object* v_i_1814_; lean_object* v_children_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1865_; 
v_i_1814_ = lean_ctor_get(v_tree_1805_, 0);
v_children_1815_ = lean_ctor_get(v_tree_1805_, 1);
v_isSharedCheck_1865_ = !lean_is_exclusive(v_tree_1805_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1817_ = v_tree_1805_;
v_isShared_1818_ = v_isSharedCheck_1865_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_children_1815_);
lean_inc(v_i_1814_);
lean_dec(v_tree_1805_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1865_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v_val_1819_; lean_object* v___x_1820_; 
v_val_1819_ = lean_ctor_get(v_ctx_x3f_1806_, 0);
lean_inc_ref(v_i_1814_);
lean_inc(v_val_1819_);
v___x_1820_ = l_Lean_Elab_Info_format(v_val_1819_, v_i_1814_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1864_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1823_ = v___x_1820_;
v_isShared_1824_ = v_isSharedCheck_1864_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1820_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1864_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v_size_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
v_size_1825_ = lean_ctor_get(v_children_1815_, 2);
v___x_1826_ = lean_unsigned_to_nat(0u);
v___x_1827_ = lean_nat_dec_eq(v_size_1825_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_del_object(v___x_1823_);
v___x_1828_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_1806_, v_i_1814_);
lean_dec_ref(v_i_1814_);
v___x_1829_ = l_Lean_PersistentArray_toList___redArg(v_children_1815_);
lean_dec_ref(v_children_1815_);
v___x_1830_ = lean_box(0);
v___x_1831_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1828_, v___x_1829_, v___x_1830_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1847_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1847_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1847_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1836_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1818_ == 0)
{
lean_ctor_set_tag(v___x_1817_, 5);
lean_ctor_set(v___x_1817_, 1, v_a_1821_);
lean_ctor_set(v___x_1817_, 0, v___x_1836_);
v___x_1838_ = v___x_1817_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_a_1821_);
v___x_1838_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1839_ = lean_box(1);
v___x_1840_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1839_, v_a_1832_);
v___x_1841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1838_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = l_Std_Format_nestD(v___x_1841_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1842_);
v___x_1844_ = v___x_1834_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_dec(v_a_1821_);
lean_del_object(v___x_1817_);
v_a_1848_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1831_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1831_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1858_; 
lean_dec_ref(v_children_1815_);
lean_dec_ref(v_i_1814_);
lean_dec_ref_known(v_ctx_x3f_1806_, 1);
v___x_1856_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1818_ == 0)
{
lean_ctor_set_tag(v___x_1817_, 5);
lean_ctor_set(v___x_1817_, 1, v_a_1821_);
lean_ctor_set(v___x_1817_, 0, v___x_1856_);
v___x_1858_ = v___x_1817_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1856_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_a_1821_);
v___x_1858_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1859_ = l_Std_Format_nestD(v___x_1858_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1859_);
v___x_1861_ = v___x_1823_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
}
else
{
lean_del_object(v___x_1817_);
lean_dec_ref(v_children_1815_);
lean_dec_ref(v_i_1814_);
lean_dec_ref_known(v_ctx_x3f_1806_, 1);
return v___x_1820_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1879_; 
lean_dec(v_ctx_x3f_1806_);
v_mvarId_1866_ = lean_ctor_get(v_tree_1805_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v_tree_1805_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1868_ = v_tree_1805_;
v_isShared_1869_ = v_isSharedCheck_1879_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_mvarId_1866_);
lean_dec(v_tree_1805_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1879_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1870_; uint8_t v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1870_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__5));
v___x_1871_ = 1;
v___x_1872_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_1866_, v___x_1871_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set_tag(v___x_1868_, 3);
lean_ctor_set(v___x_1868_, 0, v___x_1872_);
v___x_1874_ = v___x_1868_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1870_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = l_Std_Format_nestD(v___x_1875_);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object* v___x_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
if (lean_obj_tag(v_x_1881_) == 0)
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_dec(v___x_1880_);
v___x_1884_ = l_List_reverse___redArg(v_x_1882_);
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
return v___x_1885_;
}
else
{
lean_object* v_head_1886_; lean_object* v_tail_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1905_; 
v_head_1886_ = lean_ctor_get(v_x_1881_, 0);
v_tail_1887_ = lean_ctor_get(v_x_1881_, 1);
v_isSharedCheck_1905_ = !lean_is_exclusive(v_x_1881_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1889_ = v_x_1881_;
v_isShared_1890_ = v_isSharedCheck_1905_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_tail_1887_);
lean_inc(v_head_1886_);
lean_dec(v_x_1881_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1905_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; 
lean_inc(v___x_1880_);
v___x_1891_ = l_Lean_Elab_InfoTree_format(v_head_1886_, v___x_1880_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1894_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1891_, 1);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 1, v_x_1882_);
lean_ctor_set(v___x_1889_, 0, v_a_1892_);
v___x_1894_ = v___x_1889_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1892_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_x_1882_);
v___x_1894_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
v_x_1881_ = v_tail_1887_;
v_x_1882_ = v___x_1894_;
goto _start;
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_del_object(v___x_1889_);
lean_dec(v_tail_1887_);
lean_dec(v_x_1882_);
lean_dec(v___x_1880_);
v_a_1897_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1891_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1891_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object* v___x_1906_, lean_object* v_x_1907_, lean_object* v_x_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1906_, v_x_1907_, v_x_1908_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object* v_tree_1911_, lean_object* v_ctx_x3f_1912_, lean_object* v_a_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_Elab_InfoTree_format(v_tree_1911_, v_ctx_x3f_1912_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object* v_f_1915_, lean_object* v_s_1916_){
_start:
{
uint8_t v_enabled_1917_; lean_object* v_assignment_1918_; lean_object* v_lazyAssignment_1919_; lean_object* v_trees_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1928_; 
v_enabled_1917_ = lean_ctor_get_uint8(v_s_1916_, sizeof(void*)*3);
v_assignment_1918_ = lean_ctor_get(v_s_1916_, 0);
v_lazyAssignment_1919_ = lean_ctor_get(v_s_1916_, 1);
v_trees_1920_ = lean_ctor_get(v_s_1916_, 2);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_s_1916_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1922_ = v_s_1916_;
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_trees_1920_);
lean_inc(v_lazyAssignment_1919_);
lean_inc(v_assignment_1918_);
lean_dec(v_s_1916_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1924_ = lean_apply_1(v_f_1915_, v_trees_1920_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 2, v___x_1924_);
v___x_1926_ = v___x_1922_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_assignment_1918_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_lazyAssignment_1919_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v___x_1924_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*3, v_enabled_1917_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object* v_inst_1929_, lean_object* v_f_1930_){
_start:
{
lean_object* v_modifyInfoState_1931_; lean_object* v___f_1932_; lean_object* v___x_1933_; 
v_modifyInfoState_1931_ = lean_ctor_get(v_inst_1929_, 1);
lean_inc(v_modifyInfoState_1931_);
lean_dec_ref(v_inst_1929_);
v___f_1932_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1932_, 0, v_f_1930_);
v___x_1933_ = lean_apply_1(v_modifyInfoState_1931_, v___f_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object* v_m_1934_, lean_object* v_inst_1935_, lean_object* v_f_1936_){
_start:
{
lean_object* v_modifyInfoState_1937_; lean_object* v___f_1938_; lean_object* v___x_1939_; 
v_modifyInfoState_1937_ = lean_ctor_get(v_inst_1935_, 1);
lean_inc(v_modifyInfoState_1937_);
lean_dec_ref(v_inst_1935_);
v___f_1938_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1938_, 0, v_f_1936_);
v___x_1939_ = lean_apply_1(v_modifyInfoState_1937_, v___f_1938_);
return v___x_1939_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1940_ = lean_unsigned_to_nat(32u);
v___x_1941_ = lean_mk_empty_array_with_capacity(v___x_1940_);
v___x_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
return v___x_1942_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1943_ = ((size_t)5ULL);
v___x_1944_ = lean_unsigned_to_nat(0u);
v___x_1945_ = lean_unsigned_to_nat(32u);
v___x_1946_ = lean_mk_empty_array_with_capacity(v___x_1945_);
v___x_1947_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0);
v___x_1948_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
lean_ctor_set(v___x_1948_, 1, v___x_1946_);
lean_ctor_set(v___x_1948_, 2, v___x_1944_);
lean_ctor_set(v___x_1948_, 3, v___x_1944_);
lean_ctor_set_usize(v___x_1948_, 4, v___x_1943_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object* v_s_1949_){
_start:
{
uint8_t v_enabled_1950_; lean_object* v_assignment_1951_; lean_object* v_lazyAssignment_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1960_; 
v_enabled_1950_ = lean_ctor_get_uint8(v_s_1949_, sizeof(void*)*3);
v_assignment_1951_ = lean_ctor_get(v_s_1949_, 0);
v_lazyAssignment_1952_ = lean_ctor_get(v_s_1949_, 1);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_s_1949_);
if (v_isSharedCheck_1960_ == 0)
{
lean_object* v_unused_1961_; 
v_unused_1961_ = lean_ctor_get(v_s_1949_, 2);
lean_dec(v_unused_1961_);
v___x_1954_ = v_s_1949_;
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_lazyAssignment_1952_);
lean_inc(v_assignment_1951_);
lean_dec(v_s_1949_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1956_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 2, v___x_1956_);
v___x_1958_ = v___x_1954_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_assignment_1951_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_lazyAssignment_1952_);
lean_ctor_set(v_reuseFailAlloc_1959_, 2, v___x_1956_);
lean_ctor_set_uint8(v_reuseFailAlloc_1959_, sizeof(void*)*3, v_enabled_1950_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object* v_toPure_1962_, lean_object* v_trees_1963_, lean_object* v_____r_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = lean_apply_2(v_toPure_1962_, lean_box(0), v_trees_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object* v_toPure_1966_, lean_object* v_modifyInfoState_1967_, lean_object* v___f_1968_, lean_object* v_toBind_1969_, lean_object* v_____do__lift_1970_){
_start:
{
lean_object* v_trees_1971_; lean_object* v___f_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v_trees_1971_ = lean_ctor_get(v_____do__lift_1970_, 2);
lean_inc_ref(v_trees_1971_);
lean_dec_ref(v_____do__lift_1970_);
v___f_1972_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1972_, 0, v_toPure_1966_);
lean_closure_set(v___f_1972_, 1, v_trees_1971_);
v___x_1973_ = lean_apply_1(v_modifyInfoState_1967_, v___f_1968_);
v___x_1974_ = lean_apply_4(v_toBind_1969_, lean_box(0), lean_box(0), v___x_1973_, v___f_1972_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object* v_inst_1976_, lean_object* v_inst_1977_){
_start:
{
lean_object* v_toApplicative_1978_; lean_object* v_toBind_1979_; lean_object* v_getInfoState_1980_; lean_object* v_modifyInfoState_1981_; lean_object* v_toPure_1982_; lean_object* v___f_1983_; lean_object* v___f_1984_; lean_object* v___x_1985_; 
v_toApplicative_1978_ = lean_ctor_get(v_inst_1976_, 0);
lean_inc_ref(v_toApplicative_1978_);
v_toBind_1979_ = lean_ctor_get(v_inst_1976_, 1);
lean_inc_n(v_toBind_1979_, 2);
lean_dec_ref(v_inst_1976_);
v_getInfoState_1980_ = lean_ctor_get(v_inst_1977_, 0);
lean_inc(v_getInfoState_1980_);
v_modifyInfoState_1981_ = lean_ctor_get(v_inst_1977_, 1);
lean_inc(v_modifyInfoState_1981_);
lean_dec_ref(v_inst_1977_);
v_toPure_1982_ = lean_ctor_get(v_toApplicative_1978_, 1);
lean_inc(v_toPure_1982_);
lean_dec_ref(v_toApplicative_1978_);
v___f_1983_ = ((lean_object*)(l_Lean_Elab_getResetInfoTrees___redArg___closed__0));
v___f_1984_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1984_, 0, v_toPure_1982_);
lean_closure_set(v___f_1984_, 1, v_modifyInfoState_1981_);
lean_closure_set(v___f_1984_, 2, v___f_1983_);
lean_closure_set(v___f_1984_, 3, v_toBind_1979_);
v___x_1985_ = lean_apply_4(v_toBind_1979_, lean_box(0), lean_box(0), v_getInfoState_1980_, v___f_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object* v_m_1986_, lean_object* v_inst_1987_, lean_object* v_inst_1988_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_1987_, v_inst_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object* v_t_1990_, lean_object* v_s_1991_){
_start:
{
uint8_t v_enabled_1992_; lean_object* v_assignment_1993_; lean_object* v_lazyAssignment_1994_; lean_object* v_trees_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2003_; 
v_enabled_1992_ = lean_ctor_get_uint8(v_s_1991_, sizeof(void*)*3);
v_assignment_1993_ = lean_ctor_get(v_s_1991_, 0);
v_lazyAssignment_1994_ = lean_ctor_get(v_s_1991_, 1);
v_trees_1995_ = lean_ctor_get(v_s_1991_, 2);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_s_1991_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1997_ = v_s_1991_;
v_isShared_1998_ = v_isSharedCheck_2003_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_trees_1995_);
lean_inc(v_lazyAssignment_1994_);
lean_inc(v_assignment_1993_);
lean_dec(v_s_1991_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2003_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1999_ = l_Lean_PersistentArray_push___redArg(v_trees_1995_, v_t_1990_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 2, v___x_1999_);
v___x_2001_ = v___x_1997_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_assignment_1993_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_lazyAssignment_1994_);
lean_ctor_set(v_reuseFailAlloc_2002_, 2, v___x_1999_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, sizeof(void*)*3, v_enabled_1992_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object* v_toPure_2004_, lean_object* v_modifyInfoState_2005_, lean_object* v___f_2006_, lean_object* v_____do__lift_2007_){
_start:
{
uint8_t v_enabled_2008_; 
v_enabled_2008_ = lean_ctor_get_uint8(v_____do__lift_2007_, sizeof(void*)*3);
if (v_enabled_2008_ == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_dec_ref(v___f_2006_);
lean_dec(v_modifyInfoState_2005_);
v___x_2009_ = lean_box(0);
v___x_2010_ = lean_apply_2(v_toPure_2004_, lean_box(0), v___x_2009_);
return v___x_2010_;
}
else
{
lean_object* v___x_2011_; 
lean_dec(v_toPure_2004_);
v___x_2011_ = lean_apply_1(v_modifyInfoState_2005_, v___f_2006_);
return v___x_2011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object* v_toPure_2012_, lean_object* v_modifyInfoState_2013_, lean_object* v___f_2014_, lean_object* v_____do__lift_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_Elab_pushInfoTree___redArg___lam__1(v_toPure_2012_, v_modifyInfoState_2013_, v___f_2014_, v_____do__lift_2015_);
lean_dec_ref(v_____do__lift_2015_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_t_2019_){
_start:
{
lean_object* v_toApplicative_2020_; lean_object* v_toBind_2021_; lean_object* v_getInfoState_2022_; lean_object* v_modifyInfoState_2023_; lean_object* v_toPure_2024_; lean_object* v___f_2025_; lean_object* v___f_2026_; lean_object* v___x_2027_; 
v_toApplicative_2020_ = lean_ctor_get(v_inst_2017_, 0);
lean_inc_ref(v_toApplicative_2020_);
v_toBind_2021_ = lean_ctor_get(v_inst_2017_, 1);
lean_inc(v_toBind_2021_);
lean_dec_ref(v_inst_2017_);
v_getInfoState_2022_ = lean_ctor_get(v_inst_2018_, 0);
lean_inc(v_getInfoState_2022_);
v_modifyInfoState_2023_ = lean_ctor_get(v_inst_2018_, 1);
lean_inc(v_modifyInfoState_2023_);
lean_dec_ref(v_inst_2018_);
v_toPure_2024_ = lean_ctor_get(v_toApplicative_2020_, 1);
lean_inc(v_toPure_2024_);
lean_dec_ref(v_toApplicative_2020_);
v___f_2025_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2025_, 0, v_t_2019_);
v___f_2026_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2026_, 0, v_toPure_2024_);
lean_closure_set(v___f_2026_, 1, v_modifyInfoState_2023_);
lean_closure_set(v___f_2026_, 2, v___f_2025_);
v___x_2027_ = lean_apply_4(v_toBind_2021_, lean_box(0), lean_box(0), v_getInfoState_2022_, v___f_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object* v_m_2028_, lean_object* v_inst_2029_, lean_object* v_inst_2030_, lean_object* v_t_2031_){
_start:
{
lean_object* v___x_2032_; 
v___x_2032_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2029_, v_inst_2030_, v_t_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object* v_toPure_2033_, lean_object* v_t_2034_, lean_object* v_inst_2035_, lean_object* v_inst_2036_, lean_object* v_____do__lift_2037_){
_start:
{
uint8_t v_enabled_2038_; 
v_enabled_2038_ = lean_ctor_get_uint8(v_____do__lift_2037_, sizeof(void*)*3);
if (v_enabled_2038_ == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_dec_ref(v_inst_2036_);
lean_dec_ref(v_inst_2035_);
lean_dec_ref(v_t_2034_);
v___x_2039_ = lean_box(0);
v___x_2040_ = lean_apply_2(v_toPure_2033_, lean_box(0), v___x_2039_);
return v___x_2040_;
}
else
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
lean_dec(v_toPure_2033_);
v___x_2041_ = lean_unsigned_to_nat(32u);
v___x_2042_ = lean_mk_empty_array_with_capacity(v___x_2041_);
lean_dec_ref(v___x_2042_);
v___x_2043_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2044_, 0, v_t_2034_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2035_, v_inst_2036_, v___x_2044_);
return v___x_2045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object* v_toPure_2046_, lean_object* v_t_2047_, lean_object* v_inst_2048_, lean_object* v_inst_2049_, lean_object* v_____do__lift_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_Elab_pushInfoLeaf___redArg___lam__0(v_toPure_2046_, v_t_2047_, v_inst_2048_, v_inst_2049_, v_____do__lift_2050_);
lean_dec_ref(v_____do__lift_2050_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_t_2054_){
_start:
{
lean_object* v_toApplicative_2055_; lean_object* v_toBind_2056_; lean_object* v_getInfoState_2057_; lean_object* v_toPure_2058_; lean_object* v___f_2059_; lean_object* v___x_2060_; 
v_toApplicative_2055_ = lean_ctor_get(v_inst_2052_, 0);
v_toBind_2056_ = lean_ctor_get(v_inst_2052_, 1);
lean_inc(v_toBind_2056_);
v_getInfoState_2057_ = lean_ctor_get(v_inst_2053_, 0);
lean_inc(v_getInfoState_2057_);
v_toPure_2058_ = lean_ctor_get(v_toApplicative_2055_, 1);
lean_inc(v_toPure_2058_);
v___f_2059_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2059_, 0, v_toPure_2058_);
lean_closure_set(v___f_2059_, 1, v_t_2054_);
lean_closure_set(v___f_2059_, 2, v_inst_2052_);
lean_closure_set(v___f_2059_, 3, v_inst_2053_);
v___x_2060_ = lean_apply_4(v_toBind_2056_, lean_box(0), lean_box(0), v_getInfoState_2057_, v___f_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object* v_m_2061_, lean_object* v_inst_2062_, lean_object* v_inst_2063_, lean_object* v_t_2064_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2062_, v_inst_2063_, v_t_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object* v_inst_2066_, lean_object* v_inst_2067_, lean_object* v_info_2068_){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2069_, 0, v_info_2068_);
v___x_2070_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2066_, v_inst_2067_, v___x_2069_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object* v_m_2071_, lean_object* v_inst_2072_, lean_object* v_inst_2073_, lean_object* v_info_2074_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_2072_, v_inst_2073_, v_info_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object* v_stx_2076_, lean_object* v_expectedType_x3f_2077_, lean_object* v_inst_2078_, lean_object* v_inst_2079_, lean_object* v_____do__lift_2080_){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2081_ = lean_box(0);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
lean_ctor_set(v___x_2082_, 1, v_stx_2076_);
v___x_2083_ = l_Lean_LocalContext_empty;
v___x_2084_ = 0;
v___x_2085_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2085_, 0, v___x_2082_);
lean_ctor_set(v___x_2085_, 1, v___x_2083_);
lean_ctor_set(v___x_2085_, 2, v_expectedType_x3f_2077_);
lean_ctor_set(v___x_2085_, 3, v_____do__lift_2080_);
lean_ctor_set_uint8(v___x_2085_, sizeof(void*)*4, v___x_2084_);
lean_ctor_set_uint8(v___x_2085_, sizeof(void*)*4 + 1, v___x_2084_);
v___x_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
v___x_2087_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2078_, v_inst_2079_, v___x_2086_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object* v_inst_2088_, lean_object* v_inst_2089_, lean_object* v_inst_2090_, lean_object* v_inst_2091_, lean_object* v_stx_2092_, lean_object* v_n_2093_, lean_object* v_expectedType_x3f_2094_){
_start:
{
lean_object* v_toBind_2095_; lean_object* v___f_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v_toBind_2095_ = lean_ctor_get(v_inst_2088_, 1);
lean_inc(v_toBind_2095_);
lean_inc_ref(v_inst_2088_);
v___f_2096_ = lean_alloc_closure((void*)(l_Lean_Elab_addConstInfo___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2096_, 0, v_stx_2092_);
lean_closure_set(v___f_2096_, 1, v_expectedType_x3f_2094_);
lean_closure_set(v___f_2096_, 2, v_inst_2088_);
lean_closure_set(v___f_2096_, 3, v_inst_2089_);
v___x_2097_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_2088_, v_inst_2090_, v_inst_2091_, v_n_2093_);
v___x_2098_ = lean_apply_4(v_toBind_2095_, lean_box(0), lean_box(0), v___x_2097_, v___f_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object* v_m_2099_, lean_object* v_inst_2100_, lean_object* v_inst_2101_, lean_object* v_inst_2102_, lean_object* v_inst_2103_, lean_object* v_stx_2104_, lean_object* v_n_2105_, lean_object* v_expectedType_x3f_2106_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_Elab_addConstInfo___redArg(v_inst_2100_, v_inst_2101_, v_inst_2102_, v_inst_2103_, v_stx_2104_, v_n_2105_, v_expectedType_x3f_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v___x_2111_; lean_object* v_infoState_2112_; uint8_t v_enabled_2113_; 
v___x_2111_ = lean_st_ref_get(v___y_2109_);
v_infoState_2112_ = lean_ctor_get(v___x_2111_, 8);
lean_inc_ref(v_infoState_2112_);
lean_dec(v___x_2111_);
v_enabled_2113_ = lean_ctor_get_uint8(v_infoState_2112_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2112_);
if (v_enabled_2113_ == 0)
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
lean_dec_ref(v_t_2108_);
v___x_2114_ = lean_box(0);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
return v___x_2115_;
}
else
{
lean_object* v___x_2116_; lean_object* v_infoState_2117_; lean_object* v_env_2118_; lean_object* v_nextMacroScope_2119_; lean_object* v_ngen_2120_; lean_object* v_auxDeclNGen_2121_; lean_object* v_traceState_2122_; lean_object* v_cache_2123_; lean_object* v_recordedDeps_2124_; lean_object* v_messages_2125_; lean_object* v_snapshotTasks_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2148_; 
v___x_2116_ = lean_st_ref_take(v___y_2109_);
v_infoState_2117_ = lean_ctor_get(v___x_2116_, 8);
v_env_2118_ = lean_ctor_get(v___x_2116_, 0);
v_nextMacroScope_2119_ = lean_ctor_get(v___x_2116_, 1);
v_ngen_2120_ = lean_ctor_get(v___x_2116_, 2);
v_auxDeclNGen_2121_ = lean_ctor_get(v___x_2116_, 3);
v_traceState_2122_ = lean_ctor_get(v___x_2116_, 4);
v_cache_2123_ = lean_ctor_get(v___x_2116_, 5);
v_recordedDeps_2124_ = lean_ctor_get(v___x_2116_, 6);
v_messages_2125_ = lean_ctor_get(v___x_2116_, 7);
v_snapshotTasks_2126_ = lean_ctor_get(v___x_2116_, 9);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2128_ = v___x_2116_;
v_isShared_2129_ = v_isSharedCheck_2148_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_snapshotTasks_2126_);
lean_inc(v_infoState_2117_);
lean_inc(v_messages_2125_);
lean_inc(v_recordedDeps_2124_);
lean_inc(v_cache_2123_);
lean_inc(v_traceState_2122_);
lean_inc(v_auxDeclNGen_2121_);
lean_inc(v_ngen_2120_);
lean_inc(v_nextMacroScope_2119_);
lean_inc(v_env_2118_);
lean_dec(v___x_2116_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2148_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
uint8_t v_enabled_2130_; lean_object* v_assignment_2131_; lean_object* v_lazyAssignment_2132_; lean_object* v_trees_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2147_; 
v_enabled_2130_ = lean_ctor_get_uint8(v_infoState_2117_, sizeof(void*)*3);
v_assignment_2131_ = lean_ctor_get(v_infoState_2117_, 0);
v_lazyAssignment_2132_ = lean_ctor_get(v_infoState_2117_, 1);
v_trees_2133_ = lean_ctor_get(v_infoState_2117_, 2);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_infoState_2117_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2135_ = v_infoState_2117_;
v_isShared_2136_ = v_isSharedCheck_2147_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_trees_2133_);
lean_inc(v_lazyAssignment_2132_);
lean_inc(v_assignment_2131_);
lean_dec(v_infoState_2117_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2147_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2137_ = lean_box(0);
v___x_2138_ = l_Lean_PersistentArray_push___redArg(v_trees_2133_, v_t_2108_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 2, v___x_2138_);
v___x_2140_ = v___x_2135_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_assignment_2131_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_lazyAssignment_2132_);
lean_ctor_set(v_reuseFailAlloc_2146_, 2, v___x_2138_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*3, v_enabled_2130_);
v___x_2140_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2142_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 8, v___x_2140_);
v___x_2142_ = v___x_2128_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_env_2118_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_nextMacroScope_2119_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v_ngen_2120_);
lean_ctor_set(v_reuseFailAlloc_2145_, 3, v_auxDeclNGen_2121_);
lean_ctor_set(v_reuseFailAlloc_2145_, 4, v_traceState_2122_);
lean_ctor_set(v_reuseFailAlloc_2145_, 5, v_cache_2123_);
lean_ctor_set(v_reuseFailAlloc_2145_, 6, v_recordedDeps_2124_);
lean_ctor_set(v_reuseFailAlloc_2145_, 7, v_messages_2125_);
lean_ctor_set(v_reuseFailAlloc_2145_, 8, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2145_, 9, v_snapshotTasks_2126_);
v___x_2142_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = lean_st_ref_put(v___y_2109_, v___x_2142_);
v___x_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2137_);
return v___x_2144_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2149_, v___y_2150_);
lean_dec(v___y_2150_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object* v_t_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___x_2157_; lean_object* v_infoState_2158_; uint8_t v_enabled_2159_; 
v___x_2157_ = lean_st_ref_get(v___y_2155_);
v_infoState_2158_ = lean_ctor_get(v___x_2157_, 8);
lean_inc_ref(v_infoState_2158_);
lean_dec(v___x_2157_);
v_enabled_2159_ = lean_ctor_get_uint8(v_infoState_2158_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2158_);
if (v_enabled_2159_ == 0)
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
lean_dec_ref(v_t_2153_);
v___x_2160_ = lean_box(0);
v___x_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
return v___x_2161_;
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2162_ = lean_unsigned_to_nat(32u);
v___x_2163_ = lean_mk_empty_array_with_capacity(v___x_2162_);
lean_dec_ref(v___x_2163_);
v___x_2164_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2165_, 0, v_t_2153_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v___x_2165_, v___y_2155_);
return v___x_2166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object* v_t_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_2167_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
return v_res_2171_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
return v___x_2173_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2175_ = lean_unsigned_to_nat(0u);
v___x_2176_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
lean_ctor_set(v___x_2176_, 2, v___x_2175_);
lean_ctor_set(v___x_2176_, 3, v___x_2175_);
lean_ctor_set(v___x_2176_, 4, v___x_2174_);
lean_ctor_set(v___x_2176_, 5, v___x_2174_);
lean_ctor_set(v___x_2176_, 6, v___x_2174_);
lean_ctor_set(v___x_2176_, 7, v___x_2174_);
lean_ctor_set(v___x_2176_, 8, v___x_2174_);
lean_ctor_set(v___x_2176_, 9, v___x_2174_);
lean_ctor_set(v___x_2176_, 10, v___x_2174_);
return v___x_2176_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2177_ = lean_box(1);
v___x_2178_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_2179_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
lean_ctor_set(v___x_2180_, 1, v___x_2178_);
lean_ctor_set(v___x_2180_, 2, v___x_2177_);
return v___x_2180_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3));
v___x_2183_ = l_Lean_stringToMessageData(v___x_2182_);
return v___x_2183_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5));
v___x_2186_ = l_Lean_stringToMessageData(v___x_2185_);
return v___x_2186_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7));
v___x_2189_ = l_Lean_stringToMessageData(v___x_2188_);
return v___x_2189_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2191_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9));
v___x_2192_ = l_Lean_stringToMessageData(v___x_2191_);
return v___x_2192_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11));
v___x_2195_ = l_Lean_stringToMessageData(v___x_2194_);
return v___x_2195_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13));
v___x_2198_ = l_Lean_stringToMessageData(v___x_2197_);
return v___x_2198_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15));
v___x_2201_ = l_Lean_stringToMessageData(v___x_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_2202_, lean_object* v_declHint_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v_env_2208_; uint8_t v___x_2209_; 
v___x_2206_ = lean_box(0);
v___x_2207_ = lean_st_ref_get(v___y_2204_);
v_env_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc_ref(v_env_2208_);
lean_dec(v___x_2207_);
v___x_2209_ = l_Lean_Name_isAnonymous(v_declHint_2203_);
if (v___x_2209_ == 0)
{
uint8_t v_isExporting_2210_; 
v_isExporting_2210_ = lean_ctor_get_uint8(v_env_2208_, sizeof(void*)*8);
if (v_isExporting_2210_ == 0)
{
lean_object* v___x_2211_; 
lean_dec_ref(v_env_2208_);
lean_dec(v_declHint_2203_);
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v_msg_2202_);
return v___x_2211_;
}
else
{
lean_object* v___x_2212_; uint8_t v___x_2213_; 
lean_inc_ref(v_env_2208_);
v___x_2212_ = l_Lean_Environment_setExporting(v_env_2208_, v___x_2209_);
lean_inc(v_declHint_2203_);
lean_inc_ref(v___x_2212_);
v___x_2213_ = l_Lean_Environment_contains(v___x_2212_, v_declHint_2203_, v_isExporting_2210_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; 
lean_dec_ref(v___x_2212_);
lean_dec_ref(v_env_2208_);
lean_dec(v_declHint_2203_);
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v_msg_2202_);
return v___x_2214_;
}
else
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v_c_2220_; lean_object* v___x_2221_; 
v___x_2215_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2216_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_2217_ = l_Lean_Options_empty;
v___x_2218_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2212_);
lean_ctor_set(v___x_2218_, 1, v___x_2215_);
lean_ctor_set(v___x_2218_, 2, v___x_2216_);
lean_ctor_set(v___x_2218_, 3, v___x_2217_);
lean_inc(v_declHint_2203_);
v___x_2219_ = l_Lean_MessageData_ofConstName(v_declHint_2203_, v___x_2209_);
v_c_2220_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2220_, 0, v___x_2218_);
lean_ctor_set(v_c_2220_, 1, v___x_2219_);
v___x_2221_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2208_, v_declHint_2203_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_dec_ref(v_env_2208_);
lean_dec(v_declHint_2203_);
v___x_2222_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v_c_2220_);
v___x_2224_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6);
v___x_2225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2223_);
lean_ctor_set(v___x_2225_, 1, v___x_2224_);
v___x_2226_ = l_Lean_MessageData_note(v___x_2225_);
v___x_2227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2227_, 0, v_msg_2202_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
else
{
lean_object* v_val_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2263_; 
v_val_2229_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2231_ = v___x_2221_;
v_isShared_2232_ = v_isSharedCheck_2263_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_val_2229_);
lean_dec(v___x_2221_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2263_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v_mod_2235_; uint8_t v___x_2236_; 
v___x_2233_ = l_Lean_Environment_header(v_env_2208_);
lean_dec_ref(v_env_2208_);
v___x_2234_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2233_);
v_mod_2235_ = lean_array_get(v___x_2206_, v___x_2234_, v_val_2229_);
lean_dec(v_val_2229_);
lean_dec_ref(v___x_2234_);
v___x_2236_ = l_Lean_isPrivateName(v_declHint_2203_);
lean_dec(v_declHint_2203_);
if (v___x_2236_ == 0)
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2237_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8);
v___x_2238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
lean_ctor_set(v___x_2238_, 1, v_c_2220_);
v___x_2239_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10);
v___x_2240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2238_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = l_Lean_MessageData_ofName(v_mod_2235_);
v___x_2242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2240_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
v___x_2243_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12);
v___x_2244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2242_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = l_Lean_MessageData_note(v___x_2244_);
v___x_2246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2246_, 0, v_msg_2202_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set_tag(v___x_2231_, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2246_);
v___x_2248_ = v___x_2231_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
else
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2250_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
lean_ctor_set(v___x_2251_, 1, v_c_2220_);
v___x_2252_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14);
v___x_2253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2251_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = l_Lean_MessageData_ofName(v_mod_2235_);
v___x_2255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2253_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16);
v___x_2257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2255_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
v___x_2258_ = l_Lean_MessageData_note(v___x_2257_);
v___x_2259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2259_, 0, v_msg_2202_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set_tag(v___x_2231_, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2259_);
v___x_2261_ = v___x_2231_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2264_; 
lean_dec_ref(v_env_2208_);
lean_dec(v_declHint_2203_);
v___x_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2264_, 0, v_msg_2202_);
return v___x_2264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_2265_, lean_object* v_declHint_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2265_, v_declHint_2266_, v___y_2267_);
lean_dec(v___y_2267_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_2270_, lean_object* v_declHint_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v___x_2275_; lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2285_; 
v___x_2275_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2270_, v_declHint_2271_, v___y_2273_);
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2278_ = v___x_2275_;
v_isShared_2279_ = v_isSharedCheck_2285_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2275_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2285_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2280_ = l_Lean_unknownIdentifierMessageTag;
v___x_2281_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
lean_ctor_set(v___x_2281_, 1, v_a_2276_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 0, v___x_2281_);
v___x_2283_ = v___x_2278_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_2286_, lean_object* v_declHint_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2286_, v_declHint_2287_, v___y_2288_, v___y_2289_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object* v_msgData_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v___x_2296_; lean_object* v_toCold_2297_; lean_object* v_env_2298_; lean_object* v_options_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2296_ = lean_st_ref_get(v___y_2294_);
v_toCold_2297_ = lean_ctor_get(v___y_2293_, 0);
v_env_2298_ = lean_ctor_get(v___x_2296_, 0);
lean_inc_ref(v_env_2298_);
lean_dec(v___x_2296_);
v_options_2299_ = lean_ctor_get(v_toCold_2297_, 2);
v___x_2300_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2301_ = lean_unsigned_to_nat(32u);
v___x_2302_ = lean_mk_empty_array_with_capacity(v___x_2301_);
lean_dec_ref(v___x_2302_);
v___x_2303_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
lean_inc_ref(v_options_2299_);
v___x_2304_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2304_, 0, v_env_2298_);
lean_ctor_set(v___x_2304_, 1, v___x_2300_);
lean_ctor_set(v___x_2304_, 2, v___x_2303_);
lean_ctor_set(v___x_2304_, 3, v_options_2299_);
v___x_2305_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
lean_ctor_set(v___x_2305_, 1, v_msgData_2292_);
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object* v_msgData_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_ref_2316_; lean_object* v___x_2317_; lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2326_; 
v_ref_2316_ = lean_ctor_get(v___y_2313_, 2);
v___x_2317_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_2312_, v___y_2313_, v___y_2314_);
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2326_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2326_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; lean_object* v___x_2324_; 
lean_inc(v_ref_2316_);
v___x_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2322_, 0, v_ref_2316_);
lean_ctor_set(v___x_2322_, 1, v_a_2318_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set_tag(v___x_2320_, 1);
lean_ctor_set(v___x_2320_, 0, v___x_2322_);
v___x_2324_ = v___x_2320_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v___x_2322_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_2332_, lean_object* v_msg_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v_toCold_2337_; lean_object* v_currRecDepth_2338_; lean_object* v_ref_2339_; uint16_t v_optionFlags_2340_; uint8_t v_suppressElabErrors_2341_; uint8_t v_isRecordingDeps_2342_; lean_object* v_ref_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v_toCold_2337_ = lean_ctor_get(v___y_2334_, 0);
v_currRecDepth_2338_ = lean_ctor_get(v___y_2334_, 1);
v_ref_2339_ = lean_ctor_get(v___y_2334_, 2);
v_optionFlags_2340_ = lean_ctor_get_uint16(v___y_2334_, sizeof(void*)*3);
v_suppressElabErrors_2341_ = lean_ctor_get_uint8(v___y_2334_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2342_ = lean_ctor_get_uint8(v___y_2334_, sizeof(void*)*3 + 3);
v_ref_2343_ = l_Lean_replaceRef(v_ref_2332_, v_ref_2339_);
lean_inc(v_currRecDepth_2338_);
lean_inc_ref(v_toCold_2337_);
v___x_2344_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2344_, 0, v_toCold_2337_);
lean_ctor_set(v___x_2344_, 1, v_currRecDepth_2338_);
lean_ctor_set(v___x_2344_, 2, v_ref_2343_);
lean_ctor_set_uint16(v___x_2344_, sizeof(void*)*3, v_optionFlags_2340_);
lean_ctor_set_uint8(v___x_2344_, sizeof(void*)*3 + 2, v_suppressElabErrors_2341_);
lean_ctor_set_uint8(v___x_2344_, sizeof(void*)*3 + 3, v_isRecordingDeps_2342_);
v___x_2345_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2333_, v___x_2344_, v___y_2335_);
lean_dec_ref_known(v___x_2344_, 3);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_2346_, lean_object* v_msg_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2346_, v_msg_2347_, v___y_2348_, v___y_2349_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v_ref_2346_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_2352_, lean_object* v_msg_2353_, lean_object* v_declHint_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2358_; lean_object* v_a_2359_; lean_object* v___x_2360_; 
v___x_2358_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2353_, v_declHint_2354_, v___y_2355_, v___y_2356_);
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref(v___x_2358_);
v___x_2360_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2352_, v_a_2359_, v___y_2355_, v___y_2356_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2361_, lean_object* v_msg_2362_, lean_object* v_declHint_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2361_, v_msg_2362_, v_declHint_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v_ref_2361_);
return v_res_2367_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_2370_ = l_Lean_stringToMessageData(v___x_2369_);
return v___x_2370_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2));
v___x_2373_ = l_Lean_stringToMessageData(v___x_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_2374_, lean_object* v_constName_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v___x_2379_; uint8_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2379_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_2380_ = 0;
lean_inc(v_constName_2375_);
v___x_2381_ = l_Lean_MessageData_ofConstName(v_constName_2375_, v___x_2380_);
v___x_2382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2379_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_2384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2382_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
v___x_2385_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2374_, v___x_2384_, v_constName_2375_, v___y_2376_, v___y_2377_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2386_, lean_object* v_constName_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2386_, v_constName_2387_, v___y_2388_, v___y_2389_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v_ref_2386_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v_ref_2396_; lean_object* v___x_2397_; 
v_ref_2396_ = lean_ctor_get(v___y_2393_, 2);
v___x_2397_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2396_, v_constName_2392_, v___y_2393_, v___y_2394_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object* v_constName_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v___x_2407_; lean_object* v_env_2408_; uint8_t v___x_2409_; lean_object* v___x_2410_; 
v___x_2407_ = lean_st_ref_get(v___y_2405_);
v_env_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc_ref(v_env_2408_);
lean_dec(v___x_2407_);
v___x_2409_ = 0;
lean_inc(v_constName_2403_);
v___x_2410_ = l_Lean_Environment_findConstVal_x3f(v_env_2408_, v_constName_2403_, v___x_2409_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2403_, v___y_2404_, v___y_2405_);
return v___x_2411_;
}
else
{
lean_object* v_val_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec(v_constName_2403_);
v_val_2412_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2410_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_val_2412_);
lean_dec(v___x_2410_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
lean_ctor_set_tag(v___x_2414_, 0);
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_val_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object* v_a_2425_, lean_object* v_a_2426_){
_start:
{
if (lean_obj_tag(v_a_2425_) == 0)
{
lean_object* v___x_2427_; 
v___x_2427_ = l_List_reverse___redArg(v_a_2426_);
return v___x_2427_;
}
else
{
lean_object* v_head_2428_; lean_object* v_tail_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2438_; 
v_head_2428_ = lean_ctor_get(v_a_2425_, 0);
v_tail_2429_ = lean_ctor_get(v_a_2425_, 1);
v_isSharedCheck_2438_ = !lean_is_exclusive(v_a_2425_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2431_ = v_a_2425_;
v_isShared_2432_ = v_isSharedCheck_2438_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_tail_2429_);
lean_inc(v_head_2428_);
lean_dec(v_a_2425_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2438_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v___x_2435_; 
v___x_2433_ = l_Lean_mkLevelParam(v_head_2428_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 1, v_a_2426_);
lean_ctor_set(v___x_2431_, 0, v___x_2433_);
v___x_2435_ = v___x_2431_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2433_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_a_2426_);
v___x_2435_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
v_a_2425_ = v_tail_2429_;
v_a_2426_ = v___x_2435_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object* v_constName_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v___x_2443_; 
lean_inc(v_constName_2439_);
v___x_2443_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2439_, v___y_2440_, v___y_2441_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2455_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2455_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2455_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v_levelParams_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2453_; 
v_levelParams_2448_ = lean_ctor_get(v_a_2444_, 1);
lean_inc(v_levelParams_2448_);
lean_dec(v_a_2444_);
v___x_2449_ = lean_box(0);
v___x_2450_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_2448_, v___x_2449_);
v___x_2451_ = l_Lean_mkConst(v_constName_2439_, v___x_2450_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v___x_2451_);
v___x_2453_ = v___x_2446_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec(v_constName_2439_);
v_a_2456_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2443_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2443_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object* v_constName_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_2464_, v___y_2465_, v___y_2466_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object* v_stx_2469_, lean_object* v_n_2470_, lean_object* v_expectedType_x3f_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_2470_, v___y_2472_, v___y_2473_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref_known(v___x_2475_, 1);
v___x_2477_ = lean_box(0);
v___x_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2477_);
lean_ctor_set(v___x_2478_, 1, v_stx_2469_);
v___x_2479_ = l_Lean_LocalContext_empty;
v___x_2480_ = 0;
v___x_2481_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2481_, 0, v___x_2478_);
lean_ctor_set(v___x_2481_, 1, v___x_2479_);
lean_ctor_set(v___x_2481_, 2, v_expectedType_x3f_2471_);
lean_ctor_set(v___x_2481_, 3, v_a_2476_);
lean_ctor_set_uint8(v___x_2481_, sizeof(void*)*4, v___x_2480_);
lean_ctor_set_uint8(v___x_2481_, sizeof(void*)*4 + 1, v___x_2480_);
v___x_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
v___x_2483_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_2482_, v___y_2472_, v___y_2473_);
return v___x_2483_;
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec(v_expectedType_x3f_2471_);
lean_dec(v_stx_2469_);
v_a_2484_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2475_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2475_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object* v_stx_2492_, lean_object* v_n_2493_, lean_object* v_expectedType_x3f_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_2492_, v_n_2493_, v_expectedType_x3f_2494_, v___y_2495_, v___y_2496_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object* v_id_2499_, lean_object* v_expectedType_x3f_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_){
_start:
{
lean_object* v___x_2504_; 
lean_inc(v_id_2499_);
v___x_2504_ = l_Lean_realizeGlobalConstNoOverload(v_id_2499_, v_a_2501_, v_a_2502_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2532_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2507_ = v___x_2504_;
v_isShared_2508_ = v_isSharedCheck_2532_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2532_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2509_; lean_object* v_infoState_2510_; uint8_t v_enabled_2511_; 
v___x_2509_ = lean_st_ref_get(v_a_2502_);
v_infoState_2510_ = lean_ctor_get(v___x_2509_, 8);
lean_inc_ref(v_infoState_2510_);
lean_dec(v___x_2509_);
v_enabled_2511_ = lean_ctor_get_uint8(v_infoState_2510_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2510_);
if (v_enabled_2511_ == 0)
{
lean_object* v___x_2513_; 
lean_dec(v_expectedType_x3f_2500_);
lean_dec(v_id_2499_);
if (v_isShared_2508_ == 0)
{
v___x_2513_ = v___x_2507_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2505_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
else
{
lean_object* v___x_2515_; 
lean_del_object(v___x_2507_);
lean_inc(v_a_2505_);
v___x_2515_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2499_, v_a_2505_, v_expectedType_x3f_2500_, v_a_2501_, v_a_2502_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2522_ == 0)
{
lean_object* v_unused_2523_; 
v_unused_2523_ = lean_ctor_get(v___x_2515_, 0);
lean_dec(v_unused_2523_);
v___x_2517_ = v___x_2515_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_dec(v___x_2515_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 0, v_a_2505_);
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2505_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec(v_a_2505_);
v_a_2524_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2515_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2515_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2500_);
lean_dec(v_id_2499_);
return v___x_2504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object* v_id_2533_, lean_object* v_expectedType_x3f_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_2533_, v_expectedType_x3f_2534_, v_a_2535_, v_a_2536_);
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2535_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object* v_t_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2539_, v___y_2541_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2549_, lean_object* v_constName_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2550_, v___y_2551_, v___y_2552_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2555_, lean_object* v_constName_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2555_, v_constName_2556_, v___y_2557_, v___y_2558_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2561_, lean_object* v_ref_2562_, lean_object* v_constName_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2562_, v_constName_2563_, v___y_2564_, v___y_2565_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2568_, lean_object* v_ref_2569_, lean_object* v_constName_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_2568_, v_ref_2569_, v_constName_2570_, v___y_2571_, v___y_2572_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v_ref_2569_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2575_, lean_object* v_ref_2576_, lean_object* v_msg_2577_, lean_object* v_declHint_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2576_, v_msg_2577_, v_declHint_2578_, v___y_2579_, v___y_2580_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2583_, lean_object* v_ref_2584_, lean_object* v_msg_2585_, lean_object* v_declHint_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_2583_, v_ref_2584_, v_msg_2585_, v_declHint_2586_, v___y_2587_, v___y_2588_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v_ref_2584_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_2591_, lean_object* v_declHint_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v___x_2596_; 
v___x_2596_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2591_, v_declHint_2592_, v___y_2594_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2597_, lean_object* v_declHint_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2597_, v_declHint_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_2603_, lean_object* v_ref_2604_, lean_object* v_msg_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2604_, v_msg_2605_, v___y_2606_, v___y_2607_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2610_, lean_object* v_ref_2611_, lean_object* v_msg_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_2610_, v_ref_2611_, v_msg_2612_, v___y_2613_, v___y_2614_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v_ref_2611_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_2617_, lean_object* v_msg_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2618_, v___y_2619_, v___y_2620_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_2623_, lean_object* v_msg_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_2623_, v_msg_2624_, v___y_2625_, v___y_2626_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object* v_id_2629_, lean_object* v_expectedType_x3f_2630_, lean_object* v_as_x27_2631_, lean_object* v_b_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
if (lean_obj_tag(v_as_x27_2631_) == 0)
{
lean_object* v___x_2636_; 
lean_dec(v_expectedType_x3f_2630_);
lean_dec(v_id_2629_);
v___x_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2636_, 0, v_b_2632_);
return v___x_2636_;
}
else
{
lean_object* v_head_2637_; lean_object* v_tail_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v_head_2637_ = lean_ctor_get(v_as_x27_2631_, 0);
v_tail_2638_ = lean_ctor_get(v_as_x27_2631_, 1);
v___x_2639_ = lean_box(0);
lean_inc(v_expectedType_x3f_2630_);
lean_inc(v_head_2637_);
lean_inc(v_id_2629_);
v___x_2640_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2629_, v_head_2637_, v_expectedType_x3f_2630_, v___y_2633_, v___y_2634_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_dec_ref_known(v___x_2640_, 1);
v_as_x27_2631_ = v_tail_2638_;
v_b_2632_ = v___x_2639_;
goto _start;
}
else
{
lean_dec(v_expectedType_x3f_2630_);
lean_dec(v_id_2629_);
return v___x_2640_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object* v_id_2642_, lean_object* v_expectedType_x3f_2643_, lean_object* v_as_x27_2644_, lean_object* v_b_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2642_, v_expectedType_x3f_2643_, v_as_x27_2644_, v_b_2645_, v___y_2646_, v___y_2647_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v_as_x27_2644_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object* v_id_2650_, lean_object* v_expectedType_x3f_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v___x_2655_; 
lean_inc(v_id_2650_);
v___x_2655_ = l_Lean_realizeGlobalConst(v_id_2650_, v_a_2652_, v_a_2653_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2684_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2658_ = v___x_2655_;
v_isShared_2659_ = v_isSharedCheck_2684_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2655_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2684_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2660_; lean_object* v_infoState_2661_; uint8_t v_enabled_2662_; 
v___x_2660_ = lean_st_ref_get(v_a_2653_);
v_infoState_2661_ = lean_ctor_get(v___x_2660_, 8);
lean_inc_ref(v_infoState_2661_);
lean_dec(v___x_2660_);
v_enabled_2662_ = lean_ctor_get_uint8(v_infoState_2661_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2661_);
if (v_enabled_2662_ == 0)
{
lean_object* v___x_2664_; 
lean_dec(v_expectedType_x3f_2651_);
lean_dec(v_id_2650_);
if (v_isShared_2659_ == 0)
{
v___x_2664_ = v___x_2658_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2656_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
else
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
lean_del_object(v___x_2658_);
v___x_2666_ = lean_box(0);
v___x_2667_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2650_, v_expectedType_x3f_2651_, v_a_2656_, v___x_2666_, v_a_2652_, v_a_2653_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2674_ == 0)
{
lean_object* v_unused_2675_; 
v_unused_2675_ = lean_ctor_get(v___x_2667_, 0);
lean_dec(v_unused_2675_);
v___x_2669_ = v___x_2667_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_dec(v___x_2667_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v_a_2656_);
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2656_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec(v_a_2656_);
v_a_2676_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2667_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2667_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2651_);
lean_dec(v_id_2650_);
return v___x_2655_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object* v_id_2685_, lean_object* v_expectedType_x3f_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_2685_, v_expectedType_x3f_2686_, v_a_2687_, v_a_2688_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object* v_id_2691_, lean_object* v_expectedType_x3f_2692_, lean_object* v_as_2693_, lean_object* v_as_x27_2694_, lean_object* v_b_2695_, lean_object* v_a_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2691_, v_expectedType_x3f_2692_, v_as_x27_2694_, v_b_2695_, v___y_2697_, v___y_2698_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object* v_id_2701_, lean_object* v_expectedType_x3f_2702_, lean_object* v_as_2703_, lean_object* v_as_x27_2704_, lean_object* v_b_2705_, lean_object* v_a_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_2701_, v_expectedType_x3f_2702_, v_as_2703_, v_as_x27_2704_, v_b_2705_, v_a_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_as_x27_2704_);
lean_dec(v_as_2703_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object* v_ref_2711_, lean_object* v_as_x27_2712_, lean_object* v_b_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
if (lean_obj_tag(v_as_x27_2712_) == 0)
{
lean_object* v___x_2717_; 
lean_dec(v_ref_2711_);
v___x_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2717_, 0, v_b_2713_);
return v___x_2717_;
}
else
{
lean_object* v_head_2718_; lean_object* v_tail_2719_; lean_object* v_fst_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v_head_2718_ = lean_ctor_get(v_as_x27_2712_, 0);
v_tail_2719_ = lean_ctor_get(v_as_x27_2712_, 1);
v_fst_2720_ = lean_ctor_get(v_head_2718_, 0);
v___x_2721_ = lean_box(0);
v___x_2722_ = lean_box(0);
lean_inc(v_fst_2720_);
lean_inc(v_ref_2711_);
v___x_2723_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_2711_, v_fst_2720_, v___x_2722_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_dec_ref_known(v___x_2723_, 1);
v_as_x27_2712_ = v_tail_2719_;
v_b_2713_ = v___x_2721_;
goto _start;
}
else
{
lean_dec(v_ref_2711_);
return v___x_2723_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object* v_ref_2725_, lean_object* v_as_x27_2726_, lean_object* v_b_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2725_, v_as_x27_2726_, v_b_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v_as_x27_2726_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object* v_ref_2732_, lean_object* v_id_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_Lean_realizeGlobalName(v_id_2733_, v_a_2734_, v_a_2735_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2766_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2740_ = v___x_2737_;
v_isShared_2741_ = v_isSharedCheck_2766_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2737_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2766_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2742_; lean_object* v_infoState_2743_; uint8_t v_enabled_2744_; 
v___x_2742_ = lean_st_ref_get(v_a_2735_);
v_infoState_2743_ = lean_ctor_get(v___x_2742_, 8);
lean_inc_ref(v_infoState_2743_);
lean_dec(v___x_2742_);
v_enabled_2744_ = lean_ctor_get_uint8(v_infoState_2743_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2743_);
if (v_enabled_2744_ == 0)
{
lean_object* v___x_2746_; 
lean_dec(v_ref_2732_);
if (v_isShared_2741_ == 0)
{
v___x_2746_ = v___x_2740_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2738_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
else
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
lean_del_object(v___x_2740_);
v___x_2748_ = lean_box(0);
v___x_2749_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2732_, v_a_2738_, v___x_2748_, v_a_2734_, v_a_2735_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2756_ == 0)
{
lean_object* v_unused_2757_; 
v_unused_2757_ = lean_ctor_get(v___x_2749_, 0);
lean_dec(v_unused_2757_);
v___x_2751_ = v___x_2749_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_dec(v___x_2749_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 0, v_a_2738_);
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2738_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v_a_2738_);
v_a_2758_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2749_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2749_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
}
else
{
lean_dec(v_ref_2732_);
return v___x_2737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object* v_ref_2767_, lean_object* v_id_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_2767_, v_id_2768_, v_a_2769_, v_a_2770_);
lean_dec(v_a_2770_);
lean_dec_ref(v_a_2769_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object* v_ref_2773_, lean_object* v_as_2774_, lean_object* v_as_x27_2775_, lean_object* v_b_2776_, lean_object* v_a_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2773_, v_as_x27_2775_, v_b_2776_, v___y_2778_, v___y_2779_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object* v_ref_2782_, lean_object* v_as_2783_, lean_object* v_as_x27_2784_, lean_object* v_b_2785_, lean_object* v_a_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_2782_, v_as_2783_, v_as_x27_2784_, v_b_2785_, v_a_2786_, v___y_2787_, v___y_2788_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v_as_x27_2784_);
lean_dec(v_as_2783_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object* v_self_2791_){
_start:
{
lean_object* v_fst_2792_; 
v_fst_2792_ = lean_ctor_get(v_self_2791_, 0);
lean_inc(v_fst_2792_);
return v_fst_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object* v_self_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_2793_);
lean_dec_ref(v_self_2793_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object* v_info_2795_, lean_object* v_treesSaved_2796_, lean_object* v_s_2797_){
_start:
{
if (lean_obj_tag(v_info_2795_) == 0)
{
uint8_t v_enabled_2798_; lean_object* v_assignment_2799_; lean_object* v_lazyAssignment_2800_; lean_object* v_trees_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2811_; 
v_enabled_2798_ = lean_ctor_get_uint8(v_s_2797_, sizeof(void*)*3);
v_assignment_2799_ = lean_ctor_get(v_s_2797_, 0);
v_lazyAssignment_2800_ = lean_ctor_get(v_s_2797_, 1);
v_trees_2801_ = lean_ctor_get(v_s_2797_, 2);
v_isSharedCheck_2811_ = !lean_is_exclusive(v_s_2797_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2803_ = v_s_2797_;
v_isShared_2804_ = v_isSharedCheck_2811_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_trees_2801_);
lean_inc(v_lazyAssignment_2800_);
lean_inc(v_assignment_2799_);
lean_dec(v_s_2797_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2811_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v_val_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2809_; 
v_val_2805_ = lean_ctor_get(v_info_2795_, 0);
lean_inc(v_val_2805_);
lean_dec_ref_known(v_info_2795_, 1);
v___x_2806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2806_, 0, v_val_2805_);
lean_ctor_set(v___x_2806_, 1, v_trees_2801_);
v___x_2807_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2796_, v___x_2806_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 2, v___x_2807_);
v___x_2809_ = v___x_2803_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_assignment_2799_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v_lazyAssignment_2800_);
lean_ctor_set(v_reuseFailAlloc_2810_, 2, v___x_2807_);
lean_ctor_set_uint8(v_reuseFailAlloc_2810_, sizeof(void*)*3, v_enabled_2798_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
else
{
uint8_t v_enabled_2812_; lean_object* v_assignment_2813_; lean_object* v_lazyAssignment_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2830_; 
v_enabled_2812_ = lean_ctor_get_uint8(v_s_2797_, sizeof(void*)*3);
v_assignment_2813_ = lean_ctor_get(v_s_2797_, 0);
v_lazyAssignment_2814_ = lean_ctor_get(v_s_2797_, 1);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_s_2797_);
if (v_isSharedCheck_2830_ == 0)
{
lean_object* v_unused_2831_; 
v_unused_2831_ = lean_ctor_get(v_s_2797_, 2);
lean_dec(v_unused_2831_);
v___x_2816_ = v_s_2797_;
v_isShared_2817_ = v_isSharedCheck_2830_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_lazyAssignment_2814_);
lean_inc(v_assignment_2813_);
lean_dec(v_s_2797_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2830_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v_val_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2829_; 
v_val_2818_ = lean_ctor_get(v_info_2795_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v_info_2795_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2820_ = v_info_2795_;
v_isShared_2821_ = v_isSharedCheck_2829_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_val_2818_);
lean_dec(v_info_2795_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2829_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
lean_ctor_set_tag(v___x_2820_, 2);
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_val_2818_);
v___x_2823_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2824_; lean_object* v___x_2826_; 
v___x_2824_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2796_, v___x_2823_);
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 2, v___x_2824_);
v___x_2826_ = v___x_2816_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_assignment_2813_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_lazyAssignment_2814_);
lean_ctor_set(v_reuseFailAlloc_2827_, 2, v___x_2824_);
lean_ctor_set_uint8(v_reuseFailAlloc_2827_, sizeof(void*)*3, v_enabled_2812_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object* v_treesSaved_2832_, lean_object* v_modifyInfoState_2833_, lean_object* v_info_2834_){
_start:
{
lean_object* v___f_2835_; lean_object* v___x_2836_; 
v___f_2835_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2835_, 0, v_info_2834_);
lean_closure_set(v___f_2835_, 1, v_treesSaved_2832_);
v___x_2836_ = lean_apply_1(v_modifyInfoState_2833_, v___f_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object* v___f_2837_, lean_object* v_info_2838_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_apply_1(v___f_2837_, v_info_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object* v_toPure_2840_, lean_object* v_toBind_2841_, lean_object* v___f_2842_, lean_object* v_____do__lift_2843_){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2844_, 0, v_____do__lift_2843_);
v___x_2845_ = lean_apply_2(v_toPure_2840_, lean_box(0), v___x_2844_);
v___x_2846_ = lean_apply_4(v_toBind_2841_, lean_box(0), lean_box(0), v___x_2845_, v___f_2842_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object* v_toBind_2847_, lean_object* v_mkInfoOnError_2848_, lean_object* v___f_2849_, lean_object* v_mkInfo_2850_, lean_object* v___f_2851_, lean_object* v_a_x3f_2852_){
_start:
{
if (lean_obj_tag(v_a_x3f_2852_) == 0)
{
lean_object* v___x_2853_; 
lean_dec(v___f_2851_);
lean_dec(v_mkInfo_2850_);
v___x_2853_ = lean_apply_4(v_toBind_2847_, lean_box(0), lean_box(0), v_mkInfoOnError_2848_, v___f_2849_);
return v___x_2853_;
}
else
{
lean_object* v_val_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
lean_dec(v___f_2849_);
lean_dec(v_mkInfoOnError_2848_);
v_val_2854_ = lean_ctor_get(v_a_x3f_2852_, 0);
lean_inc(v_val_2854_);
lean_dec_ref_known(v_a_x3f_2852_, 1);
v___x_2855_ = lean_apply_1(v_mkInfo_2850_, v_val_2854_);
v___x_2856_ = lean_apply_4(v_toBind_2847_, lean_box(0), lean_box(0), v___x_2855_, v___f_2851_);
return v___x_2856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object* v_toFunctor_2857_, lean_object* v_modifyInfoState_2858_, lean_object* v_toPure_2859_, lean_object* v_toBind_2860_, lean_object* v_mkInfoOnError_2861_, lean_object* v_mkInfo_2862_, lean_object* v_inst_2863_, lean_object* v_x_2864_, lean_object* v___f_2865_, lean_object* v_treesSaved_2866_){
_start:
{
lean_object* v_map_2867_; lean_object* v___f_2868_; lean_object* v___f_2869_; lean_object* v___f_2870_; lean_object* v___f_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v_map_2867_ = lean_ctor_get(v_toFunctor_2857_, 0);
lean_inc(v_map_2867_);
lean_dec_ref(v_toFunctor_2857_);
v___f_2868_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2868_, 0, v_treesSaved_2866_);
lean_closure_set(v___f_2868_, 1, v_modifyInfoState_2858_);
v___f_2869_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2869_, 0, v___f_2868_);
lean_inc_ref(v___f_2869_);
lean_inc(v_toBind_2860_);
v___f_2870_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_2870_, 0, v_toPure_2859_);
lean_closure_set(v___f_2870_, 1, v_toBind_2860_);
lean_closure_set(v___f_2870_, 2, v___f_2869_);
v___f_2871_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__6), 6, 5);
lean_closure_set(v___f_2871_, 0, v_toBind_2860_);
lean_closure_set(v___f_2871_, 1, v_mkInfoOnError_2861_);
lean_closure_set(v___f_2871_, 2, v___f_2870_);
lean_closure_set(v___f_2871_, 3, v_mkInfo_2862_);
lean_closure_set(v___f_2871_, 4, v___f_2869_);
v___x_2872_ = lean_apply_4(v_inst_2863_, lean_box(0), lean_box(0), v_x_2864_, v___f_2871_);
v___x_2873_ = lean_apply_4(v_map_2867_, lean_box(0), lean_box(0), v___f_2865_, v___x_2872_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object* v_x_2874_, lean_object* v_inst_2875_, lean_object* v_inst_2876_, lean_object* v_toBind_2877_, lean_object* v___f_2878_, lean_object* v_____do__lift_2879_){
_start:
{
uint8_t v_enabled_2880_; 
v_enabled_2880_ = lean_ctor_get_uint8(v_____do__lift_2879_, sizeof(void*)*3);
if (v_enabled_2880_ == 0)
{
lean_dec(v___f_2878_);
lean_dec(v_toBind_2877_);
lean_dec_ref(v_inst_2876_);
lean_dec_ref(v_inst_2875_);
lean_inc(v_x_2874_);
return v_x_2874_;
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2875_, v_inst_2876_);
v___x_2882_ = lean_apply_4(v_toBind_2877_, lean_box(0), lean_box(0), v___x_2881_, v___f_2878_);
return v___x_2882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object* v_x_2883_, lean_object* v_inst_2884_, lean_object* v_inst_2885_, lean_object* v_toBind_2886_, lean_object* v___f_2887_, lean_object* v_____do__lift_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__7(v_x_2883_, v_inst_2884_, v_inst_2885_, v_toBind_2886_, v___f_2887_, v_____do__lift_2888_);
lean_dec_ref(v_____do__lift_2888_);
lean_dec(v_x_2883_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object* v_inst_2891_, lean_object* v_inst_2892_, lean_object* v_inst_2893_, lean_object* v_x_2894_, lean_object* v_mkInfo_2895_, lean_object* v_mkInfoOnError_2896_){
_start:
{
lean_object* v_toApplicative_2897_; lean_object* v_toBind_2898_; lean_object* v_getInfoState_2899_; lean_object* v_modifyInfoState_2900_; lean_object* v_toFunctor_2901_; lean_object* v_toPure_2902_; lean_object* v___f_2903_; lean_object* v___f_2904_; lean_object* v___f_2905_; lean_object* v___x_2906_; 
v_toApplicative_2897_ = lean_ctor_get(v_inst_2891_, 0);
v_toBind_2898_ = lean_ctor_get(v_inst_2891_, 1);
lean_inc_n(v_toBind_2898_, 3);
v_getInfoState_2899_ = lean_ctor_get(v_inst_2892_, 0);
lean_inc(v_getInfoState_2899_);
v_modifyInfoState_2900_ = lean_ctor_get(v_inst_2892_, 1);
v_toFunctor_2901_ = lean_ctor_get(v_toApplicative_2897_, 0);
v_toPure_2902_ = lean_ctor_get(v_toApplicative_2897_, 1);
v___f_2903_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2894_);
lean_inc(v_toPure_2902_);
lean_inc(v_modifyInfoState_2900_);
lean_inc_ref(v_toFunctor_2901_);
v___f_2904_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__5), 10, 9);
lean_closure_set(v___f_2904_, 0, v_toFunctor_2901_);
lean_closure_set(v___f_2904_, 1, v_modifyInfoState_2900_);
lean_closure_set(v___f_2904_, 2, v_toPure_2902_);
lean_closure_set(v___f_2904_, 3, v_toBind_2898_);
lean_closure_set(v___f_2904_, 4, v_mkInfoOnError_2896_);
lean_closure_set(v___f_2904_, 5, v_mkInfo_2895_);
lean_closure_set(v___f_2904_, 6, v_inst_2893_);
lean_closure_set(v___f_2904_, 7, v_x_2894_);
lean_closure_set(v___f_2904_, 8, v___f_2903_);
v___f_2905_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2905_, 0, v_x_2894_);
lean_closure_set(v___f_2905_, 1, v_inst_2891_);
lean_closure_set(v___f_2905_, 2, v_inst_2892_);
lean_closure_set(v___f_2905_, 3, v_toBind_2898_);
lean_closure_set(v___f_2905_, 4, v___f_2904_);
v___x_2906_ = lean_apply_4(v_toBind_2898_, lean_box(0), lean_box(0), v_getInfoState_2899_, v___f_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* v_m_2907_, lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v_00_u03b1_2910_, lean_object* v_inst_2911_, lean_object* v_x_2912_, lean_object* v_mkInfo_2913_, lean_object* v_mkInfoOnError_2914_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Lean_Elab_withInfoContext_x27___redArg(v_inst_2908_, v_inst_2909_, v_inst_2911_, v_x_2912_, v_mkInfo_2913_, v_mkInfoOnError_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object* v_treesSaved_2916_, lean_object* v_tree_2917_, lean_object* v_s_2918_){
_start:
{
uint8_t v_enabled_2919_; lean_object* v_assignment_2920_; lean_object* v_lazyAssignment_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2929_; 
v_enabled_2919_ = lean_ctor_get_uint8(v_s_2918_, sizeof(void*)*3);
v_assignment_2920_ = lean_ctor_get(v_s_2918_, 0);
v_lazyAssignment_2921_ = lean_ctor_get(v_s_2918_, 1);
v_isSharedCheck_2929_ = !lean_is_exclusive(v_s_2918_);
if (v_isSharedCheck_2929_ == 0)
{
lean_object* v_unused_2930_; 
v_unused_2930_ = lean_ctor_get(v_s_2918_, 2);
lean_dec(v_unused_2930_);
v___x_2923_ = v_s_2918_;
v_isShared_2924_ = v_isSharedCheck_2929_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_lazyAssignment_2921_);
lean_inc(v_assignment_2920_);
lean_dec(v_s_2918_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2929_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2925_; lean_object* v___x_2927_; 
v___x_2925_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2916_, v_tree_2917_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 2, v___x_2925_);
v___x_2927_ = v___x_2923_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_assignment_2920_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_lazyAssignment_2921_);
lean_ctor_set(v_reuseFailAlloc_2928_, 2, v___x_2925_);
lean_ctor_set_uint8(v_reuseFailAlloc_2928_, sizeof(void*)*3, v_enabled_2919_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object* v_treesSaved_2931_, lean_object* v_modifyInfoState_2932_, lean_object* v_tree_2933_){
_start:
{
lean_object* v___f_2934_; lean_object* v___x_2935_; 
v___f_2934_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2934_, 0, v_treesSaved_2931_);
lean_closure_set(v___f_2934_, 1, v_tree_2933_);
v___x_2935_ = lean_apply_1(v_modifyInfoState_2932_, v___f_2934_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object* v_mkInfoTree_2936_, lean_object* v_toBind_2937_, lean_object* v___f_2938_, lean_object* v_st_2939_){
_start:
{
lean_object* v_trees_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v_trees_2940_ = lean_ctor_get(v_st_2939_, 2);
lean_inc_ref(v_trees_2940_);
lean_dec_ref(v_st_2939_);
v___x_2941_ = lean_apply_1(v_mkInfoTree_2936_, v_trees_2940_);
v___x_2942_ = lean_apply_4(v_toBind_2937_, lean_box(0), lean_box(0), v___x_2941_, v___f_2938_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object* v_toBind_2943_, lean_object* v_getInfoState_2944_, lean_object* v___f_2945_, lean_object* v_x_2946_){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = lean_apply_4(v_toBind_2943_, lean_box(0), lean_box(0), v_getInfoState_2944_, v___f_2945_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object* v_toBind_2948_, lean_object* v_getInfoState_2949_, lean_object* v___f_2950_, lean_object* v_x_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(v_toBind_2948_, v_getInfoState_2949_, v___f_2950_, v_x_2951_);
lean_dec(v_x_2951_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object* v_toFunctor_2953_, lean_object* v_modifyInfoState_2954_, lean_object* v_mkInfoTree_2955_, lean_object* v_toBind_2956_, lean_object* v_getInfoState_2957_, lean_object* v_inst_2958_, lean_object* v_x_2959_, lean_object* v___f_2960_, lean_object* v_treesSaved_2961_){
_start:
{
lean_object* v_map_2962_; lean_object* v___f_2963_; lean_object* v___f_2964_; lean_object* v___f_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_map_2962_ = lean_ctor_get(v_toFunctor_2953_, 0);
lean_inc(v_map_2962_);
lean_dec_ref(v_toFunctor_2953_);
v___f_2963_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2963_, 0, v_treesSaved_2961_);
lean_closure_set(v___f_2963_, 1, v_modifyInfoState_2954_);
lean_inc(v_toBind_2956_);
v___f_2964_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2964_, 0, v_mkInfoTree_2955_);
lean_closure_set(v___f_2964_, 1, v_toBind_2956_);
lean_closure_set(v___f_2964_, 2, v___f_2963_);
v___f_2965_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_2965_, 0, v_toBind_2956_);
lean_closure_set(v___f_2965_, 1, v_getInfoState_2957_);
lean_closure_set(v___f_2965_, 2, v___f_2964_);
v___x_2966_ = lean_apply_4(v_inst_2958_, lean_box(0), lean_box(0), v_x_2959_, v___f_2965_);
v___x_2967_ = lean_apply_4(v_map_2962_, lean_box(0), lean_box(0), v___f_2960_, v___x_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object* v_inst_2968_, lean_object* v_inst_2969_, lean_object* v_inst_2970_, lean_object* v_x_2971_, lean_object* v_mkInfoTree_2972_){
_start:
{
lean_object* v_toApplicative_2973_; lean_object* v_toBind_2974_; lean_object* v_getInfoState_2975_; lean_object* v_modifyInfoState_2976_; lean_object* v_toFunctor_2977_; lean_object* v___f_2978_; lean_object* v___f_2979_; lean_object* v___f_2980_; lean_object* v___x_2981_; 
v_toApplicative_2973_ = lean_ctor_get(v_inst_2968_, 0);
v_toBind_2974_ = lean_ctor_get(v_inst_2968_, 1);
lean_inc_n(v_toBind_2974_, 3);
v_getInfoState_2975_ = lean_ctor_get(v_inst_2969_, 0);
lean_inc_n(v_getInfoState_2975_, 2);
v_modifyInfoState_2976_ = lean_ctor_get(v_inst_2969_, 1);
v_toFunctor_2977_ = lean_ctor_get(v_toApplicative_2973_, 0);
v___f_2978_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2971_);
lean_inc(v_modifyInfoState_2976_);
lean_inc_ref(v_toFunctor_2977_);
v___f_2979_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2979_, 0, v_toFunctor_2977_);
lean_closure_set(v___f_2979_, 1, v_modifyInfoState_2976_);
lean_closure_set(v___f_2979_, 2, v_mkInfoTree_2972_);
lean_closure_set(v___f_2979_, 3, v_toBind_2974_);
lean_closure_set(v___f_2979_, 4, v_getInfoState_2975_);
lean_closure_set(v___f_2979_, 5, v_inst_2970_);
lean_closure_set(v___f_2979_, 6, v_x_2971_);
lean_closure_set(v___f_2979_, 7, v___f_2978_);
v___f_2980_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2980_, 0, v_x_2971_);
lean_closure_set(v___f_2980_, 1, v_inst_2968_);
lean_closure_set(v___f_2980_, 2, v_inst_2969_);
lean_closure_set(v___f_2980_, 3, v_toBind_2974_);
lean_closure_set(v___f_2980_, 4, v___f_2979_);
v___x_2981_ = lean_apply_4(v_toBind_2974_, lean_box(0), lean_box(0), v_getInfoState_2975_, v___f_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object* v_m_2982_, lean_object* v_inst_2983_, lean_object* v_inst_2984_, lean_object* v_00_u03b1_2985_, lean_object* v_inst_2986_, lean_object* v_x_2987_, lean_object* v_mkInfoTree_2988_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_2983_, v_inst_2984_, v_inst_2986_, v_x_2987_, v_mkInfoTree_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object* v_trees_2990_, lean_object* v_toPure_2991_, lean_object* v_____do__lift_2992_){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2993_, 0, v_____do__lift_2992_);
lean_ctor_set(v___x_2993_, 1, v_trees_2990_);
v___x_2994_ = lean_apply_2(v_toPure_2991_, lean_box(0), v___x_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object* v_toPure_2995_, lean_object* v_toBind_2996_, lean_object* v_mkInfo_2997_, lean_object* v_trees_2998_){
_start:
{
lean_object* v___f_2999_; lean_object* v___x_3000_; 
v___f_2999_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2999_, 0, v_trees_2998_);
lean_closure_set(v___f_2999_, 1, v_toPure_2995_);
v___x_3000_ = lean_apply_4(v_toBind_2996_, lean_box(0), lean_box(0), v_mkInfo_2997_, v___f_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object* v_inst_3001_, lean_object* v_inst_3002_, lean_object* v_inst_3003_, lean_object* v_x_3004_, lean_object* v_mkInfo_3005_){
_start:
{
lean_object* v_toApplicative_3006_; lean_object* v_toBind_3007_; lean_object* v_toPure_3008_; lean_object* v___f_3009_; lean_object* v___x_3010_; 
v_toApplicative_3006_ = lean_ctor_get(v_inst_3001_, 0);
v_toBind_3007_ = lean_ctor_get(v_inst_3001_, 1);
v_toPure_3008_ = lean_ctor_get(v_toApplicative_3006_, 1);
lean_inc(v_toBind_3007_);
lean_inc(v_toPure_3008_);
v___f_3009_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3009_, 0, v_toPure_3008_);
lean_closure_set(v___f_3009_, 1, v_toBind_3007_);
lean_closure_set(v___f_3009_, 2, v_mkInfo_3005_);
v___x_3010_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3001_, v_inst_3002_, v_inst_3003_, v_x_3004_, v___f_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object* v_m_3011_, lean_object* v_inst_3012_, lean_object* v_inst_3013_, lean_object* v_00_u03b1_3014_, lean_object* v_inst_3015_, lean_object* v_x_3016_, lean_object* v_mkInfo_3017_){
_start:
{
lean_object* v_toApplicative_3018_; lean_object* v_toBind_3019_; lean_object* v_toPure_3020_; lean_object* v___f_3021_; lean_object* v___x_3022_; 
v_toApplicative_3018_ = lean_ctor_get(v_inst_3012_, 0);
v_toBind_3019_ = lean_ctor_get(v_inst_3012_, 1);
v_toPure_3020_ = lean_ctor_get(v_toApplicative_3018_, 1);
lean_inc(v_toBind_3019_);
lean_inc(v_toPure_3020_);
v___f_3021_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3021_, 0, v_toPure_3020_);
lean_closure_set(v___f_3021_, 1, v_toBind_3019_);
lean_closure_set(v___f_3021_, 2, v_mkInfo_3017_);
v___x_3022_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3012_, v_inst_3013_, v_inst_3015_, v_x_3016_, v___f_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object* v_treesSaved_3023_, lean_object* v_trees_3024_, lean_object* v_s_3025_){
_start:
{
uint8_t v_enabled_3026_; lean_object* v_assignment_3027_; lean_object* v_lazyAssignment_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3036_; 
v_enabled_3026_ = lean_ctor_get_uint8(v_s_3025_, sizeof(void*)*3);
v_assignment_3027_ = lean_ctor_get(v_s_3025_, 0);
v_lazyAssignment_3028_ = lean_ctor_get(v_s_3025_, 1);
v_isSharedCheck_3036_ = !lean_is_exclusive(v_s_3025_);
if (v_isSharedCheck_3036_ == 0)
{
lean_object* v_unused_3037_; 
v_unused_3037_ = lean_ctor_get(v_s_3025_, 2);
lean_dec(v_unused_3037_);
v___x_3030_ = v_s_3025_;
v_isShared_3031_ = v_isSharedCheck_3036_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_lazyAssignment_3028_);
lean_inc(v_assignment_3027_);
lean_dec(v_s_3025_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3036_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; lean_object* v___x_3034_; 
v___x_3032_ = l_Lean_PersistentArray_append___redArg(v_treesSaved_3023_, v_trees_3024_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 2, v___x_3032_);
v___x_3034_ = v___x_3030_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_assignment_3027_);
lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_lazyAssignment_3028_);
lean_ctor_set(v_reuseFailAlloc_3035_, 2, v___x_3032_);
lean_ctor_set_uint8(v_reuseFailAlloc_3035_, sizeof(void*)*3, v_enabled_3026_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object* v_treesSaved_3038_, lean_object* v_trees_3039_, lean_object* v_s_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_3038_, v_trees_3039_, v_s_3040_);
lean_dec_ref(v_trees_3039_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object* v_treesSaved_3042_, lean_object* v_modifyInfoState_3043_, lean_object* v_trees_3044_){
_start:
{
lean_object* v___f_3045_; lean_object* v___x_3046_; 
v___f_3045_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3045_, 0, v_treesSaved_3042_);
lean_closure_set(v___f_3045_, 1, v_trees_3044_);
v___x_3046_ = lean_apply_1(v_modifyInfoState_3043_, v___f_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object* v_toPure_3047_, lean_object* v_tree_3048_, lean_object* v_____do__lift_3049_){
_start:
{
if (lean_obj_tag(v_____do__lift_3049_) == 0)
{
lean_object* v___x_3050_; 
v___x_3050_ = lean_apply_2(v_toPure_3047_, lean_box(0), v_tree_3048_);
return v___x_3050_;
}
else
{
lean_object* v_val_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v_val_3051_ = lean_ctor_get(v_____do__lift_3049_, 0);
lean_inc(v_val_3051_);
v___x_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3052_, 0, v_val_3051_);
lean_ctor_set(v___x_3052_, 1, v_tree_3048_);
v___x_3053_ = lean_apply_2(v_toPure_3047_, lean_box(0), v___x_3052_);
return v___x_3053_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object* v_toPure_3054_, lean_object* v_tree_3055_, lean_object* v_____do__lift_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_3054_, v_tree_3055_, v_____do__lift_3056_);
lean_dec(v_____do__lift_3056_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object* v_assignment_3058_, lean_object* v_toPure_3059_, lean_object* v_toBind_3060_, lean_object* v_ctx_x3f_3061_, lean_object* v_tree_3062_){
_start:
{
lean_object* v_tree_3063_; lean_object* v___f_3064_; lean_object* v___x_3065_; 
v_tree_3063_ = l_Lean_Elab_InfoTree_substitute(v_tree_3062_, v_assignment_3058_);
v___f_3064_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3064_, 0, v_toPure_3059_);
lean_closure_set(v___f_3064_, 1, v_tree_3063_);
v___x_3065_ = lean_apply_4(v_toBind_3060_, lean_box(0), lean_box(0), v_ctx_x3f_3061_, v___f_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object* v_assignment_3066_, lean_object* v_toPure_3067_, lean_object* v_toBind_3068_, lean_object* v_ctx_x3f_3069_, lean_object* v_tree_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(v_assignment_3066_, v_toPure_3067_, v_toBind_3068_, v_ctx_x3f_3069_, v_tree_3070_);
lean_dec_ref(v_assignment_3066_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object* v_toPure_3072_, lean_object* v_toBind_3073_, lean_object* v_ctx_x3f_3074_, lean_object* v_inst_3075_, lean_object* v___f_3076_, lean_object* v_st_3077_){
_start:
{
lean_object* v_assignment_3078_; lean_object* v_trees_3079_; lean_object* v___f_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v_assignment_3078_ = lean_ctor_get(v_st_3077_, 0);
lean_inc_ref(v_assignment_3078_);
v_trees_3079_ = lean_ctor_get(v_st_3077_, 2);
lean_inc_ref(v_trees_3079_);
lean_dec_ref(v_st_3077_);
lean_inc(v_toBind_3073_);
v___f_3080_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_3080_, 0, v_assignment_3078_);
lean_closure_set(v___f_3080_, 1, v_toPure_3072_);
lean_closure_set(v___f_3080_, 2, v_toBind_3073_);
lean_closure_set(v___f_3080_, 3, v_ctx_x3f_3074_);
v___x_3081_ = l_Lean_PersistentArray_mapM___redArg(v_inst_3075_, v___f_3080_, v_trees_3079_);
v___x_3082_ = lean_apply_4(v_toBind_3073_, lean_box(0), lean_box(0), v___x_3081_, v___f_3076_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object* v_toFunctor_3083_, lean_object* v_modifyInfoState_3084_, lean_object* v_toPure_3085_, lean_object* v_toBind_3086_, lean_object* v_ctx_x3f_3087_, lean_object* v_inst_3088_, lean_object* v_getInfoState_3089_, lean_object* v_inst_3090_, lean_object* v_x_3091_, lean_object* v___f_3092_, lean_object* v_treesSaved_3093_){
_start:
{
lean_object* v_map_3094_; lean_object* v___f_3095_; lean_object* v___f_3096_; lean_object* v___f_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v_map_3094_ = lean_ctor_get(v_toFunctor_3083_, 0);
lean_inc(v_map_3094_);
lean_dec_ref(v_toFunctor_3083_);
v___f_3095_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3095_, 0, v_treesSaved_3093_);
lean_closure_set(v___f_3095_, 1, v_modifyInfoState_3084_);
lean_inc(v_toBind_3086_);
v___f_3096_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4), 6, 5);
lean_closure_set(v___f_3096_, 0, v_toPure_3085_);
lean_closure_set(v___f_3096_, 1, v_toBind_3086_);
lean_closure_set(v___f_3096_, 2, v_ctx_x3f_3087_);
lean_closure_set(v___f_3096_, 3, v_inst_3088_);
lean_closure_set(v___f_3096_, 4, v___f_3095_);
v___f_3097_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3097_, 0, v_toBind_3086_);
lean_closure_set(v___f_3097_, 1, v_getInfoState_3089_);
lean_closure_set(v___f_3097_, 2, v___f_3096_);
v___x_3098_ = lean_apply_4(v_inst_3090_, lean_box(0), lean_box(0), v_x_3091_, v___f_3097_);
v___x_3099_ = lean_apply_4(v_map_3094_, lean_box(0), lean_box(0), v___f_3092_, v___x_3098_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object* v_inst_3100_, lean_object* v_inst_3101_, lean_object* v_inst_3102_, lean_object* v_x_3103_, lean_object* v_ctx_x3f_3104_){
_start:
{
lean_object* v_toApplicative_3105_; lean_object* v_toBind_3106_; lean_object* v_getInfoState_3107_; lean_object* v_modifyInfoState_3108_; lean_object* v_toFunctor_3109_; lean_object* v_toPure_3110_; lean_object* v___f_3111_; lean_object* v___f_3112_; lean_object* v___f_3113_; lean_object* v___x_3114_; 
v_toApplicative_3105_ = lean_ctor_get(v_inst_3100_, 0);
v_toBind_3106_ = lean_ctor_get(v_inst_3100_, 1);
lean_inc_n(v_toBind_3106_, 3);
v_getInfoState_3107_ = lean_ctor_get(v_inst_3101_, 0);
lean_inc_n(v_getInfoState_3107_, 2);
v_modifyInfoState_3108_ = lean_ctor_get(v_inst_3101_, 1);
v_toFunctor_3109_ = lean_ctor_get(v_toApplicative_3105_, 0);
v_toPure_3110_ = lean_ctor_get(v_toApplicative_3105_, 1);
v___f_3111_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3103_);
lean_inc_ref(v_inst_3100_);
lean_inc(v_toPure_3110_);
lean_inc(v_modifyInfoState_3108_);
lean_inc_ref(v_toFunctor_3109_);
v___f_3112_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6), 11, 10);
lean_closure_set(v___f_3112_, 0, v_toFunctor_3109_);
lean_closure_set(v___f_3112_, 1, v_modifyInfoState_3108_);
lean_closure_set(v___f_3112_, 2, v_toPure_3110_);
lean_closure_set(v___f_3112_, 3, v_toBind_3106_);
lean_closure_set(v___f_3112_, 4, v_ctx_x3f_3104_);
lean_closure_set(v___f_3112_, 5, v_inst_3100_);
lean_closure_set(v___f_3112_, 6, v_getInfoState_3107_);
lean_closure_set(v___f_3112_, 7, v_inst_3102_);
lean_closure_set(v___f_3112_, 8, v_x_3103_);
lean_closure_set(v___f_3112_, 9, v___f_3111_);
v___f_3113_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3113_, 0, v_x_3103_);
lean_closure_set(v___f_3113_, 1, v_inst_3100_);
lean_closure_set(v___f_3113_, 2, v_inst_3101_);
lean_closure_set(v___f_3113_, 3, v_toBind_3106_);
lean_closure_set(v___f_3113_, 4, v___f_3112_);
v___x_3114_ = lean_apply_4(v_toBind_3106_, lean_box(0), lean_box(0), v_getInfoState_3107_, v___f_3113_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object* v_m_3115_, lean_object* v_inst_3116_, lean_object* v_inst_3117_, lean_object* v_00_u03b1_3118_, lean_object* v_inst_3119_, lean_object* v_x_3120_, lean_object* v_ctx_x3f_3121_){
_start:
{
lean_object* v___x_3122_; 
v___x_3122_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3116_, v_inst_3117_, v_inst_3119_, v_x_3120_, v_ctx_x3f_3121_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object* v_toPure_3123_, lean_object* v_____do__lift_3124_){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3125_, 0, v_____do__lift_3124_);
v___x_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
v___x_3127_ = lean_apply_2(v_toPure_3123_, lean_box(0), v___x_3126_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object* v_inst_3128_, lean_object* v_inst_3129_, lean_object* v_inst_3130_, lean_object* v_inst_3131_, lean_object* v_inst_3132_, lean_object* v_inst_3133_, lean_object* v_inst_3134_, lean_object* v_inst_3135_, lean_object* v_inst_3136_, lean_object* v_x_3137_){
_start:
{
lean_object* v_toApplicative_3138_; lean_object* v_toBind_3139_; lean_object* v_toPure_3140_; lean_object* v___x_3141_; lean_object* v___f_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v_toApplicative_3138_ = lean_ctor_get(v_inst_3128_, 0);
v_toBind_3139_ = lean_ctor_get(v_inst_3128_, 1);
v_toPure_3140_ = lean_ctor_get(v_toApplicative_3138_, 1);
lean_inc_ref(v_inst_3128_);
v___x_3141_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_3128_, v_inst_3132_, v_inst_3134_, v_inst_3133_, v_inst_3135_, v_inst_3130_, v_inst_3136_);
lean_inc(v_toPure_3140_);
v___f_3142_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3142_, 0, v_toPure_3140_);
lean_inc(v_toBind_3139_);
v___x_3143_ = lean_apply_4(v_toBind_3139_, lean_box(0), lean_box(0), v___x_3141_, v___f_3142_);
v___x_3144_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3128_, v_inst_3129_, v_inst_3131_, v_x_3137_, v___x_3143_);
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object* v_m_3145_, lean_object* v_inst_3146_, lean_object* v_inst_3147_, lean_object* v_00_u03b1_3148_, lean_object* v_inst_3149_, lean_object* v_inst_3150_, lean_object* v_inst_3151_, lean_object* v_inst_3152_, lean_object* v_inst_3153_, lean_object* v_inst_3154_, lean_object* v_inst_3155_, lean_object* v_x_3156_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = l_Lean_Elab_withSaveInfoContext___redArg(v_inst_3146_, v_inst_3147_, v_inst_3149_, v_inst_3150_, v_inst_3151_, v_inst_3152_, v_inst_3153_, v_inst_3154_, v_inst_3155_, v_x_3156_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object* v_toPure_3158_, lean_object* v_____x_3159_){
_start:
{
if (lean_obj_tag(v_____x_3159_) == 1)
{
lean_object* v_val_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3169_; 
v_val_3160_ = lean_ctor_get(v_____x_3159_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v_____x_3159_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3162_ = v_____x_3159_;
v_isShared_3163_ = v_isSharedCheck_3169_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_val_3160_);
lean_dec(v_____x_3159_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3169_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3164_; lean_object* v___x_3166_; 
v___x_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3164_, 0, v_val_3160_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 0, v___x_3164_);
v___x_3166_ = v___x_3162_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3164_);
v___x_3166_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
lean_object* v___x_3167_; 
v___x_3167_ = lean_apply_2(v_toPure_3158_, lean_box(0), v___x_3166_);
return v___x_3167_;
}
}
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
lean_dec(v_____x_3159_);
v___x_3170_ = lean_box(0);
v___x_3171_ = lean_apply_2(v_toPure_3158_, lean_box(0), v___x_3170_);
return v___x_3171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object* v_inst_3172_, lean_object* v_inst_3173_, lean_object* v_inst_3174_, lean_object* v_inst_3175_, lean_object* v_x_3176_){
_start:
{
lean_object* v_toApplicative_3177_; lean_object* v_toBind_3178_; lean_object* v_toPure_3179_; lean_object* v___f_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v_toApplicative_3177_ = lean_ctor_get(v_inst_3172_, 0);
v_toBind_3178_ = lean_ctor_get(v_inst_3172_, 1);
v_toPure_3179_ = lean_ctor_get(v_toApplicative_3177_, 1);
lean_inc(v_toPure_3179_);
v___f_3180_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3180_, 0, v_toPure_3179_);
lean_inc(v_toBind_3178_);
v___x_3181_ = lean_apply_4(v_toBind_3178_, lean_box(0), lean_box(0), v_inst_3175_, v___f_3180_);
v___x_3182_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3172_, v_inst_3173_, v_inst_3174_, v_x_3176_, v___x_3181_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object* v_m_3183_, lean_object* v_inst_3184_, lean_object* v_inst_3185_, lean_object* v_00_u03b1_3186_, lean_object* v_inst_3187_, lean_object* v_inst_3188_, lean_object* v_x_3189_){
_start:
{
lean_object* v___x_3190_; 
v___x_3190_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(v_inst_3184_, v_inst_3185_, v_inst_3187_, v_inst_3188_, v_x_3189_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object* v_toPure_3191_, lean_object* v_autoImplicits_3192_){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3193_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3193_, 0, v_autoImplicits_3192_);
v___x_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3193_);
v___x_3195_ = lean_apply_2(v_toPure_3191_, lean_box(0), v___x_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object* v_inst_3196_, lean_object* v_inst_3197_, lean_object* v_inst_3198_, lean_object* v_inst_3199_, lean_object* v_x_3200_){
_start:
{
lean_object* v_toApplicative_3201_; lean_object* v_toBind_3202_; lean_object* v_toPure_3203_; lean_object* v___f_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v_toApplicative_3201_ = lean_ctor_get(v_inst_3196_, 0);
v_toBind_3202_ = lean_ctor_get(v_inst_3196_, 1);
v_toPure_3203_ = lean_ctor_get(v_toApplicative_3201_, 1);
lean_inc(v_toPure_3203_);
v___f_3204_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3204_, 0, v_toPure_3203_);
lean_inc(v_toBind_3202_);
v___x_3205_ = lean_apply_4(v_toBind_3202_, lean_box(0), lean_box(0), v_inst_3199_, v___f_3204_);
v___x_3206_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3196_, v_inst_3197_, v_inst_3198_, v_x_3200_, v___x_3205_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object* v_m_3207_, lean_object* v_inst_3208_, lean_object* v_inst_3209_, lean_object* v_00_u03b1_3210_, lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_x_3213_){
_start:
{
lean_object* v___x_3214_; 
v___x_3214_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(v_inst_3208_, v_inst_3209_, v_inst_3211_, v_inst_3212_, v_x_3213_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object* v___x_3215_, lean_object* v___x_3216_, lean_object* v_mvarId_3217_, lean_object* v_toPure_3218_, lean_object* v_____do__lift_3219_){
_start:
{
lean_object* v_assignment_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v_assignment_3220_ = lean_ctor_get(v_____do__lift_3219_, 0);
v___x_3221_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_3215_, v___x_3216_, v_assignment_3220_, v_mvarId_3217_);
v___x_3222_ = lean_apply_2(v_toPure_3218_, lean_box(0), v___x_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object* v___x_3223_, lean_object* v___x_3224_, lean_object* v_mvarId_3225_, lean_object* v_toPure_3226_, lean_object* v_____do__lift_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(v___x_3223_, v___x_3224_, v_mvarId_3225_, v_toPure_3226_, v_____do__lift_3227_);
lean_dec_ref(v_____do__lift_3227_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object* v_inst_3231_, lean_object* v_inst_3232_, lean_object* v_mvarId_3233_){
_start:
{
lean_object* v_toApplicative_3234_; lean_object* v_toBind_3235_; lean_object* v_getInfoState_3236_; lean_object* v_toPure_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___f_3240_; lean_object* v___x_3241_; 
v_toApplicative_3234_ = lean_ctor_get(v_inst_3231_, 0);
lean_inc_ref(v_toApplicative_3234_);
v_toBind_3235_ = lean_ctor_get(v_inst_3231_, 1);
lean_inc(v_toBind_3235_);
lean_dec_ref(v_inst_3231_);
v_getInfoState_3236_ = lean_ctor_get(v_inst_3232_, 0);
lean_inc(v_getInfoState_3236_);
lean_dec_ref(v_inst_3232_);
v_toPure_3237_ = lean_ctor_get(v_toApplicative_3234_, 1);
lean_inc(v_toPure_3237_);
lean_dec_ref(v_toApplicative_3234_);
v___x_3238_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3239_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___f_3240_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3240_, 0, v___x_3238_);
lean_closure_set(v___f_3240_, 1, v___x_3239_);
lean_closure_set(v___f_3240_, 2, v_mvarId_3233_);
lean_closure_set(v___f_3240_, 3, v_toPure_3237_);
v___x_3241_ = lean_apply_4(v_toBind_3235_, lean_box(0), lean_box(0), v_getInfoState_3236_, v___f_3240_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* v_m_3242_, lean_object* v_inst_3243_, lean_object* v_inst_3244_, lean_object* v_mvarId_3245_){
_start:
{
lean_object* v___x_3246_; 
v___x_3246_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3243_, v_inst_3244_, v_mvarId_3245_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object* v___x_3247_, lean_object* v___x_3248_, lean_object* v_mvarId_3249_, lean_object* v_infoTree_3250_, lean_object* v_s_3251_){
_start:
{
uint8_t v_enabled_3252_; lean_object* v_assignment_3253_; lean_object* v_lazyAssignment_3254_; lean_object* v_trees_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3263_; 
v_enabled_3252_ = lean_ctor_get_uint8(v_s_3251_, sizeof(void*)*3);
v_assignment_3253_ = lean_ctor_get(v_s_3251_, 0);
v_lazyAssignment_3254_ = lean_ctor_get(v_s_3251_, 1);
v_trees_3255_ = lean_ctor_get(v_s_3251_, 2);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_s_3251_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3257_ = v_s_3251_;
v_isShared_3258_ = v_isSharedCheck_3263_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_trees_3255_);
lean_inc(v_lazyAssignment_3254_);
lean_inc(v_assignment_3253_);
lean_dec(v_s_3251_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3263_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3259_; lean_object* v___x_3261_; 
v___x_3259_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3247_, v___x_3248_, v_assignment_3253_, v_mvarId_3249_, v_infoTree_3250_);
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 0, v___x_3259_);
v___x_3261_ = v___x_3257_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3259_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v_lazyAssignment_3254_);
lean_ctor_set(v_reuseFailAlloc_3262_, 2, v_trees_3255_);
lean_ctor_set_uint8(v_reuseFailAlloc_3262_, sizeof(void*)*3, v_enabled_3252_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3267_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2));
v___x_3268_ = lean_unsigned_to_nat(2u);
v___x_3269_ = lean_unsigned_to_nat(384u);
v___x_3270_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1));
v___x_3271_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0));
v___x_3272_ = l_mkPanicMessageWithDecl(v___x_3271_, v___x_3270_, v___x_3269_, v___x_3268_, v___x_3267_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object* v_inst_3273_, lean_object* v___f_3274_, lean_object* v___x_3275_, lean_object* v_____do__lift_3276_){
_start:
{
if (lean_obj_tag(v_____do__lift_3276_) == 0)
{
lean_object* v_modifyInfoState_3277_; lean_object* v___x_3278_; 
v_modifyInfoState_3277_ = lean_ctor_get(v_inst_3273_, 1);
lean_inc(v_modifyInfoState_3277_);
lean_dec_ref(v_inst_3273_);
v___x_3278_ = lean_apply_1(v_modifyInfoState_3277_, v___f_3274_);
return v___x_3278_;
}
else
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
lean_dec_ref(v___f_3274_);
lean_dec_ref(v_inst_3273_);
v___x_3279_ = lean_obj_once(&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3, &l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3_once, _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3);
v___x_3280_ = l_panic___redArg(v___x_3275_, v___x_3279_);
return v___x_3280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object* v_inst_3281_, lean_object* v___f_3282_, lean_object* v___x_3283_, lean_object* v_____do__lift_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(v_inst_3281_, v___f_3282_, v___x_3283_, v_____do__lift_3284_);
lean_dec(v_____do__lift_3284_);
lean_dec(v___x_3283_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object* v_inst_3286_, lean_object* v_inst_3287_, lean_object* v_mvarId_3288_, lean_object* v_infoTree_3289_){
_start:
{
lean_object* v_toBind_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___f_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___f_3297_; lean_object* v___x_3298_; 
v_toBind_3290_ = lean_ctor_get(v_inst_3286_, 1);
lean_inc(v_toBind_3290_);
v___x_3291_ = lean_box(0);
v___x_3292_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3293_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
lean_inc(v_mvarId_3288_);
v___f_3294_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__0), 5, 4);
lean_closure_set(v___f_3294_, 0, v___x_3292_);
lean_closure_set(v___f_3294_, 1, v___x_3293_);
lean_closure_set(v___f_3294_, 2, v_mvarId_3288_);
lean_closure_set(v___f_3294_, 3, v_infoTree_3289_);
lean_inc_ref(v_inst_3287_);
lean_inc_ref(v_inst_3286_);
v___x_3295_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3286_, v_inst_3287_, v_mvarId_3288_);
v___x_3296_ = l_instInhabitedOfMonad___redArg(v_inst_3286_, v___x_3291_);
v___f_3297_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3297_, 0, v_inst_3287_);
lean_closure_set(v___f_3297_, 1, v___f_3294_);
lean_closure_set(v___f_3297_, 2, v___x_3296_);
v___x_3298_ = lean_apply_4(v_toBind_3290_, lean_box(0), lean_box(0), v___x_3295_, v___f_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* v_m_3299_, lean_object* v_inst_3300_, lean_object* v_inst_3301_, lean_object* v_mvarId_3302_, lean_object* v_infoTree_3303_){
_start:
{
lean_object* v___x_3304_; 
v___x_3304_ = l_Lean_Elab_assignInfoHoleId___redArg(v_inst_3300_, v_inst_3301_, v_mvarId_3302_, v_infoTree_3303_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object* v_stx_3305_, lean_object* v_output_3306_, lean_object* v_toPure_3307_, lean_object* v_____do__lift_3308_){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3309_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3309_, 0, v_____do__lift_3308_);
lean_ctor_set(v___x_3309_, 1, v_stx_3305_);
lean_ctor_set(v___x_3309_, 2, v_output_3306_);
v___x_3310_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
v___x_3311_ = lean_apply_2(v_toPure_3307_, lean_box(0), v___x_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object* v_inst_3312_, lean_object* v_inst_3313_, lean_object* v_inst_3314_, lean_object* v_inst_3315_, lean_object* v_stx_3316_, lean_object* v_output_3317_, lean_object* v_x_3318_){
_start:
{
lean_object* v_toApplicative_3319_; lean_object* v_toBind_3320_; lean_object* v_toPure_3321_; lean_object* v___f_3322_; lean_object* v_mkInfo_3323_; lean_object* v___f_3324_; lean_object* v___x_3325_; 
v_toApplicative_3319_ = lean_ctor_get(v_inst_3313_, 0);
v_toBind_3320_ = lean_ctor_get(v_inst_3313_, 1);
v_toPure_3321_ = lean_ctor_get(v_toApplicative_3319_, 1);
lean_inc_n(v_toPure_3321_, 2);
v___f_3322_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3322_, 0, v_stx_3316_);
lean_closure_set(v___f_3322_, 1, v_output_3317_);
lean_closure_set(v___f_3322_, 2, v_toPure_3321_);
lean_inc_n(v_toBind_3320_, 2);
v_mkInfo_3323_ = lean_apply_4(v_toBind_3320_, lean_box(0), lean_box(0), v_inst_3315_, v___f_3322_);
v___f_3324_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3324_, 0, v_toPure_3321_);
lean_closure_set(v___f_3324_, 1, v_toBind_3320_);
lean_closure_set(v___f_3324_, 2, v_mkInfo_3323_);
v___x_3325_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3313_, v_inst_3314_, v_inst_3312_, v_x_3318_, v___f_3324_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* v_m_3326_, lean_object* v_00_u03b1_3327_, lean_object* v_inst_3328_, lean_object* v_inst_3329_, lean_object* v_inst_3330_, lean_object* v_inst_3331_, lean_object* v_stx_3332_, lean_object* v_output_3333_, lean_object* v_x_3334_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l_Lean_Elab_withMacroExpansionInfo___redArg(v_inst_3328_, v_inst_3329_, v_inst_3330_, v_inst_3331_, v_stx_3332_, v_output_3333_, v_x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object* v_treesSaved_3336_, lean_object* v___x_3337_, lean_object* v___x_3338_, lean_object* v___x_3339_, lean_object* v_mvarId_3340_, lean_object* v_s_3341_){
_start:
{
lean_object* v_trees_3342_; uint8_t v_enabled_3343_; lean_object* v_assignment_3344_; lean_object* v_lazyAssignment_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3362_; 
v_trees_3342_ = lean_ctor_get(v_s_3341_, 2);
v_enabled_3343_ = lean_ctor_get_uint8(v_s_3341_, sizeof(void*)*3);
v_assignment_3344_ = lean_ctor_get(v_s_3341_, 0);
v_lazyAssignment_3345_ = lean_ctor_get(v_s_3341_, 1);
v_isSharedCheck_3362_ = !lean_is_exclusive(v_s_3341_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3347_ = v_s_3341_;
v_isShared_3348_ = v_isSharedCheck_3362_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_trees_3342_);
lean_inc(v_lazyAssignment_3345_);
lean_inc(v_assignment_3344_);
lean_dec(v_s_3341_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3362_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v_size_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
v_size_3349_ = lean_ctor_get(v_trees_3342_, 2);
v___x_3350_ = lean_unsigned_to_nat(0u);
v___x_3351_ = lean_nat_dec_lt(v___x_3350_, v_size_3349_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3353_; 
lean_dec_ref(v_trees_3342_);
lean_dec(v_mvarId_3340_);
lean_dec_ref(v___x_3339_);
lean_dec_ref(v___x_3338_);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 2, v_treesSaved_3336_);
v___x_3353_ = v___x_3347_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_assignment_3344_);
lean_ctor_set(v_reuseFailAlloc_3354_, 1, v_lazyAssignment_3345_);
lean_ctor_set(v_reuseFailAlloc_3354_, 2, v_treesSaved_3336_);
lean_ctor_set_uint8(v_reuseFailAlloc_3354_, sizeof(void*)*3, v_enabled_3343_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
else
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3360_; 
v___x_3355_ = lean_unsigned_to_nat(1u);
v___x_3356_ = lean_nat_sub(v_size_3349_, v___x_3355_);
v___x_3357_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3337_, v_trees_3342_, v___x_3356_);
lean_dec(v___x_3356_);
lean_dec_ref(v_trees_3342_);
v___x_3358_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3338_, v___x_3339_, v_assignment_3344_, v_mvarId_3340_, v___x_3357_);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 2, v_treesSaved_3336_);
lean_ctor_set(v___x_3347_, 0, v___x_3358_);
v___x_3360_ = v___x_3347_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3358_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_lazyAssignment_3345_);
lean_ctor_set(v_reuseFailAlloc_3361_, 2, v_treesSaved_3336_);
lean_ctor_set_uint8(v_reuseFailAlloc_3361_, sizeof(void*)*3, v_enabled_3343_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1___boxed(lean_object* v_treesSaved_3363_, lean_object* v___x_3364_, lean_object* v___x_3365_, lean_object* v___x_3366_, lean_object* v_mvarId_3367_, lean_object* v_s_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l_Lean_Elab_withInfoHole___redArg___lam__1(v_treesSaved_3363_, v___x_3364_, v___x_3365_, v___x_3366_, v_mvarId_3367_, v_s_3368_);
lean_dec_ref(v___x_3364_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object* v_modifyInfoState_3370_, lean_object* v___f_3371_, lean_object* v_x_3372_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = lean_apply_1(v_modifyInfoState_3370_, v___f_3371_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object* v_modifyInfoState_3374_, lean_object* v___f_3375_, lean_object* v_x_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_3374_, v___f_3375_, v_x_3376_);
lean_dec(v_x_3376_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object* v_toFunctor_3378_, lean_object* v___x_3379_, lean_object* v___x_3380_, lean_object* v___x_3381_, lean_object* v_mvarId_3382_, lean_object* v_modifyInfoState_3383_, lean_object* v_inst_3384_, lean_object* v_x_3385_, lean_object* v___f_3386_, lean_object* v_treesSaved_3387_){
_start:
{
lean_object* v_map_3388_; lean_object* v___f_3389_; lean_object* v___f_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v_map_3388_ = lean_ctor_get(v_toFunctor_3378_, 0);
lean_inc(v_map_3388_);
lean_dec_ref(v_toFunctor_3378_);
v___f_3389_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_3389_, 0, v_treesSaved_3387_);
lean_closure_set(v___f_3389_, 1, v___x_3379_);
lean_closure_set(v___f_3389_, 2, v___x_3380_);
lean_closure_set(v___f_3389_, 3, v___x_3381_);
lean_closure_set(v___f_3389_, 4, v_mvarId_3382_);
v___f_3390_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3390_, 0, v_modifyInfoState_3383_);
lean_closure_set(v___f_3390_, 1, v___f_3389_);
v___x_3391_ = lean_apply_4(v_inst_3384_, lean_box(0), lean_box(0), v_x_3385_, v___f_3390_);
v___x_3392_ = lean_apply_4(v_map_3388_, lean_box(0), lean_box(0), v___f_3386_, v___x_3391_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object* v_inst_3393_, lean_object* v_inst_3394_, lean_object* v_inst_3395_, lean_object* v_mvarId_3396_, lean_object* v_x_3397_){
_start:
{
lean_object* v_toApplicative_3398_; lean_object* v_toBind_3399_; lean_object* v_getInfoState_3400_; lean_object* v_modifyInfoState_3401_; lean_object* v_toFunctor_3402_; lean_object* v___f_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___f_3407_; lean_object* v___f_3408_; lean_object* v___x_3409_; 
v_toApplicative_3398_ = lean_ctor_get(v_inst_3394_, 0);
v_toBind_3399_ = lean_ctor_get(v_inst_3394_, 1);
lean_inc_n(v_toBind_3399_, 2);
v_getInfoState_3400_ = lean_ctor_get(v_inst_3395_, 0);
lean_inc(v_getInfoState_3400_);
v_modifyInfoState_3401_ = lean_ctor_get(v_inst_3395_, 1);
v_toFunctor_3402_ = lean_ctor_get(v_toApplicative_3398_, 0);
v___f_3403_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
v___x_3404_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3405_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3406_ = l_Lean_Elab_instInhabitedInfoTree_default;
lean_inc(v_x_3397_);
lean_inc(v_modifyInfoState_3401_);
lean_inc_ref(v_toFunctor_3402_);
v___f_3407_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3407_, 0, v_toFunctor_3402_);
lean_closure_set(v___f_3407_, 1, v___x_3406_);
lean_closure_set(v___f_3407_, 2, v___x_3404_);
lean_closure_set(v___f_3407_, 3, v___x_3405_);
lean_closure_set(v___f_3407_, 4, v_mvarId_3396_);
lean_closure_set(v___f_3407_, 5, v_modifyInfoState_3401_);
lean_closure_set(v___f_3407_, 6, v_inst_3393_);
lean_closure_set(v___f_3407_, 7, v_x_3397_);
lean_closure_set(v___f_3407_, 8, v___f_3403_);
v___f_3408_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3408_, 0, v_x_3397_);
lean_closure_set(v___f_3408_, 1, v_inst_3394_);
lean_closure_set(v___f_3408_, 2, v_inst_3395_);
lean_closure_set(v___f_3408_, 3, v_toBind_3399_);
lean_closure_set(v___f_3408_, 4, v___f_3407_);
v___x_3409_ = lean_apply_4(v_toBind_3399_, lean_box(0), lean_box(0), v_getInfoState_3400_, v___f_3408_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object* v_m_3410_, lean_object* v_00_u03b1_3411_, lean_object* v_inst_3412_, lean_object* v_inst_3413_, lean_object* v_inst_3414_, lean_object* v_mvarId_3415_, lean_object* v_x_3416_){
_start:
{
lean_object* v_toApplicative_3417_; lean_object* v_toBind_3418_; lean_object* v_getInfoState_3419_; lean_object* v_modifyInfoState_3420_; lean_object* v_toFunctor_3421_; lean_object* v___f_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___f_3426_; lean_object* v___f_3427_; lean_object* v___x_3428_; 
v_toApplicative_3417_ = lean_ctor_get(v_inst_3413_, 0);
v_toBind_3418_ = lean_ctor_get(v_inst_3413_, 1);
lean_inc_n(v_toBind_3418_, 2);
v_getInfoState_3419_ = lean_ctor_get(v_inst_3414_, 0);
lean_inc(v_getInfoState_3419_);
v_modifyInfoState_3420_ = lean_ctor_get(v_inst_3414_, 1);
v_toFunctor_3421_ = lean_ctor_get(v_toApplicative_3417_, 0);
v___f_3422_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
v___x_3423_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3424_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3425_ = l_Lean_Elab_instInhabitedInfoTree_default;
lean_inc(v_x_3416_);
lean_inc(v_modifyInfoState_3420_);
lean_inc_ref(v_toFunctor_3421_);
v___f_3426_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3426_, 0, v_toFunctor_3421_);
lean_closure_set(v___f_3426_, 1, v___x_3425_);
lean_closure_set(v___f_3426_, 2, v___x_3423_);
lean_closure_set(v___f_3426_, 3, v___x_3424_);
lean_closure_set(v___f_3426_, 4, v_mvarId_3415_);
lean_closure_set(v___f_3426_, 5, v_modifyInfoState_3420_);
lean_closure_set(v___f_3426_, 6, v_inst_3412_);
lean_closure_set(v___f_3426_, 7, v_x_3416_);
lean_closure_set(v___f_3426_, 8, v___f_3422_);
v___f_3427_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3427_, 0, v_x_3416_);
lean_closure_set(v___f_3427_, 1, v_inst_3413_);
lean_closure_set(v___f_3427_, 2, v_inst_3414_);
lean_closure_set(v___f_3427_, 3, v_toBind_3418_);
lean_closure_set(v___f_3427_, 4, v___f_3426_);
v___x_3428_ = lean_apply_4(v_toBind_3418_, lean_box(0), lean_box(0), v_getInfoState_3419_, v___f_3427_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t v_flag_3429_, lean_object* v_s_3430_){
_start:
{
lean_object* v_assignment_3431_; lean_object* v_lazyAssignment_3432_; lean_object* v_trees_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
v_assignment_3431_ = lean_ctor_get(v_s_3430_, 0);
v_lazyAssignment_3432_ = lean_ctor_get(v_s_3430_, 1);
v_trees_3433_ = lean_ctor_get(v_s_3430_, 2);
v_isSharedCheck_3440_ = !lean_is_exclusive(v_s_3430_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3435_ = v_s_3430_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_trees_3433_);
lean_inc(v_lazyAssignment_3432_);
lean_inc(v_assignment_3431_);
lean_dec(v_s_3430_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3436_ == 0)
{
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_assignment_3431_);
lean_ctor_set(v_reuseFailAlloc_3439_, 1, v_lazyAssignment_3432_);
lean_ctor_set(v_reuseFailAlloc_3439_, 2, v_trees_3433_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
lean_ctor_set_uint8(v___x_3438_, sizeof(void*)*3, v_flag_3429_);
return v___x_3438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object* v_flag_3441_, lean_object* v_s_3442_){
_start:
{
uint8_t v_flag_boxed_3443_; lean_object* v_res_3444_; 
v_flag_boxed_3443_ = lean_unbox(v_flag_3441_);
v_res_3444_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_3443_, v_s_3442_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object* v_inst_3445_, uint8_t v_flag_3446_){
_start:
{
lean_object* v_modifyInfoState_3447_; lean_object* v___x_3448_; lean_object* v___f_3449_; lean_object* v___x_3450_; 
v_modifyInfoState_3447_ = lean_ctor_get(v_inst_3445_, 1);
lean_inc(v_modifyInfoState_3447_);
lean_dec_ref(v_inst_3445_);
v___x_3448_ = lean_box(v_flag_3446_);
v___f_3449_ = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3449_, 0, v___x_3448_);
v___x_3450_ = lean_apply_1(v_modifyInfoState_3447_, v___f_3449_);
return v___x_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object* v_inst_3451_, lean_object* v_flag_3452_){
_start:
{
uint8_t v_flag_boxed_3453_; lean_object* v_res_3454_; 
v_flag_boxed_3453_ = lean_unbox(v_flag_3452_);
v_res_3454_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3451_, v_flag_boxed_3453_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object* v_m_3455_, lean_object* v_inst_3456_, uint8_t v_flag_3457_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3456_, v_flag_3457_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object* v_m_3459_, lean_object* v_inst_3460_, lean_object* v_flag_3461_){
_start:
{
uint8_t v_flag_boxed_3462_; lean_object* v_res_3463_; 
v_flag_boxed_3462_ = lean_unbox(v_flag_3461_);
v_res_3463_ = l_Lean_Elab_enableInfoTree(v_m_3459_, v_inst_3460_, v_flag_boxed_3462_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object* v_x_3464_){
_start:
{
lean_object* v_fst_3465_; 
v_fst_3465_ = lean_ctor_get(v_x_3464_, 0);
lean_inc(v_fst_3465_);
return v_fst_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object* v_x_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_3466_);
lean_dec_ref(v_x_3466_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object* v_x_3468_, lean_object* v_____r_3469_){
_start:
{
lean_inc(v_x_3468_);
return v_x_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object* v_x_3470_, lean_object* v_____r_3471_){
_start:
{
lean_object* v_res_3472_; 
v_res_3472_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_3470_, v_____r_3471_);
lean_dec(v_x_3470_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object* v___x_3473_, lean_object* v_x_3474_){
_start:
{
lean_inc(v___x_3473_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object* v___x_3475_, lean_object* v_x_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_3475_, v_x_3476_);
lean_dec(v_x_3476_);
lean_dec(v___x_3475_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object* v_toFunctor_3478_, lean_object* v_inst_3479_, uint8_t v_flag_3480_, lean_object* v_toBind_3481_, lean_object* v___f_3482_, lean_object* v_inst_3483_, lean_object* v___f_3484_, lean_object* v_____do__lift_3485_){
_start:
{
uint8_t v_enabled_3486_; lean_object* v_map_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___f_3491_; lean_object* v_y_3492_; lean_object* v___x_3493_; 
v_enabled_3486_ = lean_ctor_get_uint8(v_____do__lift_3485_, sizeof(void*)*3);
v_map_3487_ = lean_ctor_get(v_toFunctor_3478_, 0);
lean_inc(v_map_3487_);
lean_dec_ref(v_toFunctor_3478_);
lean_inc_ref(v_inst_3479_);
v___x_3488_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3479_, v_flag_3480_);
v___x_3489_ = lean_apply_4(v_toBind_3481_, lean_box(0), lean_box(0), v___x_3488_, v___f_3482_);
v___x_3490_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3479_, v_enabled_3486_);
v___f_3491_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_3491_, 0, v___x_3490_);
v_y_3492_ = lean_apply_4(v_inst_3483_, lean_box(0), lean_box(0), v___x_3489_, v___f_3491_);
v___x_3493_ = lean_apply_4(v_map_3487_, lean_box(0), lean_box(0), v___f_3484_, v_y_3492_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object* v_toFunctor_3494_, lean_object* v_inst_3495_, lean_object* v_flag_3496_, lean_object* v_toBind_3497_, lean_object* v___f_3498_, lean_object* v_inst_3499_, lean_object* v___f_3500_, lean_object* v_____do__lift_3501_){
_start:
{
uint8_t v_flag_boxed_3502_; lean_object* v_res_3503_; 
v_flag_boxed_3502_ = lean_unbox(v_flag_3496_);
v_res_3503_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_3494_, v_inst_3495_, v_flag_boxed_3502_, v_toBind_3497_, v___f_3498_, v_inst_3499_, v___f_3500_, v_____do__lift_3501_);
lean_dec_ref(v_____do__lift_3501_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object* v_inst_3505_, lean_object* v_inst_3506_, lean_object* v_inst_3507_, uint8_t v_flag_3508_, lean_object* v_x_3509_){
_start:
{
lean_object* v_toApplicative_3510_; lean_object* v_toBind_3511_; lean_object* v_getInfoState_3512_; lean_object* v_toFunctor_3513_; lean_object* v___f_3514_; lean_object* v___f_3515_; lean_object* v___x_3516_; lean_object* v___f_3517_; lean_object* v___x_3518_; 
v_toApplicative_3510_ = lean_ctor_get(v_inst_3505_, 0);
lean_inc_ref(v_toApplicative_3510_);
v_toBind_3511_ = lean_ctor_get(v_inst_3505_, 1);
lean_inc_n(v_toBind_3511_, 2);
lean_dec_ref(v_inst_3505_);
v_getInfoState_3512_ = lean_ctor_get(v_inst_3506_, 0);
lean_inc(v_getInfoState_3512_);
v_toFunctor_3513_ = lean_ctor_get(v_toApplicative_3510_, 0);
lean_inc_ref(v_toFunctor_3513_);
lean_dec_ref(v_toApplicative_3510_);
v___f_3514_ = ((lean_object*)(l_Lean_Elab_withEnableInfoTree___redArg___closed__0));
v___f_3515_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3515_, 0, v_x_3509_);
v___x_3516_ = lean_box(v_flag_3508_);
v___f_3517_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_3517_, 0, v_toFunctor_3513_);
lean_closure_set(v___f_3517_, 1, v_inst_3506_);
lean_closure_set(v___f_3517_, 2, v___x_3516_);
lean_closure_set(v___f_3517_, 3, v_toBind_3511_);
lean_closure_set(v___f_3517_, 4, v___f_3515_);
lean_closure_set(v___f_3517_, 5, v_inst_3507_);
lean_closure_set(v___f_3517_, 6, v___f_3514_);
v___x_3518_ = lean_apply_4(v_toBind_3511_, lean_box(0), lean_box(0), v_getInfoState_3512_, v___f_3517_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object* v_inst_3519_, lean_object* v_inst_3520_, lean_object* v_inst_3521_, lean_object* v_flag_3522_, lean_object* v_x_3523_){
_start:
{
uint8_t v_flag_boxed_3524_; lean_object* v_res_3525_; 
v_flag_boxed_3524_ = lean_unbox(v_flag_3522_);
v_res_3525_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3519_, v_inst_3520_, v_inst_3521_, v_flag_boxed_3524_, v_x_3523_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object* v_m_3526_, lean_object* v_00_u03b1_3527_, lean_object* v_inst_3528_, lean_object* v_inst_3529_, lean_object* v_inst_3530_, uint8_t v_flag_3531_, lean_object* v_x_3532_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3528_, v_inst_3529_, v_inst_3530_, v_flag_3531_, v_x_3532_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object* v_m_3534_, lean_object* v_00_u03b1_3535_, lean_object* v_inst_3536_, lean_object* v_inst_3537_, lean_object* v_inst_3538_, lean_object* v_flag_3539_, lean_object* v_x_3540_){
_start:
{
uint8_t v_flag_boxed_3541_; lean_object* v_res_3542_; 
v_flag_boxed_3541_ = lean_unbox(v_flag_3539_);
v_res_3542_ = l_Lean_Elab_withEnableInfoTree(v_m_3534_, v_00_u03b1_3535_, v_inst_3536_, v_inst_3537_, v_inst_3538_, v_flag_boxed_3541_, v_x_3540_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object* v_toPure_3543_, lean_object* v_____do__lift_3544_){
_start:
{
lean_object* v_trees_3545_; lean_object* v___x_3546_; 
v_trees_3545_ = lean_ctor_get(v_____do__lift_3544_, 2);
lean_inc_ref(v_trees_3545_);
lean_dec_ref(v_____do__lift_3544_);
v___x_3546_ = lean_apply_2(v_toPure_3543_, lean_box(0), v_trees_3545_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object* v_inst_3547_, lean_object* v_inst_3548_){
_start:
{
lean_object* v_toApplicative_3549_; lean_object* v_toBind_3550_; lean_object* v_getInfoState_3551_; lean_object* v_toPure_3552_; lean_object* v___f_3553_; lean_object* v___x_3554_; 
v_toApplicative_3549_ = lean_ctor_get(v_inst_3548_, 0);
lean_inc_ref(v_toApplicative_3549_);
v_toBind_3550_ = lean_ctor_get(v_inst_3548_, 1);
lean_inc(v_toBind_3550_);
lean_dec_ref(v_inst_3548_);
v_getInfoState_3551_ = lean_ctor_get(v_inst_3547_, 0);
lean_inc(v_getInfoState_3551_);
lean_dec_ref(v_inst_3547_);
v_toPure_3552_ = lean_ctor_get(v_toApplicative_3549_, 1);
lean_inc(v_toPure_3552_);
lean_dec_ref(v_toApplicative_3549_);
v___f_3553_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3553_, 0, v_toPure_3552_);
v___x_3554_ = lean_apply_4(v_toBind_3550_, lean_box(0), lean_box(0), v_getInfoState_3551_, v___f_3553_);
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object* v_m_3555_, lean_object* v_inst_3556_, lean_object* v_inst_3557_){
_start:
{
lean_object* v___x_3558_; 
v___x_3558_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_3556_, v_inst_3557_);
return v___x_3558_;
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
