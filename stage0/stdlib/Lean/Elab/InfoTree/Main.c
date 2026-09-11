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
extern lean_object* l_Lean_diagnostics;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
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
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_maxRecDepth;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "<InfoTree>"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2;
static const lean_ctor_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4;
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
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11;
static const lean_array_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17;
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
LEAN_EXPORT lean_object* l_Lean_Elab_CustomInfo_format(lean_object* v_x_136_){
_start:
{
lean_object* v_value_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_151_; 
v_value_137_ = lean_ctor_get(v_x_136_, 1);
v_isSharedCheck_151_ = !lean_is_exclusive(v_x_136_);
if (v_isSharedCheck_151_ == 0)
{
lean_object* v_unused_152_; 
v_unused_152_ = lean_ctor_get(v_x_136_, 0);
lean_dec(v_unused_152_);
v___x_139_ = v_x_136_;
v_isShared_140_ = v_isSharedCheck_151_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_value_137_);
lean_dec(v_x_136_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_151_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_141_ = ((lean_object*)(l_Lean_Elab_CustomInfo_format___closed__1));
v___x_142_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_value_137_);
lean_dec(v_value_137_);
v___x_143_ = 1;
v___x_144_ = l_Lean_Name_toString(v___x_142_, v___x_143_);
v___x_145_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
if (v_isShared_140_ == 0)
{
lean_ctor_set_tag(v___x_139_, 5);
lean_ctor_set(v___x_139_, 1, v___x_145_);
lean_ctor_set(v___x_139_, 0, v___x_141_);
v___x_147_ = v___x_139_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v___x_145_);
v___x_147_ = v_reuseFailAlloc_150_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(l_Lean_Elab_CustomInfo_format___closed__3));
v___x_149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
return v___x_149_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(lean_object* v_opts_155_, lean_object* v_opt_156_){
_start:
{
lean_object* v_name_157_; lean_object* v_defValue_158_; lean_object* v_map_159_; lean_object* v___x_160_; 
v_name_157_ = lean_ctor_get(v_opt_156_, 0);
v_defValue_158_ = lean_ctor_get(v_opt_156_, 1);
v_map_159_ = lean_ctor_get(v_opts_155_, 0);
v___x_160_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_159_, v_name_157_);
if (lean_obj_tag(v___x_160_) == 0)
{
uint8_t v___x_161_; 
v___x_161_ = lean_unbox(v_defValue_158_);
return v___x_161_;
}
else
{
lean_object* v_val_162_; 
v_val_162_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_val_162_);
lean_dec_ref_known(v___x_160_, 1);
if (lean_obj_tag(v_val_162_) == 1)
{
uint8_t v_v_163_; 
v_v_163_ = lean_ctor_get_uint8(v_val_162_, 0);
lean_dec_ref_known(v_val_162_, 0);
return v_v_163_;
}
else
{
uint8_t v___x_164_; 
lean_dec(v_val_162_);
v___x_164_ = lean_unbox(v_defValue_158_);
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0___boxed(lean_object* v_opts_165_, lean_object* v_opt_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v_opts_165_, v_opt_166_);
lean_dec_ref(v_opt_166_);
lean_dec_ref(v_opts_165_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(lean_object* v_opts_169_, lean_object* v_opt_170_){
_start:
{
lean_object* v_name_171_; lean_object* v_defValue_172_; lean_object* v_map_173_; lean_object* v___x_174_; 
v_name_171_ = lean_ctor_get(v_opt_170_, 0);
v_defValue_172_ = lean_ctor_get(v_opt_170_, 1);
v_map_173_ = lean_ctor_get(v_opts_169_, 0);
v___x_174_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_173_, v_name_171_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_inc(v_defValue_172_);
return v_defValue_172_;
}
else
{
lean_object* v_val_175_; 
v_val_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_val_175_);
lean_dec_ref_known(v___x_174_, 1);
if (lean_obj_tag(v_val_175_) == 3)
{
lean_object* v_v_176_; 
v_v_176_ = lean_ctor_get(v_val_175_, 0);
lean_inc(v_v_176_);
lean_dec_ref_known(v_val_175_, 1);
return v_v_176_;
}
else
{
lean_dec(v_val_175_);
lean_inc(v_defValue_172_);
return v_defValue_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1___boxed(lean_object* v_opts_177_, lean_object* v_opt_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v_opts_177_, v_opt_178_);
lean_dec_ref(v_opt_178_);
lean_dec_ref(v_opts_177_);
return v_res_179_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = l_Lean_Options_empty;
v___x_182_ = l_Lean_Core_getMaxHeartbeats(v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = l_Lean_firstFrontendMacroScope;
v___x_185_ = lean_nat_add(v___x_184_, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_unsigned_to_nat(32u);
v___x_191_ = lean_mk_empty_array_with_capacity(v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5(void){
_start:
{
size_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_193_ = ((size_t)5ULL);
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_unsigned_to_nat(32u);
v___x_196_ = lean_mk_empty_array_with_capacity(v___x_195_);
v___x_197_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4);
v___x_198_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v___x_196_);
lean_ctor_set(v___x_198_, 2, v___x_194_);
lean_ctor_set(v___x_198_, 3, v___x_194_);
lean_ctor_set_usize(v___x_198_, 4, v___x_193_);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6(void){
_start:
{
lean_object* v___x_199_; uint64_t v___x_200_; lean_object* v___x_201_; 
v___x_199_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5);
v___x_200_ = 0ULL;
v___x_201_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set_uint64(v___x_201_, sizeof(void*)*1, v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7(void){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_202_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = l_Lean_NameSet_empty;
v___x_208_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5);
v___x_209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
lean_ctor_set(v___x_209_, 2, v___x_207_);
return v___x_209_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; lean_object* v___x_213_; 
v___x_210_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5);
v___x_211_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_212_ = 1;
v___x_213_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_213_, 0, v___x_211_);
lean_ctor_set(v___x_213_, 1, v___x_211_);
lean_ctor_set(v___x_213_, 2, v___x_210_);
lean_ctor_set_uint8(v___x_213_, sizeof(void*)*3, v___x_212_);
return v___x_213_;
}
}
static uint8_t _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_219_ = l_Lean_diagnostics;
v___x_220_ = l_Lean_Options_empty;
v___x_221_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v___x_220_, v___x_219_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = l_Lean_maxRecDepth;
v___x_223_ = l_Lean_Options_empty;
v___x_224_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v___x_223_, v___x_222_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg(lean_object* v_info_225_, lean_object* v_x_226_){
_start:
{
lean_object* v_a_229_; lean_object* v_toCommandContextInfo_232_; lean_object* v_env_233_; lean_object* v_options_234_; lean_object* v_currNamespace_235_; lean_object* v_openDecls_236_; lean_object* v_ngen_237_; uint8_t v___x_238_; lean_object* v_env_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___y_261_; uint8_t v___y_262_; lean_object* v_fileName_263_; lean_object* v_fileMap_264_; lean_object* v_currNamespace_265_; lean_object* v_openDecls_266_; lean_object* v_initHeartbeats_267_; lean_object* v_maxHeartbeats_268_; lean_object* v_quotContext_269_; lean_object* v_currMacroScope_270_; lean_object* v_cancelTk_x3f_271_; lean_object* v_inheritedTraceOptions_272_; lean_object* v_currRecDepth_273_; lean_object* v_ref_274_; uint8_t v_suppressElabErrors_275_; lean_object* v___y_276_; lean_object* v___y_313_; uint8_t v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_332_; lean_object* v___y_333_; uint8_t v___y_334_; lean_object* v___y_335_; uint8_t v___y_336_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; lean_object* v___y_361_; lean_object* v___x_370_; uint8_t v___y_372_; lean_object* v_env_392_; uint8_t v___x_393_; 
v_toCommandContextInfo_232_ = lean_ctor_get(v_info_225_, 0);
lean_inc_ref(v_toCommandContextInfo_232_);
lean_dec_ref(v_info_225_);
v_env_233_ = lean_ctor_get(v_toCommandContextInfo_232_, 0);
lean_inc_ref(v_env_233_);
v_options_234_ = lean_ctor_get(v_toCommandContextInfo_232_, 4);
lean_inc_ref(v_options_234_);
v_currNamespace_235_ = lean_ctor_get(v_toCommandContextInfo_232_, 5);
lean_inc(v_currNamespace_235_);
v_openDecls_236_ = lean_ctor_get(v_toCommandContextInfo_232_, 6);
lean_inc(v_openDecls_236_);
v_ngen_237_ = lean_ctor_get(v_toCommandContextInfo_232_, 7);
lean_inc_ref(v_ngen_237_);
lean_dec_ref(v_toCommandContextInfo_232_);
v___x_238_ = 0;
v_env_239_ = l_Lean_Environment_setExporting(v_env_233_, v___x_238_);
v___x_240_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0));
v___x_241_ = l_Lean_instInhabitedFileMap_default;
v___x_242_ = l_Lean_Options_empty;
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_245_ = lean_box(0);
v___x_246_ = l_Lean_firstFrontendMacroScope;
v___x_247_ = lean_box(0);
v___x_248_ = lean_box(0);
v___x_249_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2);
v___x_250_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3));
v___x_251_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6);
v___x_252_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9);
v___x_253_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10);
v___x_254_ = 1;
v___x_255_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11);
v___x_256_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12));
v___x_257_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_257_, 0, v_env_239_);
lean_ctor_set(v___x_257_, 1, v___x_249_);
lean_ctor_set(v___x_257_, 2, v_ngen_237_);
lean_ctor_set(v___x_257_, 3, v___x_250_);
lean_ctor_set(v___x_257_, 4, v___x_251_);
lean_ctor_set(v___x_257_, 5, v___x_252_);
lean_ctor_set(v___x_257_, 6, v___x_253_);
lean_ctor_set(v___x_257_, 7, v___x_255_);
lean_ctor_set(v___x_257_, 8, v___x_256_);
v___x_258_ = lean_io_get_num_heartbeats();
v___x_259_ = lean_st_mk_ref(v___x_257_);
v___x_356_ = l_Lean_inheritedTraceOptions;
v___x_357_ = lean_st_ref_get(v___x_356_);
v___x_358_ = l_Lean_diagnostics;
v___x_359_ = lean_uint8_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16);
v___x_370_ = lean_st_ref_get(v___x_259_);
v_env_392_ = lean_ctor_get(v___x_370_, 0);
lean_inc_ref(v_env_392_);
lean_dec(v___x_370_);
v___x_393_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_392_);
lean_dec_ref(v_env_392_);
if (v___x_359_ == 0)
{
if (v___x_393_ == 0)
{
lean_inc(v___x_259_);
v___y_361_ = v___x_259_;
goto v___jp_360_;
}
else
{
v___y_372_ = v___x_359_;
goto v___jp_371_;
}
}
else
{
v___y_372_ = v___x_393_;
goto v___jp_371_;
}
v___jp_228_:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_mk_io_user_error(v_a_229_);
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
v___jp_260_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_277_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v_options_234_, v___y_261_);
v___x_278_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_278_, 0, v_fileName_263_);
lean_ctor_set(v___x_278_, 1, v_fileMap_264_);
lean_ctor_set(v___x_278_, 2, v_options_234_);
lean_ctor_set(v___x_278_, 3, v___x_277_);
lean_ctor_set(v___x_278_, 4, v_currNamespace_265_);
lean_ctor_set(v___x_278_, 5, v_openDecls_266_);
lean_ctor_set(v___x_278_, 6, v_initHeartbeats_267_);
lean_ctor_set(v___x_278_, 7, v_maxHeartbeats_268_);
lean_ctor_set(v___x_278_, 8, v_quotContext_269_);
lean_ctor_set(v___x_278_, 9, v_currMacroScope_270_);
lean_ctor_set(v___x_278_, 10, v_cancelTk_x3f_271_);
lean_ctor_set(v___x_278_, 11, v_inheritedTraceOptions_272_);
v___x_279_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v_currRecDepth_273_);
lean_ctor_set(v___x_279_, 2, v_ref_274_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*3, v___y_262_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*3 + 1, v_suppressElabErrors_275_);
v___x_280_ = lean_apply_3(v_x_226_, v___x_279_, v___y_276_, lean_box(0));
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_289_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_289_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = lean_st_ref_get(v___x_259_);
lean_dec(v___x_259_);
lean_dec(v___x_285_);
if (v_isShared_284_ == 0)
{
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_281_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_311_; 
lean_dec(v___x_259_);
v_a_290_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_311_ == 0)
{
v___x_292_ = v___x_280_;
v_isShared_293_ = v_isSharedCheck_311_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_280_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_311_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
if (lean_obj_tag(v_a_290_) == 0)
{
lean_object* v_msg_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
v_msg_294_ = lean_ctor_get(v_a_290_, 1);
lean_inc_ref(v_msg_294_);
lean_dec_ref_known(v_a_290_, 2);
v___x_295_ = l_Lean_MessageData_toString(v_msg_294_);
v___x_296_ = lean_mk_io_user_error(v___x_295_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_296_);
v___x_298_ = v___x_292_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
else
{
lean_object* v_id_300_; lean_object* v___x_301_; 
lean_del_object(v___x_292_);
v_id_300_ = lean_ctor_get(v_a_290_, 0);
lean_inc(v_id_300_);
lean_dec_ref_known(v_a_290_, 2);
v___x_301_ = l_Lean_InternalExceptionId_getName(v_id_300_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec(v_id_300_);
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_301_, 1);
v___x_303_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13));
v___x_304_ = l_Lean_Name_toString(v_a_302_, v___x_254_);
v___x_305_ = lean_string_append(v___x_303_, v___x_304_);
lean_dec_ref(v___x_304_);
v_a_229_ = v___x_305_;
goto v___jp_228_;
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec_ref_known(v___x_301_, 1);
v___x_306_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14));
v___x_307_ = l_Nat_reprFast(v_id_300_);
v___x_308_ = lean_string_append(v___x_306_, v___x_307_);
lean_dec_ref(v___x_307_);
v___x_309_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15));
v___x_310_ = lean_string_append(v___x_308_, v___x_309_);
v_a_229_ = v___x_310_;
goto v___jp_228_;
}
}
}
}
}
v___jp_312_:
{
lean_object* v_toCold_317_; lean_object* v_currRecDepth_318_; lean_object* v_ref_319_; uint8_t v_suppressElabErrors_320_; lean_object* v_fileName_321_; lean_object* v_fileMap_322_; lean_object* v_currNamespace_323_; lean_object* v_openDecls_324_; lean_object* v_initHeartbeats_325_; lean_object* v_maxHeartbeats_326_; lean_object* v_quotContext_327_; lean_object* v_currMacroScope_328_; lean_object* v_cancelTk_x3f_329_; lean_object* v_inheritedTraceOptions_330_; 
v_toCold_317_ = lean_ctor_get(v___y_315_, 0);
lean_inc_ref(v_toCold_317_);
v_currRecDepth_318_ = lean_ctor_get(v___y_315_, 1);
lean_inc(v_currRecDepth_318_);
v_ref_319_ = lean_ctor_get(v___y_315_, 2);
lean_inc(v_ref_319_);
v_suppressElabErrors_320_ = lean_ctor_get_uint8(v___y_315_, sizeof(void*)*3 + 1);
lean_dec_ref(v___y_315_);
v_fileName_321_ = lean_ctor_get(v_toCold_317_, 0);
lean_inc_ref(v_fileName_321_);
v_fileMap_322_ = lean_ctor_get(v_toCold_317_, 1);
lean_inc_ref(v_fileMap_322_);
v_currNamespace_323_ = lean_ctor_get(v_toCold_317_, 4);
lean_inc(v_currNamespace_323_);
v_openDecls_324_ = lean_ctor_get(v_toCold_317_, 5);
lean_inc(v_openDecls_324_);
v_initHeartbeats_325_ = lean_ctor_get(v_toCold_317_, 6);
lean_inc(v_initHeartbeats_325_);
v_maxHeartbeats_326_ = lean_ctor_get(v_toCold_317_, 7);
lean_inc(v_maxHeartbeats_326_);
v_quotContext_327_ = lean_ctor_get(v_toCold_317_, 8);
lean_inc(v_quotContext_327_);
v_currMacroScope_328_ = lean_ctor_get(v_toCold_317_, 9);
lean_inc(v_currMacroScope_328_);
v_cancelTk_x3f_329_ = lean_ctor_get(v_toCold_317_, 10);
lean_inc(v_cancelTk_x3f_329_);
v_inheritedTraceOptions_330_ = lean_ctor_get(v_toCold_317_, 11);
lean_inc_ref(v_inheritedTraceOptions_330_);
lean_dec_ref(v_toCold_317_);
v___y_261_ = v___y_313_;
v___y_262_ = v___y_314_;
v_fileName_263_ = v_fileName_321_;
v_fileMap_264_ = v_fileMap_322_;
v_currNamespace_265_ = v_currNamespace_323_;
v_openDecls_266_ = v_openDecls_324_;
v_initHeartbeats_267_ = v_initHeartbeats_325_;
v_maxHeartbeats_268_ = v_maxHeartbeats_326_;
v_quotContext_269_ = v_quotContext_327_;
v_currMacroScope_270_ = v_currMacroScope_328_;
v_cancelTk_x3f_271_ = v_cancelTk_x3f_329_;
v_inheritedTraceOptions_272_ = v_inheritedTraceOptions_330_;
v_currRecDepth_273_ = v_currRecDepth_318_;
v_ref_274_ = v_ref_319_;
v_suppressElabErrors_275_ = v_suppressElabErrors_320_;
v___y_276_ = v___y_316_;
goto v___jp_260_;
}
v___jp_331_:
{
if (v___y_336_ == 0)
{
lean_object* v___x_337_; lean_object* v_env_338_; lean_object* v_nextMacroScope_339_; lean_object* v_ngen_340_; lean_object* v_auxDeclNGen_341_; lean_object* v_traceState_342_; lean_object* v_messages_343_; lean_object* v_infoState_344_; lean_object* v_snapshotTasks_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_354_; 
v___x_337_ = lean_st_ref_take(v___y_332_);
v_env_338_ = lean_ctor_get(v___x_337_, 0);
v_nextMacroScope_339_ = lean_ctor_get(v___x_337_, 1);
v_ngen_340_ = lean_ctor_get(v___x_337_, 2);
v_auxDeclNGen_341_ = lean_ctor_get(v___x_337_, 3);
v_traceState_342_ = lean_ctor_get(v___x_337_, 4);
v_messages_343_ = lean_ctor_get(v___x_337_, 6);
v_infoState_344_ = lean_ctor_get(v___x_337_, 7);
v_snapshotTasks_345_ = lean_ctor_get(v___x_337_, 8);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; 
v_unused_355_ = lean_ctor_get(v___x_337_, 5);
lean_dec(v_unused_355_);
v___x_347_ = v___x_337_;
v_isShared_348_ = v_isSharedCheck_354_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_snapshotTasks_345_);
lean_inc(v_infoState_344_);
lean_inc(v_messages_343_);
lean_inc(v_traceState_342_);
lean_inc(v_auxDeclNGen_341_);
lean_inc(v_ngen_340_);
lean_inc(v_nextMacroScope_339_);
lean_inc(v_env_338_);
lean_dec(v___x_337_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_354_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_349_ = l_Lean_Kernel_enableDiag(v_env_338_, v___y_334_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 5, v___x_252_);
lean_ctor_set(v___x_347_, 0, v___x_349_);
v___x_351_ = v___x_347_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_nextMacroScope_339_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v_ngen_340_);
lean_ctor_set(v_reuseFailAlloc_353_, 3, v_auxDeclNGen_341_);
lean_ctor_set(v_reuseFailAlloc_353_, 4, v_traceState_342_);
lean_ctor_set(v_reuseFailAlloc_353_, 5, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_353_, 6, v_messages_343_);
lean_ctor_set(v_reuseFailAlloc_353_, 7, v_infoState_344_);
lean_ctor_set(v_reuseFailAlloc_353_, 8, v_snapshotTasks_345_);
v___x_351_ = v_reuseFailAlloc_353_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; 
v___x_352_ = lean_st_ref_put(v___y_332_, v___x_351_);
v___y_313_ = v___y_333_;
v___y_314_ = v___y_334_;
v___y_315_ = v___y_335_;
v___y_316_ = v___y_332_;
goto v___jp_312_;
}
}
}
else
{
v___y_313_ = v___y_333_;
v___y_314_ = v___y_334_;
v___y_315_ = v___y_335_;
v___y_316_ = v___y_332_;
goto v___jp_312_;
}
}
v___jp_360_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v_env_368_; uint8_t v___x_369_; 
v___x_362_ = l_Lean_maxRecDepth;
v___x_363_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17);
lean_inc(v___x_357_);
lean_inc(v___x_258_);
lean_inc(v_openDecls_236_);
lean_inc(v_currNamespace_235_);
v___x_364_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_364_, 0, v___x_240_);
lean_ctor_set(v___x_364_, 1, v___x_241_);
lean_ctor_set(v___x_364_, 2, v___x_242_);
lean_ctor_set(v___x_364_, 3, v___x_363_);
lean_ctor_set(v___x_364_, 4, v_currNamespace_235_);
lean_ctor_set(v___x_364_, 5, v_openDecls_236_);
lean_ctor_set(v___x_364_, 6, v___x_258_);
lean_ctor_set(v___x_364_, 7, v___x_244_);
lean_ctor_set(v___x_364_, 8, v___x_245_);
lean_ctor_set(v___x_364_, 9, v___x_246_);
lean_ctor_set(v___x_364_, 10, v___x_247_);
lean_ctor_set(v___x_364_, 11, v___x_357_);
v___x_365_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_243_);
lean_ctor_set(v___x_365_, 2, v___x_248_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*3, v___x_359_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*3 + 1, v___x_238_);
v___x_366_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v_options_234_, v___x_358_);
v___x_367_ = lean_st_ref_get(v___y_361_);
v_env_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc_ref(v_env_368_);
lean_dec(v___x_367_);
v___x_369_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_368_);
lean_dec_ref(v_env_368_);
if (v___x_366_ == 0)
{
if (v___x_369_ == 0)
{
lean_dec_ref_known(v___x_365_, 3);
v___y_261_ = v___x_362_;
v___y_262_ = v___x_366_;
v_fileName_263_ = v___x_240_;
v_fileMap_264_ = v___x_241_;
v_currNamespace_265_ = v_currNamespace_235_;
v_openDecls_266_ = v_openDecls_236_;
v_initHeartbeats_267_ = v___x_258_;
v_maxHeartbeats_268_ = v___x_244_;
v_quotContext_269_ = v___x_245_;
v_currMacroScope_270_ = v___x_246_;
v_cancelTk_x3f_271_ = v___x_247_;
v_inheritedTraceOptions_272_ = v___x_357_;
v_currRecDepth_273_ = v___x_243_;
v_ref_274_ = v___x_248_;
v_suppressElabErrors_275_ = v___x_238_;
v___y_276_ = v___y_361_;
goto v___jp_260_;
}
else
{
lean_dec(v___x_357_);
lean_dec(v___x_258_);
lean_dec(v_openDecls_236_);
lean_dec(v_currNamespace_235_);
v___y_332_ = v___y_361_;
v___y_333_ = v___x_362_;
v___y_334_ = v___x_366_;
v___y_335_ = v___x_365_;
v___y_336_ = v___x_366_;
goto v___jp_331_;
}
}
else
{
lean_dec(v___x_357_);
lean_dec(v___x_258_);
lean_dec(v_openDecls_236_);
lean_dec(v_currNamespace_235_);
v___y_332_ = v___y_361_;
v___y_333_ = v___x_362_;
v___y_334_ = v___x_366_;
v___y_335_ = v___x_365_;
v___y_336_ = v___x_369_;
goto v___jp_331_;
}
}
v___jp_371_:
{
if (v___y_372_ == 0)
{
lean_object* v___x_373_; lean_object* v_env_374_; lean_object* v_nextMacroScope_375_; lean_object* v_ngen_376_; lean_object* v_auxDeclNGen_377_; lean_object* v_traceState_378_; lean_object* v_messages_379_; lean_object* v_infoState_380_; lean_object* v_snapshotTasks_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_390_; 
v___x_373_ = lean_st_ref_take(v___x_259_);
v_env_374_ = lean_ctor_get(v___x_373_, 0);
v_nextMacroScope_375_ = lean_ctor_get(v___x_373_, 1);
v_ngen_376_ = lean_ctor_get(v___x_373_, 2);
v_auxDeclNGen_377_ = lean_ctor_get(v___x_373_, 3);
v_traceState_378_ = lean_ctor_get(v___x_373_, 4);
v_messages_379_ = lean_ctor_get(v___x_373_, 6);
v_infoState_380_ = lean_ctor_get(v___x_373_, 7);
v_snapshotTasks_381_ = lean_ctor_get(v___x_373_, 8);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_390_ == 0)
{
lean_object* v_unused_391_; 
v_unused_391_ = lean_ctor_get(v___x_373_, 5);
lean_dec(v_unused_391_);
v___x_383_ = v___x_373_;
v_isShared_384_ = v_isSharedCheck_390_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_snapshotTasks_381_);
lean_inc(v_infoState_380_);
lean_inc(v_messages_379_);
lean_inc(v_traceState_378_);
lean_inc(v_auxDeclNGen_377_);
lean_inc(v_ngen_376_);
lean_inc(v_nextMacroScope_375_);
lean_inc(v_env_374_);
lean_dec(v___x_373_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_390_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_385_ = l_Lean_Kernel_enableDiag(v_env_374_, v___x_359_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 5, v___x_252_);
lean_ctor_set(v___x_383_, 0, v___x_385_);
v___x_387_ = v___x_383_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_nextMacroScope_375_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v_ngen_376_);
lean_ctor_set(v_reuseFailAlloc_389_, 3, v_auxDeclNGen_377_);
lean_ctor_set(v_reuseFailAlloc_389_, 4, v_traceState_378_);
lean_ctor_set(v_reuseFailAlloc_389_, 5, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_389_, 6, v_messages_379_);
lean_ctor_set(v_reuseFailAlloc_389_, 7, v_infoState_380_);
lean_ctor_set(v_reuseFailAlloc_389_, 8, v_snapshotTasks_381_);
v___x_387_ = v_reuseFailAlloc_389_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; 
v___x_388_ = lean_st_ref_put(v___x_259_, v___x_387_);
lean_inc(v___x_259_);
v___y_361_ = v___x_259_;
goto v___jp_360_;
}
}
}
else
{
lean_inc(v___x_259_);
v___y_361_ = v___x_259_;
goto v___jp_360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___boxed(lean_object* v_info_394_, lean_object* v_x_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_394_, v_x_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM(lean_object* v_00_u03b1_398_, lean_object* v_info_399_, lean_object* v_x_400_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_399_, v_x_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___boxed(lean_object* v_00_u03b1_403_, lean_object* v_info_404_, lean_object* v_x_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Elab_ContextInfo_runCoreM(v_00_u03b1_403_, v_info_404_, v_x_405_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(lean_object* v___x_408_, lean_object* v_x_409_, lean_object* v___x_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_st_mk_ref(v___x_408_);
lean_inc(v___x_414_);
v___x_415_ = lean_apply_5(v_x_409_, v___x_410_, v___x_414_, v___y_411_, v___y_412_, lean_box(0));
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_425_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_425_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_425_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_425_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_420_ = lean_st_ref_get(v___x_414_);
lean_dec(v___x_414_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v_a_416_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_421_);
v___x_423_ = v___x_418_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec(v___x_414_);
v_a_426_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_415_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_415_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed(lean_object* v___x_434_, lean_object* v_x_435_, lean_object* v___x_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(v___x_434_, v_x_435_, v___x_436_, v___y_437_, v___y_438_);
return v_res_440_;
}
}
static uint64_t _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1(void){
_start:
{
lean_object* v___x_447_; uint64_t v___x_448_; 
v___x_447_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_448_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_447_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2(void){
_start:
{
uint64_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_449_ = lean_uint64_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1);
v___x_450_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_451_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set_uint64(v___x_451_, sizeof(void*)*1, v___x_449_);
return v___x_451_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_457_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
lean_ctor_set(v___x_457_, 2, v___x_456_);
lean_ctor_set(v___x_457_, 3, v___x_456_);
lean_ctor_set(v___x_457_, 4, v___x_456_);
lean_ctor_set(v___x_457_, 5, v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_unsigned_to_nat(32u);
v___x_459_ = lean_mk_empty_array_with_capacity(v___x_458_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7(void){
_start:
{
size_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_461_ = ((size_t)5ULL);
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_unsigned_to_nat(32u);
v___x_464_ = lean_mk_empty_array_with_capacity(v___x_463_);
v___x_465_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6);
v___x_466_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v___x_464_);
lean_ctor_set(v___x_466_, 2, v___x_462_);
lean_ctor_set(v___x_466_, 3, v___x_462_);
lean_ctor_set_usize(v___x_466_, 4, v___x_461_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
lean_ctor_set(v___x_468_, 2, v___x_467_);
lean_ctor_set(v___x_468_, 3, v___x_467_);
lean_ctor_set(v___x_468_, 4, v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object* v_info_469_, lean_object* v_lctx_470_, lean_object* v_x_471_){
_start:
{
lean_object* v___x_473_; uint8_t v___x_474_; uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v_toCommandContextInfo_481_; lean_object* v_mctx_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___f_487_; lean_object* v___x_488_; 
v___x_473_ = lean_box(1);
v___x_474_ = 0;
v___x_475_ = 1;
v___x_476_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2);
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3));
v___x_479_ = lean_box(0);
v___x_480_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_480_, 0, v___x_476_);
lean_ctor_set(v___x_480_, 1, v___x_473_);
lean_ctor_set(v___x_480_, 2, v_lctx_470_);
lean_ctor_set(v___x_480_, 3, v___x_478_);
lean_ctor_set(v___x_480_, 4, v___x_479_);
lean_ctor_set(v___x_480_, 5, v___x_477_);
lean_ctor_set(v___x_480_, 6, v___x_479_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*7, v___x_474_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*7 + 1, v___x_474_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*7 + 2, v___x_474_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*7 + 3, v___x_475_);
v_toCommandContextInfo_481_ = lean_ctor_get(v_info_469_, 0);
v_mctx_482_ = lean_ctor_get(v_toCommandContextInfo_481_, 3);
v___x_483_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_484_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7);
v___x_485_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8);
lean_inc_ref(v_mctx_482_);
v___x_486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_486_, 0, v_mctx_482_);
lean_ctor_set(v___x_486_, 1, v___x_483_);
lean_ctor_set(v___x_486_, 2, v___x_473_);
lean_ctor_set(v___x_486_, 3, v___x_484_);
lean_ctor_set(v___x_486_, 4, v___x_485_);
v___f_487_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_487_, 0, v___x_486_);
lean_closure_set(v___f_487_, 1, v_x_471_);
lean_closure_set(v___f_487_, 2, v___x_480_);
v___x_488_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_469_, v___f_487_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_497_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_497_ == 0)
{
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_497_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_497_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v_fst_493_; lean_object* v___x_495_; 
v_fst_493_ = lean_ctor_get(v_a_489_, 0);
lean_inc(v_fst_493_);
lean_dec(v_a_489_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v_fst_493_);
v___x_495_ = v___x_491_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_fst_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
v_a_498_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_488_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_488_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object* v_info_506_, lean_object* v_lctx_507_, lean_object* v_x_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_506_, v_lctx_507_, v_x_508_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object* v_00_u03b1_511_, lean_object* v_info_512_, lean_object* v_lctx_513_, lean_object* v_x_514_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_512_, v_lctx_513_, v_x_514_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object* v_00_u03b1_517_, lean_object* v_info_518_, lean_object* v_lctx_519_, lean_object* v_x_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_Elab_ContextInfo_runMetaM(v_00_u03b1_517_, v_info_518_, v_lctx_519_, v_x_520_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object* v_info_523_, lean_object* v_lctx_524_){
_start:
{
lean_object* v_toCommandContextInfo_525_; lean_object* v_env_526_; lean_object* v_mctx_527_; lean_object* v_options_528_; lean_object* v_currNamespace_529_; lean_object* v_openDecls_530_; lean_object* v___x_531_; 
v_toCommandContextInfo_525_ = lean_ctor_get(v_info_523_, 0);
v_env_526_ = lean_ctor_get(v_toCommandContextInfo_525_, 0);
v_mctx_527_ = lean_ctor_get(v_toCommandContextInfo_525_, 3);
v_options_528_ = lean_ctor_get(v_toCommandContextInfo_525_, 4);
v_currNamespace_529_ = lean_ctor_get(v_toCommandContextInfo_525_, 5);
v_openDecls_530_ = lean_ctor_get(v_toCommandContextInfo_525_, 6);
lean_inc(v_openDecls_530_);
lean_inc(v_currNamespace_529_);
lean_inc_ref(v_options_528_);
lean_inc_ref(v_mctx_527_);
lean_inc_ref(v_env_526_);
v___x_531_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_531_, 0, v_env_526_);
lean_ctor_set(v___x_531_, 1, v_mctx_527_);
lean_ctor_set(v___x_531_, 2, v_lctx_524_);
lean_ctor_set(v___x_531_, 3, v_options_528_);
lean_ctor_set(v___x_531_, 4, v_currNamespace_529_);
lean_ctor_set(v___x_531_, 5, v_openDecls_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object* v_info_532_, lean_object* v_lctx_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_532_, v_lctx_533_);
lean_dec_ref(v_info_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object* v_info_535_, lean_object* v_lctx_536_, lean_object* v_stx_537_){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_535_, v_lctx_536_);
v___x_540_ = l_Lean_ppTerm(v___x_539_, v_stx_537_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object* v_info_542_, lean_object* v_lctx_543_, lean_object* v_stx_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Elab_ContextInfo_ppSyntax(v_info_542_, v_lctx_543_, v_stx_544_);
lean_dec_ref(v_info_542_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(lean_object* v_ctx_562_, lean_object* v_pos_563_, lean_object* v_info_564_){
_start:
{
lean_object* v_toCommandContextInfo_565_; lean_object* v_fileMap_566_; lean_object* v___x_567_; lean_object* v_line_568_; lean_object* v_column_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_592_; 
v_toCommandContextInfo_565_ = lean_ctor_get(v_ctx_562_, 0);
lean_inc_ref(v_toCommandContextInfo_565_);
lean_dec_ref(v_ctx_562_);
v_fileMap_566_ = lean_ctor_get(v_toCommandContextInfo_565_, 2);
lean_inc_ref(v_fileMap_566_);
lean_dec_ref(v_toCommandContextInfo_565_);
v___x_567_ = l_Lean_FileMap_toPosition(v_fileMap_566_, v_pos_563_);
v_line_568_ = lean_ctor_get(v___x_567_, 0);
v_column_569_ = lean_ctor_get(v___x_567_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_592_ == 0)
{
v___x_571_ = v___x_567_;
v_isShared_572_ = v_isSharedCheck_592_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_column_569_);
lean_inc(v_line_568_);
lean_dec(v___x_567_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_592_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_573_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_574_ = l_Nat_reprFast(v_line_568_);
v___x_575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
if (v_isShared_572_ == 0)
{
lean_ctor_set_tag(v___x_571_, 5);
lean_ctor_set(v___x_571_, 1, v___x_575_);
lean_ctor_set(v___x_571_, 0, v___x_573_);
v___x_577_ = v___x_571_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v___x_575_);
v___x_577_ = v_reuseFailAlloc_591_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v_pos_584_; 
v___x_578_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
v___x_579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = l_Nat_reprFast(v_column_569_);
v___x_581_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
v___x_582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_579_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v_pos_584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_pos_584_, 0, v___x_582_);
lean_ctor_set(v_pos_584_, 1, v___x_583_);
switch(lean_obj_tag(v_info_564_))
{
case 0:
{
return v_pos_584_;
}
case 1:
{
uint8_t v_canonical_588_; 
v_canonical_588_ = lean_ctor_get_uint8(v_info_564_, sizeof(void*)*2);
if (v_canonical_588_ == 1)
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9));
v___x_590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_590_, 0, v_pos_584_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
return v___x_590_;
}
else
{
goto v___jp_585_;
}
}
default: 
{
goto v___jp_585_;
}
}
v___jp_585_:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7));
v___x_587_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_587_, 0, v_pos_584_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
return v___x_587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(lean_object* v_ctx_593_, lean_object* v_pos_594_, lean_object* v_info_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_593_, v_pos_594_, v_info_595_);
lean_dec(v_info_595_);
lean_dec(v_pos_594_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(lean_object* v_ctx_600_, lean_object* v_stx_601_){
_start:
{
lean_object* v___y_603_; lean_object* v___y_604_; uint8_t v___x_612_; lean_object* v___y_614_; lean_object* v___x_617_; 
v___x_612_ = 0;
v___x_617_ = l_Lean_Syntax_getPos_x3f(v_stx_601_, v___x_612_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_618_; 
v___x_618_ = lean_unsigned_to_nat(0u);
v___y_614_ = v___x_618_;
goto v___jp_613_;
}
else
{
lean_object* v_val_619_; 
v_val_619_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_val_619_);
lean_dec_ref_known(v___x_617_, 1);
v___y_614_ = v_val_619_;
goto v___jp_613_;
}
v___jp_602_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_605_ = l_Lean_Syntax_getHeadInfo(v_stx_601_);
lean_inc_ref(v_ctx_600_);
v___x_606_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_600_, v___y_603_, v___x_605_);
lean_dec(v___x_605_);
lean_dec(v___y_603_);
v___x_607_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = l_Lean_Syntax_getTailInfo(v_stx_601_);
v___x_610_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_600_, v___y_604_, v___x_609_);
lean_dec(v___x_609_);
lean_dec(v___y_604_);
v___x_611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_608_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
return v___x_611_;
}
v___jp_613_:
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_Syntax_getTailPos_x3f(v_stx_601_, v___x_612_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_inc(v___y_614_);
v___y_603_ = v___y_614_;
v___y_604_ = v___y_614_;
goto v___jp_602_;
}
else
{
lean_object* v_val_616_; 
v_val_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_val_616_);
lean_dec_ref_known(v___x_615_, 1);
v___y_603_ = v___y_614_;
v___y_604_ = v_val_616_;
goto v___jp_602_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(lean_object* v_ctx_620_, lean_object* v_stx_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_620_, v_stx_621_);
lean_dec(v_stx_621_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(lean_object* v_ctx_626_, lean_object* v_info_627_){
_start:
{
lean_object* v_elaborator_628_; lean_object* v_stx_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_644_; 
v_elaborator_628_ = lean_ctor_get(v_info_627_, 0);
v_stx_629_ = lean_ctor_get(v_info_627_, 1);
v_isSharedCheck_644_ = !lean_is_exclusive(v_info_627_);
if (v_isSharedCheck_644_ == 0)
{
v___x_631_ = v_info_627_;
v_isShared_632_ = v_isSharedCheck_644_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_stx_629_);
lean_inc(v_elaborator_628_);
lean_dec(v_info_627_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_644_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
uint8_t v___x_633_; 
v___x_633_ = l_Lean_Name_isAnonymous(v_elaborator_628_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_634_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_626_, v_stx_629_);
lean_dec(v_stx_629_);
v___x_635_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
if (v_isShared_632_ == 0)
{
lean_ctor_set_tag(v___x_631_, 5);
lean_ctor_set(v___x_631_, 1, v___x_635_);
lean_ctor_set(v___x_631_, 0, v___x_634_);
v___x_637_ = v___x_631_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v___x_635_);
v___x_637_ = v_reuseFailAlloc_642_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
uint8_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_638_ = 1;
v___x_639_ = l_Lean_Name_toString(v_elaborator_628_, v___x_638_);
v___x_640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
v___x_641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_637_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
return v___x_641_;
}
}
else
{
lean_object* v___x_643_; 
lean_del_object(v___x_631_);
lean_dec(v_elaborator_628_);
v___x_643_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_626_, v_stx_629_);
lean_dec(v_stx_629_);
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object* v_info_645_, lean_object* v_ctx_646_, lean_object* v_x_647_){
_start:
{
lean_object* v_lctx_649_; lean_object* v___x_650_; 
v_lctx_649_ = lean_ctor_get(v_info_645_, 1);
lean_inc_ref(v_lctx_649_);
lean_dec_ref(v_info_645_);
v___x_650_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_646_, v_lctx_649_, v_x_647_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(lean_object* v_info_651_, lean_object* v_ctx_652_, lean_object* v_x_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_651_, v_ctx_652_, v_x_653_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM(lean_object* v_00_u03b1_656_, lean_object* v_info_657_, lean_object* v_ctx_658_, lean_object* v_x_659_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_657_, v_ctx_658_, v_x_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___boxed(lean_object* v_00_u03b1_662_, lean_object* v_info_663_, lean_object* v_ctx_664_, lean_object* v_x_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Elab_TermInfo_runMetaM(v_00_u03b1_662_, v_info_663_, v_ctx_664_, v_x_665_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0(lean_object* v_ctx_682_, lean_object* v_toElabInfo_683_, lean_object* v_expr_684_, uint8_t v_isBinder_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v_a_706_; lean_object* v___y_716_; uint8_t v___y_717_; lean_object* v___y_720_; lean_object* v_a_721_; lean_object* v___x_724_; 
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
lean_inc(v___y_687_);
lean_inc_ref(v___y_686_);
lean_inc_ref(v_expr_684_);
v___x_724_ = lean_infer_type(v_expr_684_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_726_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref_known(v___x_724_, 1);
v___x_726_ = l_Lean_Meta_ppExpr(v_a_725_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
v_a_706_ = v_a_727_;
goto v___jp_705_;
}
else
{
lean_object* v_a_728_; 
v_a_728_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_728_);
v___y_720_ = v___x_726_;
v_a_721_ = v_a_728_;
goto v___jp_719_;
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
v_a_729_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_724_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_724_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
lean_inc(v_a_729_);
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
v___y_720_ = v___x_734_;
v_a_721_ = v_a_729_;
goto v___jp_719_;
}
}
}
v___jp_691_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
lean_inc_ref(v___y_694_);
v___x_695_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_695_, 0, v___y_694_);
v___x_696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_696_, 0, v___y_693_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_696_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v___y_692_);
v___x_700_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_682_, v_toElabInfo_683_);
v___x_703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
v___jp_705_:
{
lean_object* v___x_707_; 
v___x_707_ = l_Lean_Meta_ppExpr(v_expr_684_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_707_, 1);
v___x_709_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__3));
v___x_710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v_a_708_);
v___x_711_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
v___x_712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
if (v_isBinder_685_ == 0)
{
lean_object* v___x_713_; 
v___x_713_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__6));
v___y_692_ = v_a_706_;
v___y_693_ = v___x_712_;
v___y_694_ = v___x_713_;
goto v___jp_691_;
}
else
{
lean_object* v___x_714_; 
v___x_714_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__7));
v___y_692_ = v_a_706_;
v___y_693_ = v___x_712_;
v___y_694_ = v___x_714_;
goto v___jp_691_;
}
}
else
{
lean_dec(v_a_706_);
lean_dec_ref(v_toElabInfo_683_);
lean_dec_ref(v_ctx_682_);
return v___x_707_;
}
}
v___jp_715_:
{
if (v___y_717_ == 0)
{
lean_object* v___x_718_; 
lean_dec_ref(v___y_716_);
v___x_718_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__9));
v_a_706_ = v___x_718_;
goto v___jp_705_;
}
else
{
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v_expr_684_);
lean_dec_ref(v_toElabInfo_683_);
lean_dec_ref(v_ctx_682_);
return v___y_716_;
}
}
v___jp_719_:
{
uint8_t v___x_722_; 
v___x_722_ = l_Lean_Exception_isInterrupt(v_a_721_);
if (v___x_722_ == 0)
{
uint8_t v___x_723_; 
v___x_723_ = l_Lean_Exception_isRuntime(v_a_721_);
v___y_716_ = v___y_720_;
v___y_717_ = v___x_723_;
goto v___jp_715_;
}
else
{
lean_dec_ref(v_a_721_);
v___y_716_ = v___y_720_;
v___y_717_ = v___x_722_;
goto v___jp_715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0___boxed(lean_object* v_ctx_737_, lean_object* v_toElabInfo_738_, lean_object* v_expr_739_, lean_object* v_isBinder_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
uint8_t v_isBinder_boxed_746_; lean_object* v_res_747_; 
v_isBinder_boxed_746_ = lean_unbox(v_isBinder_740_);
v_res_747_ = l_Lean_Elab_TermInfo_format___lam__0(v_ctx_737_, v_toElabInfo_738_, v_expr_739_, v_isBinder_boxed_746_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format(lean_object* v_ctx_748_, lean_object* v_info_749_){
_start:
{
lean_object* v_toElabInfo_751_; lean_object* v_expr_752_; uint8_t v_isBinder_753_; lean_object* v___x_754_; lean_object* v___f_755_; lean_object* v___x_756_; 
v_toElabInfo_751_ = lean_ctor_get(v_info_749_, 0);
v_expr_752_ = lean_ctor_get(v_info_749_, 3);
v_isBinder_753_ = lean_ctor_get_uint8(v_info_749_, sizeof(void*)*4);
v___x_754_ = lean_box(v_isBinder_753_);
lean_inc_ref(v_expr_752_);
lean_inc_ref(v_toElabInfo_751_);
lean_inc_ref(v_ctx_748_);
v___f_755_ = lean_alloc_closure((void*)(l_Lean_Elab_TermInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_755_, 0, v_ctx_748_);
lean_closure_set(v___f_755_, 1, v_toElabInfo_751_);
lean_closure_set(v___f_755_, 2, v_expr_752_);
lean_closure_set(v___f_755_, 3, v___x_754_);
v___x_756_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_749_, v_ctx_748_, v___f_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___boxed(lean_object* v_ctx_757_, lean_object* v_info_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_Elab_TermInfo_format(v_ctx_757_, v_info_758_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialTermInfo_format(lean_object* v_ctx_764_, lean_object* v_info_765_){
_start:
{
lean_object* v_toElabInfo_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_toElabInfo_766_ = lean_ctor_get(v_info_765_, 0);
lean_inc_ref(v_toElabInfo_766_);
lean_dec_ref(v_info_765_);
v___x_767_ = ((lean_object*)(l_Lean_Elab_PartialTermInfo_format___closed__1));
v___x_768_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_764_, v_toElabInfo_766_);
v___x_769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(lean_object* v_x_776_){
_start:
{
if (lean_obj_tag(v_x_776_) == 0)
{
lean_object* v___x_777_; 
v___x_777_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_777_;
}
else
{
lean_object* v_val_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_788_; 
v_val_778_ = lean_ctor_get(v_x_776_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v_x_776_);
if (v_isSharedCheck_788_ == 0)
{
v___x_780_ = v_x_776_;
v_isShared_781_ = v_isSharedCheck_788_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_val_778_);
lean_dec(v_x_776_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_788_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_782_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_783_ = lean_expr_dbg_to_string(v_val_778_);
lean_dec(v_val_778_);
if (v_isShared_781_ == 0)
{
lean_ctor_set_tag(v___x_780_, 3);
lean_ctor_set(v___x_780_, 0, v___x_783_);
v___x_785_ = v___x_780_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_787_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; 
v___x_786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_782_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
return v___x_786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0(lean_object* v_ctx_795_, lean_object* v_lctx_796_, lean_object* v_stx_797_, lean_object* v_expectedType_x3f_798_, lean_object* v_info_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___x_805_; lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_824_; 
v___x_805_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_795_, v_lctx_796_, v_stx_797_);
v_a_806_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_824_ == 0)
{
v___x_808_ = v___x_805_;
v_isShared_809_ = v_isSharedCheck_824_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_824_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_810_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__1));
v___x_811_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v_a_806_);
v___x_812_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_798_);
v___x_815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = l_Lean_Elab_CompletionInfo_stx(v_info_799_);
v___x_819_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_795_, v___x_818_);
lean_dec(v___x_818_);
v___x_820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_817_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_820_);
v___x_822_ = v___x_808_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___boxed(lean_object* v_ctx_825_, lean_object* v_lctx_826_, lean_object* v_stx_827_, lean_object* v_expectedType_x3f_828_, lean_object* v_info_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_Elab_CompletionInfo_format___lam__0(v_ctx_825_, v_lctx_826_, v_stx_827_, v_expectedType_x3f_828_, v_info_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec_ref(v_info_829_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format(lean_object* v_ctx_842_, lean_object* v_info_843_){
_start:
{
switch(lean_obj_tag(v_info_843_))
{
case 0:
{
lean_object* v_termInfo_845_; lean_object* v_expectedType_x3f_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_867_; 
v_termInfo_845_ = lean_ctor_get(v_info_843_, 0);
v_expectedType_x3f_846_ = lean_ctor_get(v_info_843_, 1);
v_isSharedCheck_867_ = !lean_is_exclusive(v_info_843_);
if (v_isSharedCheck_867_ == 0)
{
v___x_848_ = v_info_843_;
v_isShared_849_ = v_isSharedCheck_867_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_expectedType_x3f_846_);
lean_inc(v_termInfo_845_);
lean_dec(v_info_843_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_867_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_Elab_TermInfo_format(v_ctx_842_, v_termInfo_845_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_866_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_866_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_866_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_866_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__1));
if (v_isShared_849_ == 0)
{
lean_ctor_set_tag(v___x_848_, 5);
lean_ctor_set(v___x_848_, 1, v_a_851_);
lean_ctor_set(v___x_848_, 0, v___x_855_);
v___x_857_ = v___x_848_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_a_851_);
v___x_857_ = v_reuseFailAlloc_865_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_858_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_857_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_846_);
v___x_861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_861_);
v___x_863_ = v___x_853_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_del_object(v___x_848_);
lean_dec(v_expectedType_x3f_846_);
return v___x_850_;
}
}
}
case 1:
{
lean_object* v_stx_868_; lean_object* v_lctx_869_; lean_object* v_expectedType_x3f_870_; lean_object* v___f_871_; lean_object* v___x_872_; 
v_stx_868_ = lean_ctor_get(v_info_843_, 0);
lean_inc(v_stx_868_);
v_lctx_869_ = lean_ctor_get(v_info_843_, 2);
lean_inc_ref_n(v_lctx_869_, 2);
v_expectedType_x3f_870_ = lean_ctor_get(v_info_843_, 3);
lean_inc(v_expectedType_x3f_870_);
lean_inc_ref(v_ctx_842_);
v___f_871_ = lean_alloc_closure((void*)(l_Lean_Elab_CompletionInfo_format___lam__0___boxed), 10, 5);
lean_closure_set(v___f_871_, 0, v_ctx_842_);
lean_closure_set(v___f_871_, 1, v_lctx_869_);
lean_closure_set(v___f_871_, 2, v_stx_868_);
lean_closure_set(v___f_871_, 3, v_expectedType_x3f_870_);
lean_closure_set(v___f_871_, 4, v_info_843_);
v___x_872_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_842_, v_lctx_869_, v___f_871_);
return v___x_872_;
}
default: 
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_873_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__3));
v___x_874_ = l_Lean_Elab_CompletionInfo_stx(v_info_843_);
lean_dec_ref(v_info_843_);
v___x_875_ = lean_box(0);
v___x_876_ = 0;
lean_inc(v___x_874_);
v___x_877_ = l_Lean_Syntax_formatStx(v___x_874_, v___x_875_, v___x_876_);
v___x_878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_873_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_878_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_842_, v___x_874_);
lean_dec(v___x_874_);
v___x_882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___boxed(lean_object* v_ctx_884_, lean_object* v_info_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Elab_CompletionInfo_format(v_ctx_884_, v_info_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format(lean_object* v_ctx_891_, lean_object* v_info_892_){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_894_ = ((lean_object*)(l_Lean_Elab_CommandInfo_format___closed__1));
v___x_895_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_891_, v_info_892_);
v___x_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format___boxed(lean_object* v_ctx_898_, lean_object* v_info_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_Elab_CommandInfo_format(v_ctx_898_, v_info_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format(lean_object* v_ctx_905_, lean_object* v_info_906_){
_start:
{
lean_object* v_stx_908_; lean_object* v_optionName_909_; lean_object* v___x_910_; uint8_t v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v_stx_908_ = lean_ctor_get(v_info_906_, 0);
lean_inc(v_stx_908_);
v_optionName_909_ = lean_ctor_get(v_info_906_, 1);
lean_inc(v_optionName_909_);
lean_dec_ref(v_info_906_);
v___x_910_ = ((lean_object*)(l_Lean_Elab_OptionInfo_format___closed__1));
v___x_911_ = 1;
v___x_912_ = l_Lean_Name_toString(v_optionName_909_, v___x_911_);
v___x_913_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
v___x_914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_910_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_905_, v_stx_908_);
lean_dec(v_stx_908_);
v___x_918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format___boxed(lean_object* v_ctx_920_, lean_object* v_info_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Elab_OptionInfo_format(v_ctx_920_, v_info_921_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format(lean_object* v_ctx_927_, lean_object* v_info_928_){
_start:
{
lean_object* v_stx_930_; lean_object* v_errorName_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_947_; 
v_stx_930_ = lean_ctor_get(v_info_928_, 0);
v_errorName_931_ = lean_ctor_get(v_info_928_, 1);
v_isSharedCheck_947_ = !lean_is_exclusive(v_info_928_);
if (v_isSharedCheck_947_ == 0)
{
v___x_933_ = v_info_928_;
v_isShared_934_ = v_isSharedCheck_947_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_errorName_931_);
lean_inc(v_stx_930_);
lean_dec(v_info_928_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_947_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_935_ = ((lean_object*)(l_Lean_Elab_ErrorNameInfo_format___closed__1));
v___x_936_ = 1;
v___x_937_ = l_Lean_Name_toString(v_errorName_931_, v___x_936_);
v___x_938_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
if (v_isShared_934_ == 0)
{
lean_ctor_set_tag(v___x_933_, 5);
lean_ctor_set(v___x_933_, 1, v___x_938_);
lean_ctor_set(v___x_933_, 0, v___x_935_);
v___x_940_ = v___x_933_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v___x_938_);
v___x_940_ = v_reuseFailAlloc_946_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_941_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_927_, v_stx_930_);
lean_dec(v_stx_930_);
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format___boxed(lean_object* v_ctx_948_, lean_object* v_info_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_948_, v_info_949_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0(lean_object* v_val_958_, lean_object* v_fieldName_959_, lean_object* v_ctx_960_, lean_object* v_stx_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; 
lean_inc(v___y_965_);
lean_inc_ref(v___y_964_);
lean_inc(v___y_963_);
lean_inc_ref(v___y_962_);
lean_inc_ref(v_val_958_);
v___x_967_ = lean_infer_type(v_val_958_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_969_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v___x_969_ = l_Lean_Meta_ppExpr(v_a_968_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_1000_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_1000_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_1000_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_Meta_ppExpr(v_val_958_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_999_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_999_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_999_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_999_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; uint8_t v___x_980_; lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_979_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__1));
v___x_980_ = 1;
v___x_981_ = l_Lean_Name_toString(v_fieldName_959_, v___x_980_);
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 3);
lean_ctor_set(v___x_972_, 0, v___x_981_);
v___x_983_ = v___x_972_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_998_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_979_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v_a_970_);
v___x_988_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__3));
v___x_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v_a_975_);
v___x_991_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_960_, v_stx_961_);
v___x_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_994_);
v___x_996_ = v___x_977_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
else
{
lean_del_object(v___x_972_);
lean_dec(v_a_970_);
lean_dec_ref(v_ctx_960_);
lean_dec(v_fieldName_959_);
return v___x_974_;
}
}
}
else
{
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec_ref(v_ctx_960_);
lean_dec(v_fieldName_959_);
lean_dec_ref(v_val_958_);
return v___x_969_;
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec_ref(v_ctx_960_);
lean_dec(v_fieldName_959_);
lean_dec_ref(v_val_958_);
v_a_1001_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_967_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_967_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0___boxed(lean_object* v_val_1009_, lean_object* v_fieldName_1010_, lean_object* v_ctx_1011_, lean_object* v_stx_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_Elab_FieldInfo_format___lam__0(v_val_1009_, v_fieldName_1010_, v_ctx_1011_, v_stx_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v_stx_1012_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format(lean_object* v_ctx_1019_, lean_object* v_info_1020_){
_start:
{
lean_object* v_fieldName_1022_; lean_object* v_lctx_1023_; lean_object* v_val_1024_; lean_object* v_stx_1025_; lean_object* v___f_1026_; lean_object* v___x_1027_; 
v_fieldName_1022_ = lean_ctor_get(v_info_1020_, 1);
lean_inc(v_fieldName_1022_);
v_lctx_1023_ = lean_ctor_get(v_info_1020_, 2);
lean_inc_ref(v_lctx_1023_);
v_val_1024_ = lean_ctor_get(v_info_1020_, 3);
lean_inc_ref(v_val_1024_);
v_stx_1025_ = lean_ctor_get(v_info_1020_, 4);
lean_inc(v_stx_1025_);
lean_dec_ref(v_info_1020_);
lean_inc_ref(v_ctx_1019_);
v___f_1026_ = lean_alloc_closure((void*)(l_Lean_Elab_FieldInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1026_, 0, v_val_1024_);
lean_closure_set(v___f_1026_, 1, v_fieldName_1022_);
lean_closure_set(v___f_1026_, 2, v_ctx_1019_);
lean_closure_set(v___f_1026_, 3, v_stx_1025_);
v___x_1027_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1019_, v_lctx_1023_, v___f_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___boxed(lean_object* v_ctx_1028_, lean_object* v_info_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_Elab_FieldInfo_format(v_ctx_1028_, v_info_1029_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(lean_object* v_pre_1032_, lean_object* v_x_1033_, lean_object* v_x_1034_){
_start:
{
if (lean_obj_tag(v_x_1034_) == 0)
{
lean_dec(v_pre_1032_);
return v_x_1033_;
}
else
{
lean_object* v_head_1035_; lean_object* v_tail_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1045_; 
v_head_1035_ = lean_ctor_get(v_x_1034_, 0);
v_tail_1036_ = lean_ctor_get(v_x_1034_, 1);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1038_ = v_x_1034_;
v_isShared_1039_ = v_isSharedCheck_1045_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_tail_1036_);
lean_inc(v_head_1035_);
lean_dec(v_x_1034_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1045_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
lean_inc(v_pre_1032_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 5);
lean_ctor_set(v___x_1038_, 1, v_pre_1032_);
lean_ctor_set(v___x_1038_, 0, v_x_1033_);
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_x_1033_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v_pre_1032_);
v___x_1041_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v_head_1035_);
v_x_1033_ = v___x_1042_;
v_x_1034_ = v_tail_1036_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(lean_object* v_pre_1046_, lean_object* v_x_1047_){
_start:
{
if (lean_obj_tag(v_x_1047_) == 0)
{
lean_object* v___x_1048_; 
lean_dec(v_pre_1046_);
v___x_1048_ = lean_box(0);
return v___x_1048_;
}
else
{
lean_object* v_head_1049_; lean_object* v_tail_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1058_; 
v_head_1049_ = lean_ctor_get(v_x_1047_, 0);
v_tail_1050_ = lean_ctor_get(v_x_1047_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1052_ = v_x_1047_;
v_isShared_1053_ = v_isSharedCheck_1058_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_tail_1050_);
lean_inc(v_head_1049_);
lean_dec(v_x_1047_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1058_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
lean_inc(v_pre_1046_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set_tag(v___x_1052_, 5);
lean_ctor_set(v___x_1052_, 1, v_head_1049_);
lean_ctor_set(v___x_1052_, 0, v_pre_1046_);
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_pre_1046_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_head_1049_);
v___x_1055_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(v_pre_1046_, v___x_1055_, v_tail_1050_);
return v___x_1056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(lean_object* v_x_1059_, lean_object* v_x_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
if (lean_obj_tag(v_x_1059_) == 0)
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = l_List_reverse___redArg(v_x_1060_);
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
return v___x_1067_;
}
else
{
lean_object* v_head_1068_; lean_object* v_tail_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1087_; 
v_head_1068_ = lean_ctor_get(v_x_1059_, 0);
v_tail_1069_ = lean_ctor_get(v_x_1059_, 1);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_x_1059_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1071_ = v_x_1059_;
v_isShared_1072_ = v_isSharedCheck_1087_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_tail_1069_);
lean_inc(v_head_1068_);
lean_dec(v_x_1059_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1087_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_Meta_ppGoal(v_head_1068_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v_head_1068_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1073_, 1);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v_x_1060_);
lean_ctor_set(v___x_1071_, 0, v_a_1074_);
v___x_1076_ = v___x_1071_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1074_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_x_1060_);
v___x_1076_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
v_x_1059_ = v_tail_1069_;
v_x_1060_ = v___x_1076_;
goto _start;
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_del_object(v___x_1071_);
lean_dec(v_tail_1069_);
lean_dec(v_x_1060_);
v_a_1079_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1073_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1073_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(lean_object* v_x_1088_, lean_object* v_x_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_x_1088_, v_x_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0(lean_object* v_goals_1099_, lean_object* v___x_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_goals_1099_, v___x_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1116_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1116_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1116_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1111_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1112_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1111_, v_a_1107_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1112_);
v___x_1114_ = v___x_1109_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
v_a_1117_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1106_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1106_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(lean_object* v_goals_1125_, lean_object* v___x_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0(v_goals_1125_, v___x_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
return v_res_1132_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = lean_unsigned_to_nat(32u);
v___x_1136_ = lean_mk_empty_array_with_capacity(v___x_1135_);
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2(void){
_start:
{
size_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1138_ = ((size_t)5ULL);
v___x_1139_ = lean_unsigned_to_nat(0u);
v___x_1140_ = lean_unsigned_to_nat(32u);
v___x_1141_ = lean_mk_empty_array_with_capacity(v___x_1140_);
v___x_1142_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__1, &l_Lean_Elab_ContextInfo_ppGoals___closed__1_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1);
v___x_1143_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
lean_ctor_set(v___x_1143_, 1, v___x_1141_);
lean_ctor_set(v___x_1143_, 2, v___x_1139_);
lean_ctor_set(v___x_1143_, 3, v___x_1139_);
lean_ctor_set_usize(v___x_1143_, 4, v___x_1138_);
return v___x_1143_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1144_ = lean_box(1);
v___x_1145_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_1146_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__0, &l_Lean_Elab_ContextInfo_ppGoals___closed__0_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0);
v___x_1147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v___x_1145_);
lean_ctor_set(v___x_1147_, 2, v___x_1144_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object* v_ctx_1151_, lean_object* v_goals_1152_){
_start:
{
uint8_t v___x_1154_; 
v___x_1154_ = l_List_isEmpty___redArg(v_goals_1152_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___f_1157_; lean_object* v___x_1158_; 
v___x_1155_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_1156_ = lean_box(0);
v___f_1157_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1157_, 0, v_goals_1152_);
lean_closure_set(v___f_1157_, 1, v___x_1156_);
v___x_1158_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1151_, v___x_1155_, v___f_1157_);
return v___x_1158_;
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_dec(v_goals_1152_);
lean_dec_ref(v_ctx_1151_);
v___x_1159_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___closed__5));
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
return v___x_1160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object* v_ctx_1161_, lean_object* v_goals_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctx_1161_, v_goals_1162_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format(lean_object* v_ctx_1174_, lean_object* v_info_1175_){
_start:
{
lean_object* v_toCommandContextInfo_1177_; lean_object* v_parentDecl_x3f_1178_; lean_object* v_autoImplicits_1179_; lean_object* v_env_1180_; lean_object* v_cmdEnv_x3f_1181_; lean_object* v_fileMap_1182_; lean_object* v_options_1183_; lean_object* v_currNamespace_1184_; lean_object* v_openDecls_1185_; lean_object* v_ngen_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1228_; 
v_toCommandContextInfo_1177_ = lean_ctor_get(v_ctx_1174_, 0);
lean_inc_ref(v_toCommandContextInfo_1177_);
v_parentDecl_x3f_1178_ = lean_ctor_get(v_ctx_1174_, 1);
v_autoImplicits_1179_ = lean_ctor_get(v_ctx_1174_, 2);
v_env_1180_ = lean_ctor_get(v_toCommandContextInfo_1177_, 0);
v_cmdEnv_x3f_1181_ = lean_ctor_get(v_toCommandContextInfo_1177_, 1);
v_fileMap_1182_ = lean_ctor_get(v_toCommandContextInfo_1177_, 2);
v_options_1183_ = lean_ctor_get(v_toCommandContextInfo_1177_, 4);
v_currNamespace_1184_ = lean_ctor_get(v_toCommandContextInfo_1177_, 5);
v_openDecls_1185_ = lean_ctor_get(v_toCommandContextInfo_1177_, 6);
v_ngen_1186_ = lean_ctor_get(v_toCommandContextInfo_1177_, 7);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_toCommandContextInfo_1177_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; 
v_unused_1229_ = lean_ctor_get(v_toCommandContextInfo_1177_, 3);
lean_dec(v_unused_1229_);
v___x_1188_ = v_toCommandContextInfo_1177_;
v_isShared_1189_ = v_isSharedCheck_1228_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_ngen_1186_);
lean_inc(v_openDecls_1185_);
lean_inc(v_currNamespace_1184_);
lean_inc(v_options_1183_);
lean_inc(v_fileMap_1182_);
lean_inc(v_cmdEnv_x3f_1181_);
lean_inc(v_env_1180_);
lean_dec(v_toCommandContextInfo_1177_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1228_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_toElabInfo_1190_; lean_object* v_mctxBefore_1191_; lean_object* v_goalsBefore_1192_; lean_object* v_mctxAfter_1193_; lean_object* v_goalsAfter_1194_; lean_object* v___x_1196_; 
v_toElabInfo_1190_ = lean_ctor_get(v_info_1175_, 0);
lean_inc_ref(v_toElabInfo_1190_);
v_mctxBefore_1191_ = lean_ctor_get(v_info_1175_, 1);
lean_inc_ref(v_mctxBefore_1191_);
v_goalsBefore_1192_ = lean_ctor_get(v_info_1175_, 2);
lean_inc(v_goalsBefore_1192_);
v_mctxAfter_1193_ = lean_ctor_get(v_info_1175_, 3);
lean_inc_ref(v_mctxAfter_1193_);
v_goalsAfter_1194_ = lean_ctor_get(v_info_1175_, 4);
lean_inc(v_goalsAfter_1194_);
lean_dec_ref(v_info_1175_);
lean_inc_ref(v_ngen_1186_);
lean_inc(v_openDecls_1185_);
lean_inc(v_currNamespace_1184_);
lean_inc_ref(v_options_1183_);
lean_inc_ref(v_fileMap_1182_);
lean_inc(v_cmdEnv_x3f_1181_);
lean_inc_ref(v_env_1180_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 3, v_mctxBefore_1191_);
v___x_1196_ = v___x_1188_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_env_1180_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_cmdEnv_x3f_1181_);
lean_ctor_set(v_reuseFailAlloc_1227_, 2, v_fileMap_1182_);
lean_ctor_set(v_reuseFailAlloc_1227_, 3, v_mctxBefore_1191_);
lean_ctor_set(v_reuseFailAlloc_1227_, 4, v_options_1183_);
lean_ctor_set(v_reuseFailAlloc_1227_, 5, v_currNamespace_1184_);
lean_ctor_set(v_reuseFailAlloc_1227_, 6, v_openDecls_1185_);
lean_ctor_set(v_reuseFailAlloc_1227_, 7, v_ngen_1186_);
v___x_1196_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v_ctxB_1197_; lean_object* v___x_1198_; lean_object* v_ctxA_1199_; lean_object* v___x_1200_; 
lean_inc_ref_n(v_autoImplicits_1179_, 2);
lean_inc_n(v_parentDecl_x3f_1178_, 2);
v_ctxB_1197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxB_1197_, 0, v___x_1196_);
lean_ctor_set(v_ctxB_1197_, 1, v_parentDecl_x3f_1178_);
lean_ctor_set(v_ctxB_1197_, 2, v_autoImplicits_1179_);
v___x_1198_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1198_, 0, v_env_1180_);
lean_ctor_set(v___x_1198_, 1, v_cmdEnv_x3f_1181_);
lean_ctor_set(v___x_1198_, 2, v_fileMap_1182_);
lean_ctor_set(v___x_1198_, 3, v_mctxAfter_1193_);
lean_ctor_set(v___x_1198_, 4, v_options_1183_);
lean_ctor_set(v___x_1198_, 5, v_currNamespace_1184_);
lean_ctor_set(v___x_1198_, 6, v_openDecls_1185_);
lean_ctor_set(v___x_1198_, 7, v_ngen_1186_);
v_ctxA_1199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxA_1199_, 0, v___x_1198_);
lean_ctor_set(v_ctxA_1199_, 1, v_parentDecl_x3f_1178_);
lean_ctor_set(v_ctxA_1199_, 2, v_autoImplicits_1179_);
v___x_1200_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxB_1197_, v_goalsBefore_1192_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1202_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1201_);
lean_dec_ref_known(v___x_1200_, 1);
v___x_1202_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxA_1199_, v_goalsAfter_1194_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1226_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1226_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1226_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v_stx_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; 
v_stx_1207_ = lean_ctor_get(v_toElabInfo_1190_, 1);
lean_inc(v_stx_1207_);
v___x_1208_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__1));
v___x_1209_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1174_, v_toElabInfo_1190_);
v___x_1210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1208_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
v___x_1211_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = lean_box(0);
v___x_1214_ = 0;
v___x_1215_ = l_Lean_Syntax_formatStx(v_stx_1207_, v___x_1213_, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1212_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v___x_1217_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__3));
v___x_1218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1216_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v_a_1201_);
v___x_1220_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__5));
v___x_1221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v_a_1203_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1222_);
v___x_1224_ = v___x_1205_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
else
{
lean_dec(v_a_1201_);
lean_dec_ref(v_toElabInfo_1190_);
lean_dec_ref(v_ctx_1174_);
return v___x_1202_;
}
}
else
{
lean_dec_ref_known(v_ctxA_1199_, 3);
lean_dec(v_goalsAfter_1194_);
lean_dec_ref(v_toElabInfo_1190_);
lean_dec_ref(v_ctx_1174_);
return v___x_1200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format___boxed(lean_object* v_ctx_1230_, lean_object* v_info_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_Elab_TacticInfo_format(v_ctx_1230_, v_info_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object* v_ctx_1240_, lean_object* v_info_1241_){
_start:
{
lean_object* v_lctx_1243_; lean_object* v_stx_1244_; lean_object* v_output_1245_; lean_object* v___x_1246_; lean_object* v_a_1247_; lean_object* v___x_1248_; lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1261_; 
v_lctx_1243_ = lean_ctor_get(v_info_1241_, 0);
lean_inc_ref_n(v_lctx_1243_, 2);
v_stx_1244_ = lean_ctor_get(v_info_1241_, 1);
lean_inc(v_stx_1244_);
v_output_1245_ = lean_ctor_get(v_info_1241_, 2);
lean_inc(v_output_1245_);
lean_dec_ref(v_info_1241_);
v___x_1246_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1240_, v_lctx_1243_, v_stx_1244_);
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref(v___x_1246_);
v___x_1248_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1240_, v_lctx_1243_, v_output_1245_);
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1261_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1261_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1253_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__1));
v___x_1254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
lean_ctor_set(v___x_1254_, 1, v_a_1247_);
v___x_1255_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__3));
v___x_1256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1254_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set(v___x_1257_, 1, v_a_1249_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1257_);
v___x_1259_ = v___x_1251_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object* v_ctx_1262_, lean_object* v_info_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1262_, v_info_1263_);
lean_dec_ref(v_ctx_1262_);
return v_res_1265_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__0(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7);
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
return v___x_1267_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__1(void){
_start:
{
uint8_t v___x_1268_; size_t v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1268_ = 1;
v___x_1269_ = ((size_t)0ULL);
v___x_1270_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__0, &l_Lean_Elab_UserWidgetInfo_format___closed__0_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__0);
v___x_1271_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
lean_ctor_set_usize(v___x_1271_, 2, v___x_1269_);
lean_ctor_set_uint8(v___x_1271_, sizeof(void*)*3, v___x_1268_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_UserWidgetInfo_format(lean_object* v_info_1275_){
_start:
{
lean_object* v_toWidgetInstance_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1305_; 
v_toWidgetInstance_1276_ = lean_ctor_get(v_info_1275_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_info_1275_);
if (v_isSharedCheck_1305_ == 0)
{
lean_object* v_unused_1306_; 
v_unused_1306_ = lean_ctor_get(v_info_1275_, 1);
lean_dec(v_unused_1306_);
v___x_1278_ = v_info_1275_;
v_isShared_1279_ = v_isSharedCheck_1305_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_toWidgetInstance_1276_);
lean_dec(v_info_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1305_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v_id_1280_; lean_object* v_props_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v_fst_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1303_; 
v_id_1280_ = lean_ctor_get(v_toWidgetInstance_1276_, 0);
lean_inc(v_id_1280_);
v_props_1281_ = lean_ctor_get(v_toWidgetInstance_1276_, 1);
lean_inc_ref(v_props_1281_);
lean_dec_ref(v_toWidgetInstance_1276_);
v___x_1282_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__1, &l_Lean_Elab_UserWidgetInfo_format___closed__1_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__1);
v___x_1283_ = lean_apply_1(v_props_1281_, v___x_1282_);
v_fst_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1303_ == 0)
{
lean_object* v_unused_1304_; 
v_unused_1304_ = lean_ctor_get(v___x_1283_, 1);
lean_dec(v_unused_1304_);
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1303_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_fst_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1303_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1288_ = ((lean_object*)(l_Lean_Elab_UserWidgetInfo_format___closed__3));
v___x_1289_ = 1;
v___x_1290_ = l_Lean_Name_toString(v_id_1280_, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set_tag(v___x_1286_, 5);
lean_ctor_set(v___x_1286_, 1, v___x_1291_);
lean_ctor_set(v___x_1286_, 0, v___x_1288_);
v___x_1293_ = v___x_1286_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1294_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
if (v_isShared_1279_ == 0)
{
lean_ctor_set_tag(v___x_1278_, 5);
lean_ctor_set(v___x_1278_, 1, v___x_1294_);
lean_ctor_set(v___x_1278_, 0, v___x_1293_);
v___x_1296_ = v___x_1278_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1297_ = lean_unsigned_to_nat(80u);
v___x_1298_ = l_Lean_Json_pretty(v_fst_1284_, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
v___x_1300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1296_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
return v___x_1300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FVarAliasInfo_format(lean_object* v_info_1313_){
_start:
{
lean_object* v_userName_1314_; lean_object* v_id_1315_; lean_object* v_baseId_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_userName_1314_ = lean_ctor_get(v_info_1313_, 0);
lean_inc(v_userName_1314_);
v_id_1315_ = lean_ctor_get(v_info_1313_, 1);
lean_inc(v_id_1315_);
v_baseId_1316_ = lean_ctor_get(v_info_1313_, 2);
lean_inc(v_baseId_1316_);
lean_dec_ref(v_info_1313_);
v___x_1317_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__1));
v___x_1318_ = l_Lean_Name_eraseMacroScopes(v_userName_1314_);
lean_dec(v_userName_1314_);
v___x_1319_ = 1;
v___x_1320_ = l_Lean_Name_toString(v___x_1318_, v___x_1319_);
v___x_1321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
v___x_1322_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1317_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___x_1323_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_1324_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1322_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
v___x_1325_ = l_Lean_Name_toString(v_id_1315_, v___x_1319_);
v___x_1326_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
v___x_1327_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1324_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v___x_1328_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__3));
v___x_1329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1327_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = l_Lean_Name_toString(v_baseId_1316_, v___x_1319_);
v___x_1331_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
v___x_1332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1329_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format(lean_object* v_ctx_1336_, lean_object* v_info_1337_){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = ((lean_object*)(l_Lean_Elab_FieldRedeclInfo_format___closed__1));
v___x_1339_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1336_, v_info_1337_);
v___x_1340_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1338_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format___boxed(lean_object* v_ctx_1341_, lean_object* v_info_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1341_, v_info_1342_);
lean_dec(v_info_1342_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f(lean_object* v_ppCtx_1346_, lean_object* v_info_1347_){
_start:
{
lean_object* v_mkDocString_x3f_1349_; 
v_mkDocString_x3f_1349_ = lean_ctor_get(v_info_1347_, 2);
lean_inc(v_mkDocString_x3f_1349_);
lean_dec_ref(v_info_1347_);
if (lean_obj_tag(v_mkDocString_x3f_1349_) == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_dec_ref(v_ppCtx_1346_);
v___x_1350_ = lean_box(0);
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
return v___x_1351_;
}
else
{
lean_object* v_val_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1384_; 
v_val_1352_ = lean_ctor_get(v_mkDocString_x3f_1349_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_mkDocString_x3f_1349_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1354_ = v_mkDocString_x3f_1349_;
v_isShared_1355_ = v_isSharedCheck_1384_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_val_1352_);
lean_dec(v_mkDocString_x3f_1349_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1384_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_apply_2(v_val_1352_, v_ppCtx_1346_, lean_box(0));
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1367_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1367_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1367_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v_a_1357_);
v___x_1362_ = v___x_1354_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1364_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1362_);
v___x_1364_ = v___x_1359_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1383_; 
v_a_1368_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1370_ = v___x_1356_;
v_isShared_1371_ = v_isSharedCheck_1383_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1356_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1383_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1372_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0));
v___x_1373_ = lean_io_error_to_string(v_a_1368_);
v___x_1374_ = lean_string_append(v___x_1372_, v___x_1373_);
lean_dec_ref(v___x_1373_);
v___x_1375_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1376_ = lean_string_append(v___x_1374_, v___x_1375_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1376_);
v___x_1378_ = v___x_1354_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_object* v___x_1380_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set_tag(v___x_1370_, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1378_);
v___x_1380_ = v___x_1370_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___boxed(lean_object* v_ppCtx_1385_, lean_object* v_info_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_ppCtx_1385_, v_info_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(lean_object* v_x_1389_, lean_object* v_x_1390_){
_start:
{
if (lean_obj_tag(v_x_1389_) == 0)
{
lean_object* v___x_1391_; 
v___x_1391_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_1391_;
}
else
{
lean_object* v_val_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1403_; 
v_val_1392_ = lean_ctor_get(v_x_1389_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1394_ = v_x_1389_;
v_isShared_1395_ = v_isSharedCheck_1403_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_val_1392_);
lean_dec(v_x_1389_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1403_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1396_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_1397_ = l_String_quote(v_val_1392_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set_tag(v___x_1394_, 3);
lean_ctor_set(v___x_1394_, 0, v___x_1397_);
v___x_1399_ = v___x_1394_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1396_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
v___x_1401_ = l_Repr_addAppParen(v___x_1400_, v_x_1390_);
return v___x_1401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(lean_object* v_x_1404_, lean_object* v_x_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_x_1404_, v_x_1405_);
lean_dec(v_x_1405_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object* v_ctx_1421_, lean_object* v_info_1422_){
_start:
{
lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v_toTermInfo_1430_; lean_object* v_location_x3f_1431_; uint8_t v_explicit_1432_; lean_object* v___y_1434_; 
v_toTermInfo_1430_ = lean_ctor_get(v_info_1422_, 0);
lean_inc_ref(v_toTermInfo_1430_);
v_location_x3f_1431_ = lean_ctor_get(v_info_1422_, 1);
lean_inc(v_location_x3f_1431_);
v_explicit_1432_ = lean_ctor_get_uint8(v_info_1422_, sizeof(void*)*3);
if (lean_obj_tag(v_location_x3f_1431_) == 1)
{
lean_object* v_val_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1516_; 
v_val_1455_ = lean_ctor_get(v_location_x3f_1431_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_location_x3f_1431_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1457_ = v_location_x3f_1431_;
v_isShared_1458_ = v_isSharedCheck_1516_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_val_1455_);
lean_dec(v_location_x3f_1431_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1516_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v_range_1459_; lean_object* v_pos_1460_; lean_object* v_endPos_1461_; lean_object* v_module_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1514_; 
v_range_1459_ = lean_ctor_get(v_val_1455_, 1);
v_pos_1460_ = lean_ctor_get(v_range_1459_, 0);
lean_inc_ref(v_pos_1460_);
v_endPos_1461_ = lean_ctor_get(v_range_1459_, 2);
lean_inc_ref(v_endPos_1461_);
v_module_1462_ = lean_ctor_get(v_val_1455_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v_val_1455_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; 
v_unused_1515_ = lean_ctor_get(v_val_1455_, 1);
lean_dec(v_unused_1515_);
v___x_1464_ = v_val_1455_;
v_isShared_1465_ = v_isSharedCheck_1514_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_module_1462_);
lean_dec(v_val_1455_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1514_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v_line_1466_; lean_object* v_column_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1513_; 
v_line_1466_ = lean_ctor_get(v_pos_1460_, 0);
v_column_1467_ = lean_ctor_get(v_pos_1460_, 1);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_pos_1460_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1469_ = v_pos_1460_;
v_isShared_1470_ = v_isSharedCheck_1513_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_column_1467_);
lean_inc(v_line_1466_);
lean_dec(v_pos_1460_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1513_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v_line_1471_; lean_object* v_column_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1512_; 
v_line_1471_ = lean_ctor_get(v_endPos_1461_, 0);
v_column_1472_ = lean_ctor_get(v_endPos_1461_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_endPos_1461_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1474_ = v_endPos_1461_;
v_isShared_1475_ = v_isSharedCheck_1512_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_column_1472_);
lean_inc(v_line_1471_);
lean_dec(v_endPos_1461_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1512_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
uint8_t v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
v___x_1476_ = 1;
v___x_1477_ = l_Lean_Name_toString(v_module_1462_, v___x_1476_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set_tag(v___x_1457_, 3);
lean_ctor_set(v___x_1457_, 0, v___x_1477_);
v___x_1479_ = v___x_1457_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1480_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
if (v_isShared_1475_ == 0)
{
lean_ctor_set_tag(v___x_1474_, 5);
lean_ctor_set(v___x_1474_, 1, v___x_1480_);
lean_ctor_set(v___x_1474_, 0, v___x_1479_);
v___x_1482_ = v___x_1474_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1483_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_1484_ = l_Nat_reprFast(v_line_1466_);
v___x_1485_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set_tag(v___x_1469_, 5);
lean_ctor_set(v___x_1469_, 1, v___x_1485_);
lean_ctor_set(v___x_1469_, 0, v___x_1483_);
v___x_1487_ = v___x_1469_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1488_; lean_object* v___x_1490_; 
v___x_1488_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
if (v_isShared_1465_ == 0)
{
lean_ctor_set_tag(v___x_1464_, 5);
lean_ctor_set(v___x_1464_, 1, v___x_1488_);
lean_ctor_set(v___x_1464_, 0, v___x_1487_);
v___x_1490_ = v___x_1464_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1491_ = l_Nat_reprFast(v_column_1467_);
v___x_1492_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
v___x_1493_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1490_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v___x_1495_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1493_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1482_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_1498_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1496_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v___x_1499_ = l_Nat_reprFast(v_line_1471_);
v___x_1500_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
v___x_1501_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1483_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
v___x_1502_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
lean_ctor_set(v___x_1502_, 1, v___x_1488_);
v___x_1503_ = l_Nat_reprFast(v_column_1472_);
v___x_1504_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
v___x_1505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1502_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
v___x_1506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v___x_1494_);
v___x_1507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1498_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___y_1434_ = v___x_1507_;
goto v___jp_1433_;
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
lean_object* v___x_1517_; 
lean_dec(v_location_x3f_1431_);
v___x_1517_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
v___y_1434_ = v___x_1517_;
goto v___jp_1433_;
}
v___jp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_inc_ref(v___y_1426_);
v___x_1427_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___y_1426_);
v___x_1428_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___y_1425_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
return v___x_1429_;
}
v___jp_1433_:
{
lean_object* v_lctx_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v_a_1438_; lean_object* v___x_1439_; 
v_lctx_1435_ = lean_ctor_get(v_toTermInfo_1430_, 1);
lean_inc_ref(v_lctx_1435_);
v___x_1436_ = l_Lean_Elab_ContextInfo_toPPContext(v_ctx_1421_, v_lctx_1435_);
v___x_1437_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v___x_1436_, v_info_1422_);
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref(v___x_1437_);
v___x_1439_ = l_Lean_Elab_TermInfo_format(v_ctx_1421_, v_toTermInfo_1430_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1439_, 1);
v___x_1441_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__1));
v___x_1442_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
lean_ctor_set(v___x_1442_, 1, v_a_1440_);
v___x_1443_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__3));
v___x_1444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1442_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
lean_ctor_set(v___x_1445_, 1, v___y_1434_);
v___x_1446_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__5));
v___x_1447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = lean_unsigned_to_nat(0u);
v___x_1449_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_a_1438_, v___x_1448_);
v___x_1450_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1447_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__7));
v___x_1452_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
if (v_explicit_1432_ == 0)
{
lean_object* v___x_1453_; 
v___x_1453_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__8));
v___y_1425_ = v___x_1452_;
v___y_1426_ = v___x_1453_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1454_; 
v___x_1454_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__9));
v___y_1425_ = v___x_1452_;
v___y_1426_ = v___x_1454_;
goto v___jp_1424_;
}
}
else
{
lean_dec(v_a_1438_);
lean_dec(v___y_1434_);
return v___x_1439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object* v_ctx_1518_, lean_object* v_info_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1518_, v_info_1519_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object* v_ctx_1525_, lean_object* v_info_1526_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1527_ = ((lean_object*)(l_Lean_Elab_ChoiceInfo_format___closed__1));
v___x_1528_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1525_, v_info_1526_);
v___x_1529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object* v_ctx_1533_, lean_object* v_info_1534_){
_start:
{
lean_object* v_stx_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v_stx_1535_ = lean_ctor_get(v_info_1534_, 1);
v___x_1536_ = ((lean_object*)(l_Lean_Elab_DocInfo_format___closed__1));
lean_inc(v_stx_1535_);
v___x_1537_ = l_Lean_Syntax_getKind(v_stx_1535_);
v___x_1538_ = 1;
v___x_1539_ = l_Lean_Name_toString(v___x_1537_, v___x_1538_);
v___x_1540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
v___x_1541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1536_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1541_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1533_, v_info_1534_);
v___x_1545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object* v_ctx_1555_, lean_object* v_info_1556_){
_start:
{
lean_object* v_toElabInfo_1557_; lean_object* v_name_1558_; uint8_t v_kind_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_toElabInfo_1557_ = lean_ctor_get(v_info_1556_, 0);
lean_inc_ref(v_toElabInfo_1557_);
v_name_1558_ = lean_ctor_get(v_info_1556_, 1);
lean_inc(v_name_1558_);
v_kind_1559_ = lean_ctor_get_uint8(v_info_1556_, sizeof(void*)*2);
lean_dec_ref(v_info_1556_);
v___x_1560_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__1));
v___x_1561_ = 1;
v___x_1562_ = l_Lean_Name_toString(v_name_1558_, v___x_1561_);
v___x_1563_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1560_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__3));
v___x_1566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1564_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = lean_unsigned_to_nat(0u);
v___x_1568_ = l_Lean_Elab_instReprDocElabKind_repr(v_kind_1559_, v___x_1567_);
v___x_1569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1566_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___x_1570_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__5));
v___x_1571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1555_, v_toElabInfo_1557_);
v___x_1573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object* v_ctx_1574_, lean_object* v_x_1575_){
_start:
{
switch(lean_obj_tag(v_x_1575_))
{
case 0:
{
lean_object* v_i_1577_; lean_object* v___x_1578_; 
v_i_1577_ = lean_ctor_get(v_x_1575_, 0);
lean_inc_ref(v_i_1577_);
lean_dec_ref_known(v_x_1575_, 1);
v___x_1578_ = l_Lean_Elab_TacticInfo_format(v_ctx_1574_, v_i_1577_);
return v___x_1578_;
}
case 1:
{
lean_object* v_i_1579_; lean_object* v___x_1580_; 
v_i_1579_ = lean_ctor_get(v_x_1575_, 0);
lean_inc_ref(v_i_1579_);
lean_dec_ref_known(v_x_1575_, 1);
v___x_1580_ = l_Lean_Elab_TermInfo_format(v_ctx_1574_, v_i_1579_);
return v___x_1580_;
}
case 2:
{
lean_object* v_i_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1589_; 
v_i_1581_ = lean_ctor_get(v_x_1575_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_x_1575_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1583_ = v_x_1575_;
v_isShared_1584_ = v_isSharedCheck_1589_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_i_1581_);
lean_dec(v_x_1575_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1589_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1585_ = l_Lean_Elab_PartialTermInfo_format(v_ctx_1574_, v_i_1581_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set_tag(v___x_1583_, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1585_);
v___x_1587_ = v___x_1583_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
case 3:
{
lean_object* v_i_1590_; lean_object* v___x_1591_; 
v_i_1590_ = lean_ctor_get(v_x_1575_, 0);
lean_inc_ref(v_i_1590_);
lean_dec_ref_known(v_x_1575_, 1);
v___x_1591_ = l_Lean_Elab_CommandInfo_format(v_ctx_1574_, v_i_1590_);
return v___x_1591_;
}
case 4:
{
lean_object* v_i_1592_; lean_object* v___x_1593_; 
v_i_1592_ = lean_ctor_get(v_x_1575_, 0);
lean_inc_ref(v_i_1592_);
lean_dec_ref_known(v_x_1575_, 1);
v___x_1593_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1574_, v_i_1592_);
lean_dec_ref(v_ctx_1574_);
return v___x_1593_;
}
case 5:
{
lean_object* v_i_1594_; lean_object* v___x_1595_; 
v_i_1594_ = lean_ctor_get(v_x_1575_, 0);
lean_inc_ref(v_i_1594_);
lean_dec_ref_known(v_x_1575_, 1);
v___x_1595_ = l_Lean_Elab_OptionInfo_format(v_ctx_1574_, v_i_1594_);
return v___x_1595_;
}
case 6:
{
lean_object* v_i_1596_; lean_object* v___x_1597_; 
v_i_1596_ = lean_ctor_get(v_x_1575_, 0);
lean_inc_ref(v_i_1596_);
lean_dec_ref_known(v_x_1575_, 1);
v___x_1597_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_1574_, v_i_1596_);
return v___x_1597_;
}
case 7:
{
lean_object* v_i_1598_; lean_object* v___x_1599_; 
v_i_1598_ = lean_ctor_get(v_x_1575_, 0);
lean_inc_ref(v_i_1598_);
lean_dec_ref_known(v_x_1575_, 1);
v___x_1599_ = l_Lean_Elab_FieldInfo_format(v_ctx_1574_, v_i_1598_);
return v___x_1599_;
}
case 8:
{
lean_object* v_i_1600_; lean_object* v___x_1601_; 
v_i_1600_ = lean_ctor_get(v_x_1575_, 0);
lean_inc_ref(v_i_1600_);
lean_dec_ref_known(v_x_1575_, 1);
v___x_1601_ = l_Lean_Elab_CompletionInfo_format(v_ctx_1574_, v_i_1600_);
return v___x_1601_;
}
case 9:
{
lean_object* v_i_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1610_; 
lean_dec_ref(v_ctx_1574_);
v_i_1602_ = lean_ctor_get(v_x_1575_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_x_1575_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1604_ = v_x_1575_;
v_isShared_1605_ = v_isSharedCheck_1610_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_i_1602_);
lean_dec(v_x_1575_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1610_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1606_ = l_Lean_Elab_UserWidgetInfo_format(v_i_1602_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set_tag(v___x_1604_, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1606_);
v___x_1608_ = v___x_1604_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
case 10:
{
lean_object* v_i_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1619_; 
lean_dec_ref(v_ctx_1574_);
v_i_1611_ = lean_ctor_get(v_x_1575_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_x_1575_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1613_ = v_x_1575_;
v_isShared_1614_ = v_isSharedCheck_1619_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_i_1611_);
lean_dec(v_x_1575_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1619_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1615_ = l_Lean_Elab_CustomInfo_format(v_i_1611_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set_tag(v___x_1613_, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1615_);
v___x_1617_ = v___x_1613_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
case 11:
{
lean_object* v_i_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1628_; 
lean_dec_ref(v_ctx_1574_);
v_i_1620_ = lean_ctor_get(v_x_1575_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_x_1575_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1622_ = v_x_1575_;
v_isShared_1623_ = v_isSharedCheck_1628_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_i_1620_);
lean_dec(v_x_1575_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1628_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1624_ = l_Lean_Elab_FVarAliasInfo_format(v_i_1620_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set_tag(v___x_1622_, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1624_);
v___x_1626_ = v___x_1622_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
case 12:
{
lean_object* v_i_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1637_; 
v_i_1629_ = lean_ctor_get(v_x_1575_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_x_1575_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1631_ = v_x_1575_;
v_isShared_1632_ = v_isSharedCheck_1637_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_i_1629_);
lean_dec(v_x_1575_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1637_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1633_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1574_, v_i_1629_);
lean_dec(v_i_1629_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set_tag(v___x_1631_, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1633_);
v___x_1635_ = v___x_1631_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
case 13:
{
lean_object* v_i_1638_; lean_object* v___x_1639_; 
v_i_1638_ = lean_ctor_get(v_x_1575_, 0);
lean_inc_ref(v_i_1638_);
lean_dec_ref_known(v_x_1575_, 1);
v___x_1639_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1574_, v_i_1638_);
return v___x_1639_;
}
case 14:
{
lean_object* v_i_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1648_; 
v_i_1640_ = lean_ctor_get(v_x_1575_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_x_1575_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1642_ = v_x_1575_;
v_isShared_1643_ = v_isSharedCheck_1648_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_i_1640_);
lean_dec(v_x_1575_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1648_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1644_ = l_Lean_Elab_ChoiceInfo_format(v_ctx_1574_, v_i_1640_);
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
case 15:
{
lean_object* v_i_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1657_; 
v_i_1649_ = lean_ctor_get(v_x_1575_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_x_1575_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1651_ = v_x_1575_;
v_isShared_1652_ = v_isSharedCheck_1657_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_i_1649_);
lean_dec(v_x_1575_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1657_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1653_; lean_object* v___x_1655_; 
v___x_1653_ = l_Lean_Elab_DocInfo_format(v_ctx_1574_, v_i_1649_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set_tag(v___x_1651_, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1653_);
v___x_1655_ = v___x_1651_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
default: 
{
lean_object* v_i_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1666_; 
v_i_1658_ = lean_ctor_get(v_x_1575_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_x_1575_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1660_ = v_x_1575_;
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_i_1658_);
lean_dec(v_x_1575_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1662_ = l_Lean_Elab_DocElabInfo_format(v_ctx_1574_, v_i_1658_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object* v_ctx_1667_, lean_object* v_x_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_Elab_Info_format(v_ctx_1667_, v_x_1668_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object* v_x_1671_, lean_object* v_x_1672_){
_start:
{
if (lean_obj_tag(v_x_1672_) == 0)
{
return v_x_1671_;
}
else
{
lean_object* v_head_1673_; lean_object* v_tail_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v_head_1673_ = lean_ctor_get(v_x_1672_, 0);
v_tail_1674_ = lean_ctor_get(v_x_1672_, 1);
v___x_1675_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2));
v___x_1676_ = lean_string_append(v_x_1671_, v___x_1675_);
v___x_1677_ = lean_expr_dbg_to_string(v_head_1673_);
v___x_1678_ = lean_string_append(v___x_1676_, v___x_1677_);
lean_dec_ref(v___x_1677_);
v_x_1671_ = v___x_1678_;
v_x_1672_ = v_tail_1674_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object* v_x_1680_, lean_object* v_x_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v_x_1680_, v_x_1681_);
lean_dec(v_x_1681_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object* v_x_1685_){
_start:
{
if (lean_obj_tag(v_x_1685_) == 0)
{
lean_object* v___x_1686_; 
v___x_1686_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0));
return v___x_1686_;
}
else
{
lean_object* v_tail_1687_; 
v_tail_1687_ = lean_ctor_get(v_x_1685_, 1);
if (lean_obj_tag(v_tail_1687_) == 0)
{
lean_object* v_head_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v_head_1688_ = lean_ctor_get(v_x_1685_, 0);
v___x_1689_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1690_ = lean_expr_dbg_to_string(v_head_1688_);
v___x_1691_ = lean_string_append(v___x_1689_, v___x_1690_);
lean_dec_ref(v___x_1690_);
v___x_1692_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1693_ = lean_string_append(v___x_1691_, v___x_1692_);
return v___x_1693_;
}
else
{
lean_object* v_head_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; uint32_t v___x_1699_; lean_object* v___x_1700_; 
v_head_1694_ = lean_ctor_get(v_x_1685_, 0);
v___x_1695_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1696_ = lean_expr_dbg_to_string(v_head_1694_);
v___x_1697_ = lean_string_append(v___x_1695_, v___x_1696_);
lean_dec_ref(v___x_1696_);
v___x_1698_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v___x_1697_, v_tail_1687_);
v___x_1699_ = 93;
v___x_1700_ = lean_string_push(v___x_1698_, v___x_1699_);
return v___x_1700_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object* v_x_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v_x_1701_);
lean_dec(v_x_1701_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object* v_ctx_1709_){
_start:
{
switch(lean_obj_tag(v_ctx_1709_))
{
case 0:
{
lean_object* v___x_1710_; 
lean_dec_ref_known(v_ctx_1709_, 1);
v___x_1710_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__1));
return v___x_1710_;
}
case 1:
{
lean_object* v_parentDecl_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1724_; 
v_parentDecl_1711_ = lean_ctor_get(v_ctx_1709_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_ctx_1709_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1713_ = v_ctx_1709_;
v_isShared_1714_ = v_isSharedCheck_1724_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_parentDecl_1711_);
lean_dec(v_ctx_1709_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1724_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1715_; uint8_t v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1715_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__2));
v___x_1716_ = 1;
v___x_1717_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_parentDecl_1711_, v___x_1716_);
v___x_1718_ = lean_string_append(v___x_1715_, v___x_1717_);
lean_dec_ref(v___x_1717_);
v___x_1719_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1720_ = lean_string_append(v___x_1718_, v___x_1719_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set_tag(v___x_1713_, 3);
lean_ctor_set(v___x_1713_, 0, v___x_1720_);
v___x_1722_ = v___x_1713_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(3, 1, 0);
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
lean_object* v_autoImplicits_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1740_; 
v_autoImplicits_1725_ = lean_ctor_get(v_ctx_1709_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_ctx_1709_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1727_ = v_ctx_1709_;
v_isShared_1728_ = v_isSharedCheck_1740_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_autoImplicits_1725_);
lean_dec(v_ctx_1709_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1740_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1729_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__3));
v___x_1730_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__4));
v___x_1731_ = lean_array_to_list(v_autoImplicits_1725_);
v___x_1732_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v___x_1731_);
lean_dec(v___x_1731_);
v___x_1733_ = lean_string_append(v___x_1730_, v___x_1732_);
lean_dec_ref(v___x_1732_);
v___x_1734_ = lean_string_append(v___x_1729_, v___x_1733_);
lean_dec_ref(v___x_1733_);
v___x_1735_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1736_ = lean_string_append(v___x_1734_, v___x_1735_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set_tag(v___x_1727_, 3);
lean_ctor_set(v___x_1727_, 0, v___x_1736_);
v___x_1738_ = v___x_1727_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(3, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format(lean_object* v_tree_1750_, lean_object* v_ctx_x3f_1751_){
_start:
{
switch(lean_obj_tag(v_tree_1750_))
{
case 0:
{
lean_object* v_i_1753_; lean_object* v_t_1754_; lean_object* v___x_1755_; 
v_i_1753_ = lean_ctor_get(v_tree_1750_, 0);
lean_inc_ref(v_i_1753_);
v_t_1754_ = lean_ctor_get(v_tree_1750_, 1);
lean_inc_ref(v_t_1754_);
lean_dec_ref_known(v_tree_1750_, 2);
v___x_1755_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1753_, v_ctx_x3f_1751_);
v_tree_1750_ = v_t_1754_;
v_ctx_x3f_1751_ = v___x_1755_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_ctx_x3f_1751_) == 0)
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_dec_ref_known(v_tree_1750_, 2);
v___x_1757_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__1));
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
return v___x_1758_;
}
else
{
lean_object* v_i_1759_; lean_object* v_children_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1810_; 
v_i_1759_ = lean_ctor_get(v_tree_1750_, 0);
v_children_1760_ = lean_ctor_get(v_tree_1750_, 1);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_tree_1750_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1762_ = v_tree_1750_;
v_isShared_1763_ = v_isSharedCheck_1810_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_children_1760_);
lean_inc(v_i_1759_);
lean_dec(v_tree_1750_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1810_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v_val_1764_; lean_object* v___x_1765_; 
v_val_1764_ = lean_ctor_get(v_ctx_x3f_1751_, 0);
lean_inc_ref(v_i_1759_);
lean_inc(v_val_1764_);
v___x_1765_ = l_Lean_Elab_Info_format(v_val_1764_, v_i_1759_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1809_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1809_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1809_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v_size_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; 
v_size_1770_ = lean_ctor_get(v_children_1760_, 2);
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = lean_nat_dec_eq(v_size_1770_, v___x_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_del_object(v___x_1768_);
v___x_1773_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_1751_, v_i_1759_);
lean_dec_ref(v_i_1759_);
v___x_1774_ = l_Lean_PersistentArray_toList___redArg(v_children_1760_);
lean_dec_ref(v_children_1760_);
v___x_1775_ = lean_box(0);
v___x_1776_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1773_, v___x_1774_, v___x_1775_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1792_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1792_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1792_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1781_; lean_object* v___x_1783_; 
v___x_1781_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1763_ == 0)
{
lean_ctor_set_tag(v___x_1762_, 5);
lean_ctor_set(v___x_1762_, 1, v_a_1766_);
lean_ctor_set(v___x_1762_, 0, v___x_1781_);
v___x_1783_ = v___x_1762_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_a_1766_);
v___x_1783_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1784_ = lean_box(1);
v___x_1785_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1784_, v_a_1777_);
v___x_1786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1783_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = l_Std_Format_nestD(v___x_1786_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1787_);
v___x_1789_ = v___x_1779_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_a_1766_);
lean_del_object(v___x_1762_);
v_a_1793_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1776_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1776_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1803_; 
lean_dec_ref(v_children_1760_);
lean_dec_ref_known(v_ctx_x3f_1751_, 1);
lean_dec_ref(v_i_1759_);
v___x_1801_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1763_ == 0)
{
lean_ctor_set_tag(v___x_1762_, 5);
lean_ctor_set(v___x_1762_, 1, v_a_1766_);
lean_ctor_set(v___x_1762_, 0, v___x_1801_);
v___x_1803_ = v___x_1762_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1801_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_a_1766_);
v___x_1803_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1804_ = l_Std_Format_nestD(v___x_1803_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1804_);
v___x_1806_ = v___x_1768_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_del_object(v___x_1762_);
lean_dec_ref(v_children_1760_);
lean_dec_ref_known(v_ctx_x3f_1751_, 1);
lean_dec_ref(v_i_1759_);
return v___x_1765_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1824_; 
lean_dec(v_ctx_x3f_1751_);
v_mvarId_1811_ = lean_ctor_get(v_tree_1750_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_tree_1750_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1813_ = v_tree_1750_;
v_isShared_1814_ = v_isSharedCheck_1824_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_mvarId_1811_);
lean_dec(v_tree_1750_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1824_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; uint8_t v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1815_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__5));
v___x_1816_ = 1;
v___x_1817_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_1811_, v___x_1816_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set_tag(v___x_1813_, 3);
lean_ctor_set(v___x_1813_, 0, v___x_1817_);
v___x_1819_ = v___x_1813_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1815_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = l_Std_Format_nestD(v___x_1820_);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
return v___x_1822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object* v___x_1825_, lean_object* v_x_1826_, lean_object* v_x_1827_){
_start:
{
if (lean_obj_tag(v_x_1826_) == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_dec(v___x_1825_);
v___x_1829_ = l_List_reverse___redArg(v_x_1827_);
v___x_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
return v___x_1830_;
}
else
{
lean_object* v_head_1831_; lean_object* v_tail_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1850_; 
v_head_1831_ = lean_ctor_get(v_x_1826_, 0);
v_tail_1832_ = lean_ctor_get(v_x_1826_, 1);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_x_1826_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1834_ = v_x_1826_;
v_isShared_1835_ = v_isSharedCheck_1850_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_tail_1832_);
lean_inc(v_head_1831_);
lean_dec(v_x_1826_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1850_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; 
lean_inc(v___x_1825_);
v___x_1836_ = l_Lean_Elab_InfoTree_format(v_head_1831_, v___x_1825_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref_known(v___x_1836_, 1);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v_x_1827_);
lean_ctor_set(v___x_1834_, 0, v_a_1837_);
v___x_1839_ = v___x_1834_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1837_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_x_1827_);
v___x_1839_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
v_x_1826_ = v_tail_1832_;
v_x_1827_ = v___x_1839_;
goto _start;
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_del_object(v___x_1834_);
lean_dec(v_tail_1832_);
lean_dec(v_x_1827_);
lean_dec(v___x_1825_);
v_a_1842_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1836_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1836_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object* v___x_1851_, lean_object* v_x_1852_, lean_object* v_x_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1851_, v_x_1852_, v_x_1853_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object* v_tree_1856_, lean_object* v_ctx_x3f_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_Elab_InfoTree_format(v_tree_1856_, v_ctx_x3f_1857_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object* v_f_1860_, lean_object* v_s_1861_){
_start:
{
uint8_t v_enabled_1862_; lean_object* v_assignment_1863_; lean_object* v_lazyAssignment_1864_; lean_object* v_trees_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1873_; 
v_enabled_1862_ = lean_ctor_get_uint8(v_s_1861_, sizeof(void*)*3);
v_assignment_1863_ = lean_ctor_get(v_s_1861_, 0);
v_lazyAssignment_1864_ = lean_ctor_get(v_s_1861_, 1);
v_trees_1865_ = lean_ctor_get(v_s_1861_, 2);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_s_1861_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1867_ = v_s_1861_;
v_isShared_1868_ = v_isSharedCheck_1873_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_trees_1865_);
lean_inc(v_lazyAssignment_1864_);
lean_inc(v_assignment_1863_);
lean_dec(v_s_1861_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1873_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
v___x_1869_ = lean_apply_1(v_f_1860_, v_trees_1865_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 2, v___x_1869_);
v___x_1871_ = v___x_1867_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_assignment_1863_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_lazyAssignment_1864_);
lean_ctor_set(v_reuseFailAlloc_1872_, 2, v___x_1869_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, sizeof(void*)*3, v_enabled_1862_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object* v_inst_1874_, lean_object* v_f_1875_){
_start:
{
lean_object* v_modifyInfoState_1876_; lean_object* v___f_1877_; lean_object* v___x_1878_; 
v_modifyInfoState_1876_ = lean_ctor_get(v_inst_1874_, 1);
lean_inc(v_modifyInfoState_1876_);
lean_dec_ref(v_inst_1874_);
v___f_1877_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1877_, 0, v_f_1875_);
v___x_1878_ = lean_apply_1(v_modifyInfoState_1876_, v___f_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object* v_m_1879_, lean_object* v_inst_1880_, lean_object* v_f_1881_){
_start:
{
lean_object* v_modifyInfoState_1882_; lean_object* v___f_1883_; lean_object* v___x_1884_; 
v_modifyInfoState_1882_ = lean_ctor_get(v_inst_1880_, 1);
lean_inc(v_modifyInfoState_1882_);
lean_dec_ref(v_inst_1880_);
v___f_1883_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1883_, 0, v_f_1881_);
v___x_1884_ = lean_apply_1(v_modifyInfoState_1882_, v___f_1883_);
return v___x_1884_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1885_ = lean_unsigned_to_nat(32u);
v___x_1886_ = lean_mk_empty_array_with_capacity(v___x_1885_);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
return v___x_1887_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1888_ = ((size_t)5ULL);
v___x_1889_ = lean_unsigned_to_nat(0u);
v___x_1890_ = lean_unsigned_to_nat(32u);
v___x_1891_ = lean_mk_empty_array_with_capacity(v___x_1890_);
v___x_1892_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0);
v___x_1893_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v___x_1891_);
lean_ctor_set(v___x_1893_, 2, v___x_1889_);
lean_ctor_set(v___x_1893_, 3, v___x_1889_);
lean_ctor_set_usize(v___x_1893_, 4, v___x_1888_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object* v_s_1894_){
_start:
{
uint8_t v_enabled_1895_; lean_object* v_assignment_1896_; lean_object* v_lazyAssignment_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1905_; 
v_enabled_1895_ = lean_ctor_get_uint8(v_s_1894_, sizeof(void*)*3);
v_assignment_1896_ = lean_ctor_get(v_s_1894_, 0);
v_lazyAssignment_1897_ = lean_ctor_get(v_s_1894_, 1);
v_isSharedCheck_1905_ = !lean_is_exclusive(v_s_1894_);
if (v_isSharedCheck_1905_ == 0)
{
lean_object* v_unused_1906_; 
v_unused_1906_ = lean_ctor_get(v_s_1894_, 2);
lean_dec(v_unused_1906_);
v___x_1899_ = v_s_1894_;
v_isShared_1900_ = v_isSharedCheck_1905_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_lazyAssignment_1897_);
lean_inc(v_assignment_1896_);
lean_dec(v_s_1894_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1905_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1901_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 2, v___x_1901_);
v___x_1903_ = v___x_1899_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_assignment_1896_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_lazyAssignment_1897_);
lean_ctor_set(v_reuseFailAlloc_1904_, 2, v___x_1901_);
lean_ctor_set_uint8(v_reuseFailAlloc_1904_, sizeof(void*)*3, v_enabled_1895_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object* v_toPure_1907_, lean_object* v_trees_1908_, lean_object* v_____r_1909_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_apply_2(v_toPure_1907_, lean_box(0), v_trees_1908_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object* v_toPure_1911_, lean_object* v_modifyInfoState_1912_, lean_object* v___f_1913_, lean_object* v_toBind_1914_, lean_object* v_____do__lift_1915_){
_start:
{
lean_object* v_trees_1916_; lean_object* v___f_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v_trees_1916_ = lean_ctor_get(v_____do__lift_1915_, 2);
lean_inc_ref(v_trees_1916_);
lean_dec_ref(v_____do__lift_1915_);
v___f_1917_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1917_, 0, v_toPure_1911_);
lean_closure_set(v___f_1917_, 1, v_trees_1916_);
v___x_1918_ = lean_apply_1(v_modifyInfoState_1912_, v___f_1913_);
v___x_1919_ = lean_apply_4(v_toBind_1914_, lean_box(0), lean_box(0), v___x_1918_, v___f_1917_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object* v_inst_1921_, lean_object* v_inst_1922_){
_start:
{
lean_object* v_toApplicative_1923_; lean_object* v_toBind_1924_; lean_object* v_getInfoState_1925_; lean_object* v_modifyInfoState_1926_; lean_object* v_toPure_1927_; lean_object* v___f_1928_; lean_object* v___f_1929_; lean_object* v___x_1930_; 
v_toApplicative_1923_ = lean_ctor_get(v_inst_1921_, 0);
lean_inc_ref(v_toApplicative_1923_);
v_toBind_1924_ = lean_ctor_get(v_inst_1921_, 1);
lean_inc_n(v_toBind_1924_, 2);
lean_dec_ref(v_inst_1921_);
v_getInfoState_1925_ = lean_ctor_get(v_inst_1922_, 0);
lean_inc(v_getInfoState_1925_);
v_modifyInfoState_1926_ = lean_ctor_get(v_inst_1922_, 1);
lean_inc(v_modifyInfoState_1926_);
lean_dec_ref(v_inst_1922_);
v_toPure_1927_ = lean_ctor_get(v_toApplicative_1923_, 1);
lean_inc(v_toPure_1927_);
lean_dec_ref(v_toApplicative_1923_);
v___f_1928_ = ((lean_object*)(l_Lean_Elab_getResetInfoTrees___redArg___closed__0));
v___f_1929_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1929_, 0, v_toPure_1927_);
lean_closure_set(v___f_1929_, 1, v_modifyInfoState_1926_);
lean_closure_set(v___f_1929_, 2, v___f_1928_);
lean_closure_set(v___f_1929_, 3, v_toBind_1924_);
v___x_1930_ = lean_apply_4(v_toBind_1924_, lean_box(0), lean_box(0), v_getInfoState_1925_, v___f_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object* v_m_1931_, lean_object* v_inst_1932_, lean_object* v_inst_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_1932_, v_inst_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object* v_t_1935_, lean_object* v_s_1936_){
_start:
{
uint8_t v_enabled_1937_; lean_object* v_assignment_1938_; lean_object* v_lazyAssignment_1939_; lean_object* v_trees_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1948_; 
v_enabled_1937_ = lean_ctor_get_uint8(v_s_1936_, sizeof(void*)*3);
v_assignment_1938_ = lean_ctor_get(v_s_1936_, 0);
v_lazyAssignment_1939_ = lean_ctor_get(v_s_1936_, 1);
v_trees_1940_ = lean_ctor_get(v_s_1936_, 2);
v_isSharedCheck_1948_ = !lean_is_exclusive(v_s_1936_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1942_ = v_s_1936_;
v_isShared_1943_ = v_isSharedCheck_1948_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_trees_1940_);
lean_inc(v_lazyAssignment_1939_);
lean_inc(v_assignment_1938_);
lean_dec(v_s_1936_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1948_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1944_; lean_object* v___x_1946_; 
v___x_1944_ = l_Lean_PersistentArray_push___redArg(v_trees_1940_, v_t_1935_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 2, v___x_1944_);
v___x_1946_ = v___x_1942_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_assignment_1938_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_lazyAssignment_1939_);
lean_ctor_set(v_reuseFailAlloc_1947_, 2, v___x_1944_);
lean_ctor_set_uint8(v_reuseFailAlloc_1947_, sizeof(void*)*3, v_enabled_1937_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object* v_toPure_1949_, lean_object* v_modifyInfoState_1950_, lean_object* v___f_1951_, lean_object* v_____do__lift_1952_){
_start:
{
uint8_t v_enabled_1953_; 
v_enabled_1953_ = lean_ctor_get_uint8(v_____do__lift_1952_, sizeof(void*)*3);
if (v_enabled_1953_ == 0)
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec_ref(v___f_1951_);
lean_dec(v_modifyInfoState_1950_);
v___x_1954_ = lean_box(0);
v___x_1955_ = lean_apply_2(v_toPure_1949_, lean_box(0), v___x_1954_);
return v___x_1955_;
}
else
{
lean_object* v___x_1956_; 
lean_dec(v_toPure_1949_);
v___x_1956_ = lean_apply_1(v_modifyInfoState_1950_, v___f_1951_);
return v___x_1956_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object* v_toPure_1957_, lean_object* v_modifyInfoState_1958_, lean_object* v___f_1959_, lean_object* v_____do__lift_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_Elab_pushInfoTree___redArg___lam__1(v_toPure_1957_, v_modifyInfoState_1958_, v___f_1959_, v_____do__lift_1960_);
lean_dec_ref(v_____do__lift_1960_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object* v_inst_1962_, lean_object* v_inst_1963_, lean_object* v_t_1964_){
_start:
{
lean_object* v_toApplicative_1965_; lean_object* v_toBind_1966_; lean_object* v_getInfoState_1967_; lean_object* v_modifyInfoState_1968_; lean_object* v_toPure_1969_; lean_object* v___f_1970_; lean_object* v___f_1971_; lean_object* v___x_1972_; 
v_toApplicative_1965_ = lean_ctor_get(v_inst_1962_, 0);
lean_inc_ref(v_toApplicative_1965_);
v_toBind_1966_ = lean_ctor_get(v_inst_1962_, 1);
lean_inc(v_toBind_1966_);
lean_dec_ref(v_inst_1962_);
v_getInfoState_1967_ = lean_ctor_get(v_inst_1963_, 0);
lean_inc(v_getInfoState_1967_);
v_modifyInfoState_1968_ = lean_ctor_get(v_inst_1963_, 1);
lean_inc(v_modifyInfoState_1968_);
lean_dec_ref(v_inst_1963_);
v_toPure_1969_ = lean_ctor_get(v_toApplicative_1965_, 1);
lean_inc(v_toPure_1969_);
lean_dec_ref(v_toApplicative_1965_);
v___f_1970_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1970_, 0, v_t_1964_);
v___f_1971_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1971_, 0, v_toPure_1969_);
lean_closure_set(v___f_1971_, 1, v_modifyInfoState_1968_);
lean_closure_set(v___f_1971_, 2, v___f_1970_);
v___x_1972_ = lean_apply_4(v_toBind_1966_, lean_box(0), lean_box(0), v_getInfoState_1967_, v___f_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object* v_m_1973_, lean_object* v_inst_1974_, lean_object* v_inst_1975_, lean_object* v_t_1976_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_1974_, v_inst_1975_, v_t_1976_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object* v_toPure_1978_, lean_object* v_t_1979_, lean_object* v_inst_1980_, lean_object* v_inst_1981_, lean_object* v_____do__lift_1982_){
_start:
{
uint8_t v_enabled_1983_; 
v_enabled_1983_ = lean_ctor_get_uint8(v_____do__lift_1982_, sizeof(void*)*3);
if (v_enabled_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_dec_ref(v_inst_1981_);
lean_dec_ref(v_inst_1980_);
lean_dec_ref(v_t_1979_);
v___x_1984_ = lean_box(0);
v___x_1985_ = lean_apply_2(v_toPure_1978_, lean_box(0), v___x_1984_);
return v___x_1985_;
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
lean_dec(v_toPure_1978_);
v___x_1986_ = lean_unsigned_to_nat(32u);
v___x_1987_ = lean_mk_empty_array_with_capacity(v___x_1986_);
lean_dec_ref(v___x_1987_);
v___x_1988_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_1989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1989_, 0, v_t_1979_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_1980_, v_inst_1981_, v___x_1989_);
return v___x_1990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object* v_toPure_1991_, lean_object* v_t_1992_, lean_object* v_inst_1993_, lean_object* v_inst_1994_, lean_object* v_____do__lift_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_Elab_pushInfoLeaf___redArg___lam__0(v_toPure_1991_, v_t_1992_, v_inst_1993_, v_inst_1994_, v_____do__lift_1995_);
lean_dec_ref(v_____do__lift_1995_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object* v_inst_1997_, lean_object* v_inst_1998_, lean_object* v_t_1999_){
_start:
{
lean_object* v_toApplicative_2000_; lean_object* v_toBind_2001_; lean_object* v_getInfoState_2002_; lean_object* v_toPure_2003_; lean_object* v___f_2004_; lean_object* v___x_2005_; 
v_toApplicative_2000_ = lean_ctor_get(v_inst_1997_, 0);
v_toBind_2001_ = lean_ctor_get(v_inst_1997_, 1);
lean_inc(v_toBind_2001_);
v_getInfoState_2002_ = lean_ctor_get(v_inst_1998_, 0);
lean_inc(v_getInfoState_2002_);
v_toPure_2003_ = lean_ctor_get(v_toApplicative_2000_, 1);
lean_inc(v_toPure_2003_);
v___f_2004_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2004_, 0, v_toPure_2003_);
lean_closure_set(v___f_2004_, 1, v_t_1999_);
lean_closure_set(v___f_2004_, 2, v_inst_1997_);
lean_closure_set(v___f_2004_, 3, v_inst_1998_);
v___x_2005_ = lean_apply_4(v_toBind_2001_, lean_box(0), lean_box(0), v_getInfoState_2002_, v___f_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object* v_m_2006_, lean_object* v_inst_2007_, lean_object* v_inst_2008_, lean_object* v_t_2009_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2007_, v_inst_2008_, v_t_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object* v_inst_2011_, lean_object* v_inst_2012_, lean_object* v_info_2013_){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2014_, 0, v_info_2013_);
v___x_2015_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2011_, v_inst_2012_, v___x_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object* v_m_2016_, lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_info_2019_){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_2017_, v_inst_2018_, v_info_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object* v_stx_2021_, lean_object* v_expectedType_x3f_2022_, lean_object* v_inst_2023_, lean_object* v_inst_2024_, lean_object* v_____do__lift_2025_){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2026_ = lean_box(0);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
lean_ctor_set(v___x_2027_, 1, v_stx_2021_);
v___x_2028_ = l_Lean_LocalContext_empty;
v___x_2029_ = 0;
v___x_2030_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2030_, 0, v___x_2027_);
lean_ctor_set(v___x_2030_, 1, v___x_2028_);
lean_ctor_set(v___x_2030_, 2, v_expectedType_x3f_2022_);
lean_ctor_set(v___x_2030_, 3, v_____do__lift_2025_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*4, v___x_2029_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*4 + 1, v___x_2029_);
v___x_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
v___x_2032_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2023_, v_inst_2024_, v___x_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object* v_inst_2033_, lean_object* v_inst_2034_, lean_object* v_inst_2035_, lean_object* v_inst_2036_, lean_object* v_stx_2037_, lean_object* v_n_2038_, lean_object* v_expectedType_x3f_2039_){
_start:
{
lean_object* v_toBind_2040_; lean_object* v___f_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v_toBind_2040_ = lean_ctor_get(v_inst_2033_, 1);
lean_inc(v_toBind_2040_);
lean_inc_ref(v_inst_2033_);
v___f_2041_ = lean_alloc_closure((void*)(l_Lean_Elab_addConstInfo___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2041_, 0, v_stx_2037_);
lean_closure_set(v___f_2041_, 1, v_expectedType_x3f_2039_);
lean_closure_set(v___f_2041_, 2, v_inst_2033_);
lean_closure_set(v___f_2041_, 3, v_inst_2034_);
v___x_2042_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_2033_, v_inst_2035_, v_inst_2036_, v_n_2038_);
v___x_2043_ = lean_apply_4(v_toBind_2040_, lean_box(0), lean_box(0), v___x_2042_, v___f_2041_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object* v_m_2044_, lean_object* v_inst_2045_, lean_object* v_inst_2046_, lean_object* v_inst_2047_, lean_object* v_inst_2048_, lean_object* v_stx_2049_, lean_object* v_n_2050_, lean_object* v_expectedType_x3f_2051_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_Elab_addConstInfo___redArg(v_inst_2045_, v_inst_2046_, v_inst_2047_, v_inst_2048_, v_stx_2049_, v_n_2050_, v_expectedType_x3f_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v___x_2056_; lean_object* v_infoState_2057_; uint8_t v_enabled_2058_; 
v___x_2056_ = lean_st_ref_get(v___y_2054_);
v_infoState_2057_ = lean_ctor_get(v___x_2056_, 7);
lean_inc_ref(v_infoState_2057_);
lean_dec(v___x_2056_);
v_enabled_2058_ = lean_ctor_get_uint8(v_infoState_2057_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2057_);
if (v_enabled_2058_ == 0)
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
lean_dec_ref(v_t_2053_);
v___x_2059_ = lean_box(0);
v___x_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
return v___x_2060_;
}
else
{
lean_object* v___x_2061_; lean_object* v_infoState_2062_; lean_object* v_env_2063_; lean_object* v_nextMacroScope_2064_; lean_object* v_ngen_2065_; lean_object* v_auxDeclNGen_2066_; lean_object* v_traceState_2067_; lean_object* v_cache_2068_; lean_object* v_messages_2069_; lean_object* v_snapshotTasks_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2092_; 
v___x_2061_ = lean_st_ref_take(v___y_2054_);
v_infoState_2062_ = lean_ctor_get(v___x_2061_, 7);
v_env_2063_ = lean_ctor_get(v___x_2061_, 0);
v_nextMacroScope_2064_ = lean_ctor_get(v___x_2061_, 1);
v_ngen_2065_ = lean_ctor_get(v___x_2061_, 2);
v_auxDeclNGen_2066_ = lean_ctor_get(v___x_2061_, 3);
v_traceState_2067_ = lean_ctor_get(v___x_2061_, 4);
v_cache_2068_ = lean_ctor_get(v___x_2061_, 5);
v_messages_2069_ = lean_ctor_get(v___x_2061_, 6);
v_snapshotTasks_2070_ = lean_ctor_get(v___x_2061_, 8);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2072_ = v___x_2061_;
v_isShared_2073_ = v_isSharedCheck_2092_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_snapshotTasks_2070_);
lean_inc(v_infoState_2062_);
lean_inc(v_messages_2069_);
lean_inc(v_cache_2068_);
lean_inc(v_traceState_2067_);
lean_inc(v_auxDeclNGen_2066_);
lean_inc(v_ngen_2065_);
lean_inc(v_nextMacroScope_2064_);
lean_inc(v_env_2063_);
lean_dec(v___x_2061_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2092_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
uint8_t v_enabled_2074_; lean_object* v_assignment_2075_; lean_object* v_lazyAssignment_2076_; lean_object* v_trees_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2091_; 
v_enabled_2074_ = lean_ctor_get_uint8(v_infoState_2062_, sizeof(void*)*3);
v_assignment_2075_ = lean_ctor_get(v_infoState_2062_, 0);
v_lazyAssignment_2076_ = lean_ctor_get(v_infoState_2062_, 1);
v_trees_2077_ = lean_ctor_get(v_infoState_2062_, 2);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_infoState_2062_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2079_ = v_infoState_2062_;
v_isShared_2080_ = v_isSharedCheck_2091_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_trees_2077_);
lean_inc(v_lazyAssignment_2076_);
lean_inc(v_assignment_2075_);
lean_dec(v_infoState_2062_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2091_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2084_; 
v___x_2081_ = lean_box(0);
v___x_2082_ = l_Lean_PersistentArray_push___redArg(v_trees_2077_, v_t_2053_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 2, v___x_2082_);
v___x_2084_ = v___x_2079_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_assignment_2075_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_lazyAssignment_2076_);
lean_ctor_set(v_reuseFailAlloc_2090_, 2, v___x_2082_);
lean_ctor_set_uint8(v_reuseFailAlloc_2090_, sizeof(void*)*3, v_enabled_2074_);
v___x_2084_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2086_; 
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 7, v___x_2084_);
v___x_2086_ = v___x_2072_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_env_2063_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_nextMacroScope_2064_);
lean_ctor_set(v_reuseFailAlloc_2089_, 2, v_ngen_2065_);
lean_ctor_set(v_reuseFailAlloc_2089_, 3, v_auxDeclNGen_2066_);
lean_ctor_set(v_reuseFailAlloc_2089_, 4, v_traceState_2067_);
lean_ctor_set(v_reuseFailAlloc_2089_, 5, v_cache_2068_);
lean_ctor_set(v_reuseFailAlloc_2089_, 6, v_messages_2069_);
lean_ctor_set(v_reuseFailAlloc_2089_, 7, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2089_, 8, v_snapshotTasks_2070_);
v___x_2086_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = lean_st_ref_put(v___y_2054_, v___x_2086_);
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2081_);
return v___x_2088_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2093_, v___y_2094_);
lean_dec(v___y_2094_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object* v_t_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v___x_2101_; lean_object* v_infoState_2102_; uint8_t v_enabled_2103_; 
v___x_2101_ = lean_st_ref_get(v___y_2099_);
v_infoState_2102_ = lean_ctor_get(v___x_2101_, 7);
lean_inc_ref(v_infoState_2102_);
lean_dec(v___x_2101_);
v_enabled_2103_ = lean_ctor_get_uint8(v_infoState_2102_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2102_);
if (v_enabled_2103_ == 0)
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
lean_dec_ref(v_t_2097_);
v___x_2104_ = lean_box(0);
v___x_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
return v___x_2105_;
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2106_ = lean_unsigned_to_nat(32u);
v___x_2107_ = lean_mk_empty_array_with_capacity(v___x_2106_);
lean_dec_ref(v___x_2107_);
v___x_2108_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2109_, 0, v_t_2097_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v___x_2109_, v___y_2099_);
return v___x_2110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object* v_t_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
return v_res_2115_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7);
v___x_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
return v___x_2117_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2119_ = lean_unsigned_to_nat(0u);
v___x_2120_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
lean_ctor_set(v___x_2120_, 2, v___x_2119_);
lean_ctor_set(v___x_2120_, 3, v___x_2119_);
lean_ctor_set(v___x_2120_, 4, v___x_2118_);
lean_ctor_set(v___x_2120_, 5, v___x_2118_);
lean_ctor_set(v___x_2120_, 6, v___x_2118_);
lean_ctor_set(v___x_2120_, 7, v___x_2118_);
lean_ctor_set(v___x_2120_, 8, v___x_2118_);
lean_ctor_set(v___x_2120_, 9, v___x_2118_);
lean_ctor_set(v___x_2120_, 10, v___x_2118_);
return v___x_2120_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2121_ = lean_box(1);
v___x_2122_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_2123_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
lean_ctor_set(v___x_2124_, 1, v___x_2122_);
lean_ctor_set(v___x_2124_, 2, v___x_2121_);
return v___x_2124_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3));
v___x_2127_ = l_Lean_stringToMessageData(v___x_2126_);
return v___x_2127_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6(void){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5));
v___x_2130_ = l_Lean_stringToMessageData(v___x_2129_);
return v___x_2130_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8(void){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7));
v___x_2133_ = l_Lean_stringToMessageData(v___x_2132_);
return v___x_2133_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10(void){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9));
v___x_2136_ = l_Lean_stringToMessageData(v___x_2135_);
return v___x_2136_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11));
v___x_2139_ = l_Lean_stringToMessageData(v___x_2138_);
return v___x_2139_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13));
v___x_2142_ = l_Lean_stringToMessageData(v___x_2141_);
return v___x_2142_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15));
v___x_2145_ = l_Lean_stringToMessageData(v___x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_2146_, lean_object* v_declHint_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v_env_2152_; uint8_t v___x_2153_; 
v___x_2150_ = lean_box(0);
v___x_2151_ = lean_st_ref_get(v___y_2148_);
v_env_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc_ref(v_env_2152_);
lean_dec(v___x_2151_);
v___x_2153_ = l_Lean_Name_isAnonymous(v_declHint_2147_);
if (v___x_2153_ == 0)
{
uint8_t v_isExporting_2154_; 
v_isExporting_2154_ = lean_ctor_get_uint8(v_env_2152_, sizeof(void*)*8);
if (v_isExporting_2154_ == 0)
{
lean_object* v___x_2155_; 
lean_dec_ref(v_env_2152_);
lean_dec(v_declHint_2147_);
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v_msg_2146_);
return v___x_2155_;
}
else
{
lean_object* v___x_2156_; uint8_t v___x_2157_; 
lean_inc_ref(v_env_2152_);
v___x_2156_ = l_Lean_Environment_setExporting(v_env_2152_, v___x_2153_);
lean_inc(v_declHint_2147_);
lean_inc_ref(v___x_2156_);
v___x_2157_ = l_Lean_Environment_contains(v___x_2156_, v_declHint_2147_, v_isExporting_2154_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; 
lean_dec_ref(v___x_2156_);
lean_dec_ref(v_env_2152_);
lean_dec(v_declHint_2147_);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v_msg_2146_);
return v___x_2158_;
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v_c_2164_; lean_object* v___x_2165_; 
v___x_2159_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2160_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_2161_ = l_Lean_Options_empty;
v___x_2162_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2156_);
lean_ctor_set(v___x_2162_, 1, v___x_2159_);
lean_ctor_set(v___x_2162_, 2, v___x_2160_);
lean_ctor_set(v___x_2162_, 3, v___x_2161_);
lean_inc(v_declHint_2147_);
v___x_2163_ = l_Lean_MessageData_ofConstName(v_declHint_2147_, v___x_2153_);
v_c_2164_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2164_, 0, v___x_2162_);
lean_ctor_set(v_c_2164_, 1, v___x_2163_);
v___x_2165_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2152_, v_declHint_2147_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_dec_ref(v_env_2152_);
lean_dec(v_declHint_2147_);
v___x_2166_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
lean_ctor_set(v___x_2167_, 1, v_c_2164_);
v___x_2168_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6);
v___x_2169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2167_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = l_Lean_MessageData_note(v___x_2169_);
v___x_2171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2171_, 0, v_msg_2146_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
return v___x_2172_;
}
else
{
lean_object* v_val_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2207_; 
v_val_2173_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2175_ = v___x_2165_;
v_isShared_2176_ = v_isSharedCheck_2207_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_val_2173_);
lean_dec(v___x_2165_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2207_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v_mod_2179_; uint8_t v___x_2180_; 
v___x_2177_ = l_Lean_Environment_header(v_env_2152_);
lean_dec_ref(v_env_2152_);
v___x_2178_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2177_);
v_mod_2179_ = lean_array_get(v___x_2150_, v___x_2178_, v_val_2173_);
lean_dec(v_val_2173_);
lean_dec_ref(v___x_2178_);
v___x_2180_ = l_Lean_isPrivateName(v_declHint_2147_);
lean_dec(v_declHint_2147_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2181_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8);
v___x_2182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v_c_2164_);
v___x_2183_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10);
v___x_2184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2182_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
v___x_2185_ = l_Lean_MessageData_ofName(v_mod_2179_);
v___x_2186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2184_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v___x_2187_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12);
v___x_2188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2186_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
v___x_2189_ = l_Lean_MessageData_note(v___x_2188_);
v___x_2190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2190_, 0, v_msg_2146_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set_tag(v___x_2175_, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2190_);
v___x_2192_ = v___x_2175_;
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
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2194_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_2195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
lean_ctor_set(v___x_2195_, 1, v_c_2164_);
v___x_2196_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14);
v___x_2197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2195_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = l_Lean_MessageData_ofName(v_mod_2179_);
v___x_2199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
v___x_2200_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16);
v___x_2201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2199_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = l_Lean_MessageData_note(v___x_2201_);
v___x_2203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2203_, 0, v_msg_2146_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set_tag(v___x_2175_, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2203_);
v___x_2205_ = v___x_2175_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2203_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2208_; 
lean_dec_ref(v_env_2152_);
lean_dec(v_declHint_2147_);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v_msg_2146_);
return v___x_2208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_2209_, lean_object* v_declHint_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2209_, v_declHint_2210_, v___y_2211_);
lean_dec(v___y_2211_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_2214_, lean_object* v_declHint_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___x_2219_; lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2229_; 
v___x_2219_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2214_, v_declHint_2215_, v___y_2217_);
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2222_ = v___x_2219_;
v_isShared_2223_ = v_isSharedCheck_2229_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2219_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2229_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2224_ = l_Lean_unknownIdentifierMessageTag;
v___x_2225_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
lean_ctor_set(v___x_2225_, 1, v_a_2220_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v___x_2225_);
v___x_2227_ = v___x_2222_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_2230_, lean_object* v_declHint_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2230_, v_declHint_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object* v_msgData_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v___x_2240_; lean_object* v_toCold_2241_; lean_object* v_env_2242_; lean_object* v_options_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2240_ = lean_st_ref_get(v___y_2238_);
v_toCold_2241_ = lean_ctor_get(v___y_2237_, 0);
v_env_2242_ = lean_ctor_get(v___x_2240_, 0);
lean_inc_ref(v_env_2242_);
lean_dec(v___x_2240_);
v_options_2243_ = lean_ctor_get(v_toCold_2241_, 2);
v___x_2244_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2245_ = lean_unsigned_to_nat(32u);
v___x_2246_ = lean_mk_empty_array_with_capacity(v___x_2245_);
lean_dec_ref(v___x_2246_);
v___x_2247_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
lean_inc_ref(v_options_2243_);
v___x_2248_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2248_, 0, v_env_2242_);
lean_ctor_set(v___x_2248_, 1, v___x_2244_);
lean_ctor_set(v___x_2248_, 2, v___x_2247_);
lean_ctor_set(v___x_2248_, 3, v_options_2243_);
v___x_2249_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
lean_ctor_set(v___x_2249_, 1, v_msgData_2236_);
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object* v_msgData_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_2251_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_ref_2260_; lean_object* v___x_2261_; lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2270_; 
v_ref_2260_ = lean_ctor_get(v___y_2257_, 2);
v___x_2261_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_2256_, v___y_2257_, v___y_2258_);
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2270_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2270_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
lean_inc(v_ref_2260_);
v___x_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2266_, 0, v_ref_2260_);
lean_ctor_set(v___x_2266_, 1, v_a_2262_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set_tag(v___x_2264_, 1);
lean_ctor_set(v___x_2264_, 0, v___x_2266_);
v___x_2268_ = v___x_2264_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2271_, v___y_2272_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_2276_, lean_object* v_msg_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_toCold_2281_; lean_object* v_currRecDepth_2282_; lean_object* v_ref_2283_; uint8_t v_diag_2284_; uint8_t v_suppressElabErrors_2285_; lean_object* v_ref_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v_toCold_2281_ = lean_ctor_get(v___y_2278_, 0);
v_currRecDepth_2282_ = lean_ctor_get(v___y_2278_, 1);
v_ref_2283_ = lean_ctor_get(v___y_2278_, 2);
v_diag_2284_ = lean_ctor_get_uint8(v___y_2278_, sizeof(void*)*3);
v_suppressElabErrors_2285_ = lean_ctor_get_uint8(v___y_2278_, sizeof(void*)*3 + 1);
v_ref_2286_ = l_Lean_replaceRef(v_ref_2276_, v_ref_2283_);
lean_inc(v_currRecDepth_2282_);
lean_inc_ref(v_toCold_2281_);
v___x_2287_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2287_, 0, v_toCold_2281_);
lean_ctor_set(v___x_2287_, 1, v_currRecDepth_2282_);
lean_ctor_set(v___x_2287_, 2, v_ref_2286_);
lean_ctor_set_uint8(v___x_2287_, sizeof(void*)*3, v_diag_2284_);
lean_ctor_set_uint8(v___x_2287_, sizeof(void*)*3 + 1, v_suppressElabErrors_2285_);
v___x_2288_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2277_, v___x_2287_, v___y_2279_);
lean_dec_ref_known(v___x_2287_, 3);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_2289_, lean_object* v_msg_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2289_, v_msg_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v_ref_2289_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_2295_, lean_object* v_msg_2296_, lean_object* v_declHint_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2301_; lean_object* v_a_2302_; lean_object* v___x_2303_; 
v___x_2301_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2296_, v_declHint_2297_, v___y_2298_, v___y_2299_);
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref(v___x_2301_);
v___x_2303_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2295_, v_a_2302_, v___y_2298_, v___y_2299_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2304_, lean_object* v_msg_2305_, lean_object* v_declHint_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2304_, v_msg_2305_, v_declHint_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v_ref_2304_);
return v_res_2310_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_2313_ = l_Lean_stringToMessageData(v___x_2312_);
return v___x_2313_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2));
v___x_2316_ = l_Lean_stringToMessageData(v___x_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_2317_, lean_object* v_constName_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v___x_2322_; uint8_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2322_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_2323_ = 0;
lean_inc(v_constName_2318_);
v___x_2324_ = l_Lean_MessageData_ofConstName(v_constName_2318_, v___x_2323_);
v___x_2325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2322_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
v___x_2326_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_2327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2325_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
v___x_2328_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2317_, v___x_2327_, v_constName_2318_, v___y_2319_, v___y_2320_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2329_, lean_object* v_constName_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2329_, v_constName_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v_ref_2329_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v_ref_2339_; lean_object* v___x_2340_; 
v_ref_2339_ = lean_ctor_get(v___y_2336_, 2);
v___x_2340_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2339_, v_constName_2335_, v___y_2336_, v___y_2337_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object* v_constName_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v___x_2350_; lean_object* v_env_2351_; uint8_t v___x_2352_; lean_object* v___x_2353_; 
v___x_2350_ = lean_st_ref_get(v___y_2348_);
v_env_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc_ref(v_env_2351_);
lean_dec(v___x_2350_);
v___x_2352_ = 0;
lean_inc(v_constName_2346_);
v___x_2353_ = l_Lean_Environment_findConstVal_x3f(v_env_2351_, v_constName_2346_, v___x_2352_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2346_, v___y_2347_, v___y_2348_);
return v___x_2354_;
}
else
{
lean_object* v_val_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec(v_constName_2346_);
v_val_2355_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2353_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_val_2355_);
lean_dec(v___x_2353_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
lean_ctor_set_tag(v___x_2357_, 0);
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_val_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
if (lean_obj_tag(v_a_2368_) == 0)
{
lean_object* v___x_2370_; 
v___x_2370_ = l_List_reverse___redArg(v_a_2369_);
return v___x_2370_;
}
else
{
lean_object* v_head_2371_; lean_object* v_tail_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2381_; 
v_head_2371_ = lean_ctor_get(v_a_2368_, 0);
v_tail_2372_ = lean_ctor_get(v_a_2368_, 1);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_a_2368_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2374_ = v_a_2368_;
v_isShared_2375_ = v_isSharedCheck_2381_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_tail_2372_);
lean_inc(v_head_2371_);
lean_dec(v_a_2368_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2381_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2376_; lean_object* v___x_2378_; 
v___x_2376_ = l_Lean_mkLevelParam(v_head_2371_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 1, v_a_2369_);
lean_ctor_set(v___x_2374_, 0, v___x_2376_);
v___x_2378_ = v___x_2374_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v_a_2369_);
v___x_2378_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
v_a_2368_ = v_tail_2372_;
v_a_2369_ = v___x_2378_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object* v_constName_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v___x_2386_; 
lean_inc(v_constName_2382_);
v___x_2386_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2398_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2389_ = v___x_2386_;
v_isShared_2390_ = v_isSharedCheck_2398_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2398_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v_levelParams_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2396_; 
v_levelParams_2391_ = lean_ctor_get(v_a_2387_, 1);
lean_inc(v_levelParams_2391_);
lean_dec(v_a_2387_);
v___x_2392_ = lean_box(0);
v___x_2393_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_2391_, v___x_2392_);
v___x_2394_ = l_Lean_mkConst(v_constName_2382_, v___x_2393_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2394_);
v___x_2396_ = v___x_2389_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2394_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec(v_constName_2382_);
v_a_2399_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2386_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2386_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object* v_constName_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_2407_, v___y_2408_, v___y_2409_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object* v_stx_2412_, lean_object* v_n_2413_, lean_object* v_expectedType_x3f_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_2413_, v___y_2415_, v___y_2416_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2419_);
lean_dec_ref_known(v___x_2418_, 1);
v___x_2420_ = lean_box(0);
v___x_2421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
lean_ctor_set(v___x_2421_, 1, v_stx_2412_);
v___x_2422_ = l_Lean_LocalContext_empty;
v___x_2423_ = 0;
v___x_2424_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2424_, 0, v___x_2421_);
lean_ctor_set(v___x_2424_, 1, v___x_2422_);
lean_ctor_set(v___x_2424_, 2, v_expectedType_x3f_2414_);
lean_ctor_set(v___x_2424_, 3, v_a_2419_);
lean_ctor_set_uint8(v___x_2424_, sizeof(void*)*4, v___x_2423_);
lean_ctor_set_uint8(v___x_2424_, sizeof(void*)*4 + 1, v___x_2423_);
v___x_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
v___x_2426_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_2425_, v___y_2415_, v___y_2416_);
return v___x_2426_;
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec(v_expectedType_x3f_2414_);
lean_dec(v_stx_2412_);
v_a_2427_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2418_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2418_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object* v_stx_2435_, lean_object* v_n_2436_, lean_object* v_expectedType_x3f_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_2435_, v_n_2436_, v_expectedType_x3f_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object* v_id_2442_, lean_object* v_expectedType_x3f_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v___x_2447_; 
lean_inc(v_id_2442_);
v___x_2447_ = l_Lean_realizeGlobalConstNoOverload(v_id_2442_, v_a_2444_, v_a_2445_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2475_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2450_ = v___x_2447_;
v_isShared_2451_ = v_isSharedCheck_2475_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2475_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2452_; lean_object* v_infoState_2453_; uint8_t v_enabled_2454_; 
v___x_2452_ = lean_st_ref_get(v_a_2445_);
v_infoState_2453_ = lean_ctor_get(v___x_2452_, 7);
lean_inc_ref(v_infoState_2453_);
lean_dec(v___x_2452_);
v_enabled_2454_ = lean_ctor_get_uint8(v_infoState_2453_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2453_);
if (v_enabled_2454_ == 0)
{
lean_object* v___x_2456_; 
lean_dec(v_expectedType_x3f_2443_);
lean_dec(v_id_2442_);
if (v_isShared_2451_ == 0)
{
v___x_2456_ = v___x_2450_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2448_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
else
{
lean_object* v___x_2458_; 
lean_del_object(v___x_2450_);
lean_inc(v_a_2448_);
v___x_2458_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2442_, v_a_2448_, v_expectedType_x3f_2443_, v_a_2444_, v_a_2445_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2465_ == 0)
{
lean_object* v_unused_2466_; 
v_unused_2466_ = lean_ctor_get(v___x_2458_, 0);
lean_dec(v_unused_2466_);
v___x_2460_ = v___x_2458_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_dec(v___x_2458_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v_a_2448_);
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2448_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec(v_a_2448_);
v_a_2467_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2458_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2458_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2443_);
lean_dec(v_id_2442_);
return v___x_2447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object* v_id_2476_, lean_object* v_expectedType_x3f_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_2476_, v_expectedType_x3f_2477_, v_a_2478_, v_a_2479_);
lean_dec(v_a_2479_);
lean_dec_ref(v_a_2478_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object* v_t_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2482_, v___y_2484_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_2487_, v___y_2488_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2492_, lean_object* v_constName_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2493_, v___y_2494_, v___y_2495_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2498_, lean_object* v_constName_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2498_, v_constName_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2504_, lean_object* v_ref_2505_, lean_object* v_constName_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2505_, v_constName_2506_, v___y_2507_, v___y_2508_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2511_, lean_object* v_ref_2512_, lean_object* v_constName_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_2511_, v_ref_2512_, v_constName_2513_, v___y_2514_, v___y_2515_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v_ref_2512_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2518_, lean_object* v_ref_2519_, lean_object* v_msg_2520_, lean_object* v_declHint_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v___x_2525_; 
v___x_2525_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2519_, v_msg_2520_, v_declHint_2521_, v___y_2522_, v___y_2523_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2526_, lean_object* v_ref_2527_, lean_object* v_msg_2528_, lean_object* v_declHint_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_2526_, v_ref_2527_, v_msg_2528_, v_declHint_2529_, v___y_2530_, v___y_2531_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v_ref_2527_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_2534_, lean_object* v_declHint_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2534_, v_declHint_2535_, v___y_2537_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2540_, lean_object* v_declHint_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2540_, v_declHint_2541_, v___y_2542_, v___y_2543_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_2546_, lean_object* v_ref_2547_, lean_object* v_msg_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v___x_2552_; 
v___x_2552_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2547_, v_msg_2548_, v___y_2549_, v___y_2550_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2553_, lean_object* v_ref_2554_, lean_object* v_msg_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_2553_, v_ref_2554_, v_msg_2555_, v___y_2556_, v___y_2557_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v_ref_2554_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_2560_, lean_object* v_msg_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2561_, v___y_2562_, v___y_2563_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_2566_, lean_object* v_msg_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_2566_, v_msg_2567_, v___y_2568_, v___y_2569_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object* v_id_2572_, lean_object* v_expectedType_x3f_2573_, lean_object* v_as_x27_2574_, lean_object* v_b_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
if (lean_obj_tag(v_as_x27_2574_) == 0)
{
lean_object* v___x_2579_; 
lean_dec(v_expectedType_x3f_2573_);
lean_dec(v_id_2572_);
v___x_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2579_, 0, v_b_2575_);
return v___x_2579_;
}
else
{
lean_object* v_head_2580_; lean_object* v_tail_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v_head_2580_ = lean_ctor_get(v_as_x27_2574_, 0);
v_tail_2581_ = lean_ctor_get(v_as_x27_2574_, 1);
v___x_2582_ = lean_box(0);
lean_inc(v_expectedType_x3f_2573_);
lean_inc(v_head_2580_);
lean_inc(v_id_2572_);
v___x_2583_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2572_, v_head_2580_, v_expectedType_x3f_2573_, v___y_2576_, v___y_2577_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_dec_ref_known(v___x_2583_, 1);
v_as_x27_2574_ = v_tail_2581_;
v_b_2575_ = v___x_2582_;
goto _start;
}
else
{
lean_dec(v_expectedType_x3f_2573_);
lean_dec(v_id_2572_);
return v___x_2583_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object* v_id_2585_, lean_object* v_expectedType_x3f_2586_, lean_object* v_as_x27_2587_, lean_object* v_b_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2585_, v_expectedType_x3f_2586_, v_as_x27_2587_, v_b_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v_as_x27_2587_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object* v_id_2593_, lean_object* v_expectedType_x3f_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_){
_start:
{
lean_object* v___x_2598_; 
lean_inc(v_id_2593_);
v___x_2598_ = l_Lean_realizeGlobalConst(v_id_2593_, v_a_2595_, v_a_2596_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2627_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2601_ = v___x_2598_;
v_isShared_2602_ = v_isSharedCheck_2627_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2598_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2627_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2603_; lean_object* v_infoState_2604_; uint8_t v_enabled_2605_; 
v___x_2603_ = lean_st_ref_get(v_a_2596_);
v_infoState_2604_ = lean_ctor_get(v___x_2603_, 7);
lean_inc_ref(v_infoState_2604_);
lean_dec(v___x_2603_);
v_enabled_2605_ = lean_ctor_get_uint8(v_infoState_2604_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2604_);
if (v_enabled_2605_ == 0)
{
lean_object* v___x_2607_; 
lean_dec(v_expectedType_x3f_2594_);
lean_dec(v_id_2593_);
if (v_isShared_2602_ == 0)
{
v___x_2607_ = v___x_2601_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2599_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
else
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_del_object(v___x_2601_);
v___x_2609_ = lean_box(0);
v___x_2610_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2593_, v_expectedType_x3f_2594_, v_a_2599_, v___x_2609_, v_a_2595_, v_a_2596_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2617_ == 0)
{
lean_object* v_unused_2618_; 
v_unused_2618_ = lean_ctor_get(v___x_2610_, 0);
lean_dec(v_unused_2618_);
v___x_2612_ = v___x_2610_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_dec(v___x_2610_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v_a_2599_);
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2599_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec(v_a_2599_);
v_a_2619_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2610_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2610_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2594_);
lean_dec(v_id_2593_);
return v___x_2598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object* v_id_2628_, lean_object* v_expectedType_x3f_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_2628_, v_expectedType_x3f_2629_, v_a_2630_, v_a_2631_);
lean_dec(v_a_2631_);
lean_dec_ref(v_a_2630_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object* v_id_2634_, lean_object* v_expectedType_x3f_2635_, lean_object* v_as_2636_, lean_object* v_as_x27_2637_, lean_object* v_b_2638_, lean_object* v_a_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2634_, v_expectedType_x3f_2635_, v_as_x27_2637_, v_b_2638_, v___y_2640_, v___y_2641_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object* v_id_2644_, lean_object* v_expectedType_x3f_2645_, lean_object* v_as_2646_, lean_object* v_as_x27_2647_, lean_object* v_b_2648_, lean_object* v_a_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_2644_, v_expectedType_x3f_2645_, v_as_2646_, v_as_x27_2647_, v_b_2648_, v_a_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v_as_x27_2647_);
lean_dec(v_as_2646_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object* v_ref_2654_, lean_object* v_as_x27_2655_, lean_object* v_b_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
if (lean_obj_tag(v_as_x27_2655_) == 0)
{
lean_object* v___x_2660_; 
lean_dec(v_ref_2654_);
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v_b_2656_);
return v___x_2660_;
}
else
{
lean_object* v_head_2661_; lean_object* v_tail_2662_; lean_object* v_fst_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v_head_2661_ = lean_ctor_get(v_as_x27_2655_, 0);
v_tail_2662_ = lean_ctor_get(v_as_x27_2655_, 1);
v_fst_2663_ = lean_ctor_get(v_head_2661_, 0);
v___x_2664_ = lean_box(0);
v___x_2665_ = lean_box(0);
lean_inc(v_fst_2663_);
lean_inc(v_ref_2654_);
v___x_2666_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_2654_, v_fst_2663_, v___x_2665_, v___y_2657_, v___y_2658_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_dec_ref_known(v___x_2666_, 1);
v_as_x27_2655_ = v_tail_2662_;
v_b_2656_ = v___x_2664_;
goto _start;
}
else
{
lean_dec(v_ref_2654_);
return v___x_2666_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object* v_ref_2668_, lean_object* v_as_x27_2669_, lean_object* v_b_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2668_, v_as_x27_2669_, v_b_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v_as_x27_2669_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object* v_ref_2675_, lean_object* v_id_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Lean_realizeGlobalName(v_id_2676_, v_a_2677_, v_a_2678_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2709_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2683_ = v___x_2680_;
v_isShared_2684_ = v_isSharedCheck_2709_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2680_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2709_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; lean_object* v_infoState_2686_; uint8_t v_enabled_2687_; 
v___x_2685_ = lean_st_ref_get(v_a_2678_);
v_infoState_2686_ = lean_ctor_get(v___x_2685_, 7);
lean_inc_ref(v_infoState_2686_);
lean_dec(v___x_2685_);
v_enabled_2687_ = lean_ctor_get_uint8(v_infoState_2686_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2686_);
if (v_enabled_2687_ == 0)
{
lean_object* v___x_2689_; 
lean_dec(v_ref_2675_);
if (v_isShared_2684_ == 0)
{
v___x_2689_ = v___x_2683_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2681_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
else
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
lean_del_object(v___x_2683_);
v___x_2691_ = lean_box(0);
v___x_2692_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2675_, v_a_2681_, v___x_2691_, v_a_2677_, v_a_2678_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2699_ == 0)
{
lean_object* v_unused_2700_; 
v_unused_2700_ = lean_ctor_get(v___x_2692_, 0);
lean_dec(v_unused_2700_);
v___x_2694_ = v___x_2692_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_dec(v___x_2692_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v_a_2681_);
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2681_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
lean_dec(v_a_2681_);
v_a_2701_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2692_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2692_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
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
else
{
lean_dec(v_ref_2675_);
return v___x_2680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object* v_ref_2710_, lean_object* v_id_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_2710_, v_id_2711_, v_a_2712_, v_a_2713_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object* v_ref_2716_, lean_object* v_as_2717_, lean_object* v_as_x27_2718_, lean_object* v_b_2719_, lean_object* v_a_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2716_, v_as_x27_2718_, v_b_2719_, v___y_2721_, v___y_2722_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object* v_ref_2725_, lean_object* v_as_2726_, lean_object* v_as_x27_2727_, lean_object* v_b_2728_, lean_object* v_a_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_2725_, v_as_2726_, v_as_x27_2727_, v_b_2728_, v_a_2729_, v___y_2730_, v___y_2731_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_as_x27_2727_);
lean_dec(v_as_2726_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object* v_self_2734_){
_start:
{
lean_object* v_fst_2735_; 
v_fst_2735_ = lean_ctor_get(v_self_2734_, 0);
lean_inc(v_fst_2735_);
return v_fst_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object* v_self_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_2736_);
lean_dec_ref(v_self_2736_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object* v_info_2738_, lean_object* v_treesSaved_2739_, lean_object* v_s_2740_){
_start:
{
if (lean_obj_tag(v_info_2738_) == 0)
{
uint8_t v_enabled_2741_; lean_object* v_assignment_2742_; lean_object* v_lazyAssignment_2743_; lean_object* v_trees_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2754_; 
v_enabled_2741_ = lean_ctor_get_uint8(v_s_2740_, sizeof(void*)*3);
v_assignment_2742_ = lean_ctor_get(v_s_2740_, 0);
v_lazyAssignment_2743_ = lean_ctor_get(v_s_2740_, 1);
v_trees_2744_ = lean_ctor_get(v_s_2740_, 2);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_s_2740_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2746_ = v_s_2740_;
v_isShared_2747_ = v_isSharedCheck_2754_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_trees_2744_);
lean_inc(v_lazyAssignment_2743_);
lean_inc(v_assignment_2742_);
lean_dec(v_s_2740_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2754_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v_val_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
v_val_2748_ = lean_ctor_get(v_info_2738_, 0);
lean_inc(v_val_2748_);
lean_dec_ref_known(v_info_2738_, 1);
v___x_2749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2749_, 0, v_val_2748_);
lean_ctor_set(v___x_2749_, 1, v_trees_2744_);
v___x_2750_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2739_, v___x_2749_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 2, v___x_2750_);
v___x_2752_ = v___x_2746_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_assignment_2742_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v_lazyAssignment_2743_);
lean_ctor_set(v_reuseFailAlloc_2753_, 2, v___x_2750_);
lean_ctor_set_uint8(v_reuseFailAlloc_2753_, sizeof(void*)*3, v_enabled_2741_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
else
{
uint8_t v_enabled_2755_; lean_object* v_assignment_2756_; lean_object* v_lazyAssignment_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2773_; 
v_enabled_2755_ = lean_ctor_get_uint8(v_s_2740_, sizeof(void*)*3);
v_assignment_2756_ = lean_ctor_get(v_s_2740_, 0);
v_lazyAssignment_2757_ = lean_ctor_get(v_s_2740_, 1);
v_isSharedCheck_2773_ = !lean_is_exclusive(v_s_2740_);
if (v_isSharedCheck_2773_ == 0)
{
lean_object* v_unused_2774_; 
v_unused_2774_ = lean_ctor_get(v_s_2740_, 2);
lean_dec(v_unused_2774_);
v___x_2759_ = v_s_2740_;
v_isShared_2760_ = v_isSharedCheck_2773_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_lazyAssignment_2757_);
lean_inc(v_assignment_2756_);
lean_dec(v_s_2740_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2773_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v_val_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2772_; 
v_val_2761_ = lean_ctor_get(v_info_2738_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v_info_2738_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2763_ = v_info_2738_;
v_isShared_2764_ = v_isSharedCheck_2772_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_val_2761_);
lean_dec(v_info_2738_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2772_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
lean_ctor_set_tag(v___x_2763_, 2);
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_val_2761_);
v___x_2766_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v___x_2767_; lean_object* v___x_2769_; 
v___x_2767_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2739_, v___x_2766_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 2, v___x_2767_);
v___x_2769_ = v___x_2759_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_assignment_2756_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v_lazyAssignment_2757_);
lean_ctor_set(v_reuseFailAlloc_2770_, 2, v___x_2767_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, sizeof(void*)*3, v_enabled_2755_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object* v_treesSaved_2775_, lean_object* v_modifyInfoState_2776_, lean_object* v_info_2777_){
_start:
{
lean_object* v___f_2778_; lean_object* v___x_2779_; 
v___f_2778_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2778_, 0, v_info_2777_);
lean_closure_set(v___f_2778_, 1, v_treesSaved_2775_);
v___x_2779_ = lean_apply_1(v_modifyInfoState_2776_, v___f_2778_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object* v___f_2780_, lean_object* v_info_2781_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = lean_apply_1(v___f_2780_, v_info_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object* v_toPure_2783_, lean_object* v_toBind_2784_, lean_object* v___f_2785_, lean_object* v_____do__lift_2786_){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2787_, 0, v_____do__lift_2786_);
v___x_2788_ = lean_apply_2(v_toPure_2783_, lean_box(0), v___x_2787_);
v___x_2789_ = lean_apply_4(v_toBind_2784_, lean_box(0), lean_box(0), v___x_2788_, v___f_2785_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object* v_toBind_2790_, lean_object* v_mkInfoOnError_2791_, lean_object* v___f_2792_, lean_object* v_mkInfo_2793_, lean_object* v___f_2794_, lean_object* v_a_x3f_2795_){
_start:
{
if (lean_obj_tag(v_a_x3f_2795_) == 0)
{
lean_object* v___x_2796_; 
lean_dec(v___f_2794_);
lean_dec(v_mkInfo_2793_);
v___x_2796_ = lean_apply_4(v_toBind_2790_, lean_box(0), lean_box(0), v_mkInfoOnError_2791_, v___f_2792_);
return v___x_2796_;
}
else
{
lean_object* v_val_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
lean_dec(v___f_2792_);
lean_dec(v_mkInfoOnError_2791_);
v_val_2797_ = lean_ctor_get(v_a_x3f_2795_, 0);
lean_inc(v_val_2797_);
lean_dec_ref_known(v_a_x3f_2795_, 1);
v___x_2798_ = lean_apply_1(v_mkInfo_2793_, v_val_2797_);
v___x_2799_ = lean_apply_4(v_toBind_2790_, lean_box(0), lean_box(0), v___x_2798_, v___f_2794_);
return v___x_2799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object* v_toFunctor_2800_, lean_object* v_modifyInfoState_2801_, lean_object* v_toPure_2802_, lean_object* v_toBind_2803_, lean_object* v_mkInfoOnError_2804_, lean_object* v_mkInfo_2805_, lean_object* v_inst_2806_, lean_object* v_x_2807_, lean_object* v___f_2808_, lean_object* v_treesSaved_2809_){
_start:
{
lean_object* v_map_2810_; lean_object* v___f_2811_; lean_object* v___f_2812_; lean_object* v___f_2813_; lean_object* v___f_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v_map_2810_ = lean_ctor_get(v_toFunctor_2800_, 0);
lean_inc(v_map_2810_);
lean_dec_ref(v_toFunctor_2800_);
v___f_2811_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2811_, 0, v_treesSaved_2809_);
lean_closure_set(v___f_2811_, 1, v_modifyInfoState_2801_);
v___f_2812_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2812_, 0, v___f_2811_);
lean_inc_ref(v___f_2812_);
lean_inc(v_toBind_2803_);
v___f_2813_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_2813_, 0, v_toPure_2802_);
lean_closure_set(v___f_2813_, 1, v_toBind_2803_);
lean_closure_set(v___f_2813_, 2, v___f_2812_);
v___f_2814_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__6), 6, 5);
lean_closure_set(v___f_2814_, 0, v_toBind_2803_);
lean_closure_set(v___f_2814_, 1, v_mkInfoOnError_2804_);
lean_closure_set(v___f_2814_, 2, v___f_2813_);
lean_closure_set(v___f_2814_, 3, v_mkInfo_2805_);
lean_closure_set(v___f_2814_, 4, v___f_2812_);
v___x_2815_ = lean_apply_4(v_inst_2806_, lean_box(0), lean_box(0), v_x_2807_, v___f_2814_);
v___x_2816_ = lean_apply_4(v_map_2810_, lean_box(0), lean_box(0), v___f_2808_, v___x_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object* v_x_2817_, lean_object* v_inst_2818_, lean_object* v_inst_2819_, lean_object* v_toBind_2820_, lean_object* v___f_2821_, lean_object* v_____do__lift_2822_){
_start:
{
uint8_t v_enabled_2823_; 
v_enabled_2823_ = lean_ctor_get_uint8(v_____do__lift_2822_, sizeof(void*)*3);
if (v_enabled_2823_ == 0)
{
lean_dec(v___f_2821_);
lean_dec(v_toBind_2820_);
lean_dec_ref(v_inst_2819_);
lean_dec_ref(v_inst_2818_);
lean_inc(v_x_2817_);
return v_x_2817_;
}
else
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2818_, v_inst_2819_);
v___x_2825_ = lean_apply_4(v_toBind_2820_, lean_box(0), lean_box(0), v___x_2824_, v___f_2821_);
return v___x_2825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object* v_x_2826_, lean_object* v_inst_2827_, lean_object* v_inst_2828_, lean_object* v_toBind_2829_, lean_object* v___f_2830_, lean_object* v_____do__lift_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__7(v_x_2826_, v_inst_2827_, v_inst_2828_, v_toBind_2829_, v___f_2830_, v_____do__lift_2831_);
lean_dec_ref(v_____do__lift_2831_);
lean_dec(v_x_2826_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object* v_inst_2834_, lean_object* v_inst_2835_, lean_object* v_inst_2836_, lean_object* v_x_2837_, lean_object* v_mkInfo_2838_, lean_object* v_mkInfoOnError_2839_){
_start:
{
lean_object* v_toApplicative_2840_; lean_object* v_toBind_2841_; lean_object* v_getInfoState_2842_; lean_object* v_modifyInfoState_2843_; lean_object* v_toFunctor_2844_; lean_object* v_toPure_2845_; lean_object* v___f_2846_; lean_object* v___f_2847_; lean_object* v___f_2848_; lean_object* v___x_2849_; 
v_toApplicative_2840_ = lean_ctor_get(v_inst_2834_, 0);
v_toBind_2841_ = lean_ctor_get(v_inst_2834_, 1);
lean_inc_n(v_toBind_2841_, 3);
v_getInfoState_2842_ = lean_ctor_get(v_inst_2835_, 0);
lean_inc(v_getInfoState_2842_);
v_modifyInfoState_2843_ = lean_ctor_get(v_inst_2835_, 1);
v_toFunctor_2844_ = lean_ctor_get(v_toApplicative_2840_, 0);
v_toPure_2845_ = lean_ctor_get(v_toApplicative_2840_, 1);
v___f_2846_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2837_);
lean_inc(v_toPure_2845_);
lean_inc(v_modifyInfoState_2843_);
lean_inc_ref(v_toFunctor_2844_);
v___f_2847_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__5), 10, 9);
lean_closure_set(v___f_2847_, 0, v_toFunctor_2844_);
lean_closure_set(v___f_2847_, 1, v_modifyInfoState_2843_);
lean_closure_set(v___f_2847_, 2, v_toPure_2845_);
lean_closure_set(v___f_2847_, 3, v_toBind_2841_);
lean_closure_set(v___f_2847_, 4, v_mkInfoOnError_2839_);
lean_closure_set(v___f_2847_, 5, v_mkInfo_2838_);
lean_closure_set(v___f_2847_, 6, v_inst_2836_);
lean_closure_set(v___f_2847_, 7, v_x_2837_);
lean_closure_set(v___f_2847_, 8, v___f_2846_);
v___f_2848_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2848_, 0, v_x_2837_);
lean_closure_set(v___f_2848_, 1, v_inst_2834_);
lean_closure_set(v___f_2848_, 2, v_inst_2835_);
lean_closure_set(v___f_2848_, 3, v_toBind_2841_);
lean_closure_set(v___f_2848_, 4, v___f_2847_);
v___x_2849_ = lean_apply_4(v_toBind_2841_, lean_box(0), lean_box(0), v_getInfoState_2842_, v___f_2848_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* v_m_2850_, lean_object* v_inst_2851_, lean_object* v_inst_2852_, lean_object* v_00_u03b1_2853_, lean_object* v_inst_2854_, lean_object* v_x_2855_, lean_object* v_mkInfo_2856_, lean_object* v_mkInfoOnError_2857_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_Lean_Elab_withInfoContext_x27___redArg(v_inst_2851_, v_inst_2852_, v_inst_2854_, v_x_2855_, v_mkInfo_2856_, v_mkInfoOnError_2857_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object* v_treesSaved_2859_, lean_object* v_tree_2860_, lean_object* v_s_2861_){
_start:
{
uint8_t v_enabled_2862_; lean_object* v_assignment_2863_; lean_object* v_lazyAssignment_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2872_; 
v_enabled_2862_ = lean_ctor_get_uint8(v_s_2861_, sizeof(void*)*3);
v_assignment_2863_ = lean_ctor_get(v_s_2861_, 0);
v_lazyAssignment_2864_ = lean_ctor_get(v_s_2861_, 1);
v_isSharedCheck_2872_ = !lean_is_exclusive(v_s_2861_);
if (v_isSharedCheck_2872_ == 0)
{
lean_object* v_unused_2873_; 
v_unused_2873_ = lean_ctor_get(v_s_2861_, 2);
lean_dec(v_unused_2873_);
v___x_2866_ = v_s_2861_;
v_isShared_2867_ = v_isSharedCheck_2872_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_lazyAssignment_2864_);
lean_inc(v_assignment_2863_);
lean_dec(v_s_2861_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2872_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2868_; lean_object* v___x_2870_; 
v___x_2868_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2859_, v_tree_2860_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 2, v___x_2868_);
v___x_2870_ = v___x_2866_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_assignment_2863_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_lazyAssignment_2864_);
lean_ctor_set(v_reuseFailAlloc_2871_, 2, v___x_2868_);
lean_ctor_set_uint8(v_reuseFailAlloc_2871_, sizeof(void*)*3, v_enabled_2862_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object* v_treesSaved_2874_, lean_object* v_modifyInfoState_2875_, lean_object* v_tree_2876_){
_start:
{
lean_object* v___f_2877_; lean_object* v___x_2878_; 
v___f_2877_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2877_, 0, v_treesSaved_2874_);
lean_closure_set(v___f_2877_, 1, v_tree_2876_);
v___x_2878_ = lean_apply_1(v_modifyInfoState_2875_, v___f_2877_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object* v_mkInfoTree_2879_, lean_object* v_toBind_2880_, lean_object* v___f_2881_, lean_object* v_st_2882_){
_start:
{
lean_object* v_trees_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v_trees_2883_ = lean_ctor_get(v_st_2882_, 2);
lean_inc_ref(v_trees_2883_);
lean_dec_ref(v_st_2882_);
v___x_2884_ = lean_apply_1(v_mkInfoTree_2879_, v_trees_2883_);
v___x_2885_ = lean_apply_4(v_toBind_2880_, lean_box(0), lean_box(0), v___x_2884_, v___f_2881_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object* v_toBind_2886_, lean_object* v_getInfoState_2887_, lean_object* v___f_2888_, lean_object* v_x_2889_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = lean_apply_4(v_toBind_2886_, lean_box(0), lean_box(0), v_getInfoState_2887_, v___f_2888_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object* v_toBind_2891_, lean_object* v_getInfoState_2892_, lean_object* v___f_2893_, lean_object* v_x_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(v_toBind_2891_, v_getInfoState_2892_, v___f_2893_, v_x_2894_);
lean_dec(v_x_2894_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object* v_toFunctor_2896_, lean_object* v_modifyInfoState_2897_, lean_object* v_mkInfoTree_2898_, lean_object* v_toBind_2899_, lean_object* v_getInfoState_2900_, lean_object* v_inst_2901_, lean_object* v_x_2902_, lean_object* v___f_2903_, lean_object* v_treesSaved_2904_){
_start:
{
lean_object* v_map_2905_; lean_object* v___f_2906_; lean_object* v___f_2907_; lean_object* v___f_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v_map_2905_ = lean_ctor_get(v_toFunctor_2896_, 0);
lean_inc(v_map_2905_);
lean_dec_ref(v_toFunctor_2896_);
v___f_2906_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2906_, 0, v_treesSaved_2904_);
lean_closure_set(v___f_2906_, 1, v_modifyInfoState_2897_);
lean_inc(v_toBind_2899_);
v___f_2907_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2907_, 0, v_mkInfoTree_2898_);
lean_closure_set(v___f_2907_, 1, v_toBind_2899_);
lean_closure_set(v___f_2907_, 2, v___f_2906_);
v___f_2908_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_2908_, 0, v_toBind_2899_);
lean_closure_set(v___f_2908_, 1, v_getInfoState_2900_);
lean_closure_set(v___f_2908_, 2, v___f_2907_);
v___x_2909_ = lean_apply_4(v_inst_2901_, lean_box(0), lean_box(0), v_x_2902_, v___f_2908_);
v___x_2910_ = lean_apply_4(v_map_2905_, lean_box(0), lean_box(0), v___f_2903_, v___x_2909_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object* v_inst_2911_, lean_object* v_inst_2912_, lean_object* v_inst_2913_, lean_object* v_x_2914_, lean_object* v_mkInfoTree_2915_){
_start:
{
lean_object* v_toApplicative_2916_; lean_object* v_toBind_2917_; lean_object* v_getInfoState_2918_; lean_object* v_modifyInfoState_2919_; lean_object* v_toFunctor_2920_; lean_object* v___f_2921_; lean_object* v___f_2922_; lean_object* v___f_2923_; lean_object* v___x_2924_; 
v_toApplicative_2916_ = lean_ctor_get(v_inst_2911_, 0);
v_toBind_2917_ = lean_ctor_get(v_inst_2911_, 1);
lean_inc_n(v_toBind_2917_, 3);
v_getInfoState_2918_ = lean_ctor_get(v_inst_2912_, 0);
lean_inc_n(v_getInfoState_2918_, 2);
v_modifyInfoState_2919_ = lean_ctor_get(v_inst_2912_, 1);
v_toFunctor_2920_ = lean_ctor_get(v_toApplicative_2916_, 0);
v___f_2921_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2914_);
lean_inc(v_modifyInfoState_2919_);
lean_inc_ref(v_toFunctor_2920_);
v___f_2922_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2922_, 0, v_toFunctor_2920_);
lean_closure_set(v___f_2922_, 1, v_modifyInfoState_2919_);
lean_closure_set(v___f_2922_, 2, v_mkInfoTree_2915_);
lean_closure_set(v___f_2922_, 3, v_toBind_2917_);
lean_closure_set(v___f_2922_, 4, v_getInfoState_2918_);
lean_closure_set(v___f_2922_, 5, v_inst_2913_);
lean_closure_set(v___f_2922_, 6, v_x_2914_);
lean_closure_set(v___f_2922_, 7, v___f_2921_);
v___f_2923_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2923_, 0, v_x_2914_);
lean_closure_set(v___f_2923_, 1, v_inst_2911_);
lean_closure_set(v___f_2923_, 2, v_inst_2912_);
lean_closure_set(v___f_2923_, 3, v_toBind_2917_);
lean_closure_set(v___f_2923_, 4, v___f_2922_);
v___x_2924_ = lean_apply_4(v_toBind_2917_, lean_box(0), lean_box(0), v_getInfoState_2918_, v___f_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object* v_m_2925_, lean_object* v_inst_2926_, lean_object* v_inst_2927_, lean_object* v_00_u03b1_2928_, lean_object* v_inst_2929_, lean_object* v_x_2930_, lean_object* v_mkInfoTree_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_2926_, v_inst_2927_, v_inst_2929_, v_x_2930_, v_mkInfoTree_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object* v_trees_2933_, lean_object* v_toPure_2934_, lean_object* v_____do__lift_2935_){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2936_, 0, v_____do__lift_2935_);
lean_ctor_set(v___x_2936_, 1, v_trees_2933_);
v___x_2937_ = lean_apply_2(v_toPure_2934_, lean_box(0), v___x_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object* v_toPure_2938_, lean_object* v_toBind_2939_, lean_object* v_mkInfo_2940_, lean_object* v_trees_2941_){
_start:
{
lean_object* v___f_2942_; lean_object* v___x_2943_; 
v___f_2942_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2942_, 0, v_trees_2941_);
lean_closure_set(v___f_2942_, 1, v_toPure_2938_);
v___x_2943_ = lean_apply_4(v_toBind_2939_, lean_box(0), lean_box(0), v_mkInfo_2940_, v___f_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object* v_inst_2944_, lean_object* v_inst_2945_, lean_object* v_inst_2946_, lean_object* v_x_2947_, lean_object* v_mkInfo_2948_){
_start:
{
lean_object* v_toApplicative_2949_; lean_object* v_toBind_2950_; lean_object* v_toPure_2951_; lean_object* v___f_2952_; lean_object* v___x_2953_; 
v_toApplicative_2949_ = lean_ctor_get(v_inst_2944_, 0);
v_toBind_2950_ = lean_ctor_get(v_inst_2944_, 1);
v_toPure_2951_ = lean_ctor_get(v_toApplicative_2949_, 1);
lean_inc(v_toBind_2950_);
lean_inc(v_toPure_2951_);
v___f_2952_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2952_, 0, v_toPure_2951_);
lean_closure_set(v___f_2952_, 1, v_toBind_2950_);
lean_closure_set(v___f_2952_, 2, v_mkInfo_2948_);
v___x_2953_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_2944_, v_inst_2945_, v_inst_2946_, v_x_2947_, v___f_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object* v_m_2954_, lean_object* v_inst_2955_, lean_object* v_inst_2956_, lean_object* v_00_u03b1_2957_, lean_object* v_inst_2958_, lean_object* v_x_2959_, lean_object* v_mkInfo_2960_){
_start:
{
lean_object* v_toApplicative_2961_; lean_object* v_toBind_2962_; lean_object* v_toPure_2963_; lean_object* v___f_2964_; lean_object* v___x_2965_; 
v_toApplicative_2961_ = lean_ctor_get(v_inst_2955_, 0);
v_toBind_2962_ = lean_ctor_get(v_inst_2955_, 1);
v_toPure_2963_ = lean_ctor_get(v_toApplicative_2961_, 1);
lean_inc(v_toBind_2962_);
lean_inc(v_toPure_2963_);
v___f_2964_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2964_, 0, v_toPure_2963_);
lean_closure_set(v___f_2964_, 1, v_toBind_2962_);
lean_closure_set(v___f_2964_, 2, v_mkInfo_2960_);
v___x_2965_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_2955_, v_inst_2956_, v_inst_2958_, v_x_2959_, v___f_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object* v_treesSaved_2966_, lean_object* v_trees_2967_, lean_object* v_s_2968_){
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
v___x_2975_ = l_Lean_PersistentArray_append___redArg(v_treesSaved_2966_, v_trees_2967_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object* v_treesSaved_2981_, lean_object* v_trees_2982_, lean_object* v_s_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_2981_, v_trees_2982_, v_s_2983_);
lean_dec_ref(v_trees_2982_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object* v_treesSaved_2985_, lean_object* v_modifyInfoState_2986_, lean_object* v_trees_2987_){
_start:
{
lean_object* v___f_2988_; lean_object* v___x_2989_; 
v___f_2988_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2988_, 0, v_treesSaved_2985_);
lean_closure_set(v___f_2988_, 1, v_trees_2987_);
v___x_2989_ = lean_apply_1(v_modifyInfoState_2986_, v___f_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object* v_toPure_2990_, lean_object* v_tree_2991_, lean_object* v_____do__lift_2992_){
_start:
{
if (lean_obj_tag(v_____do__lift_2992_) == 0)
{
lean_object* v___x_2993_; 
v___x_2993_ = lean_apply_2(v_toPure_2990_, lean_box(0), v_tree_2991_);
return v___x_2993_;
}
else
{
lean_object* v_val_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v_val_2994_ = lean_ctor_get(v_____do__lift_2992_, 0);
lean_inc(v_val_2994_);
v___x_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2995_, 0, v_val_2994_);
lean_ctor_set(v___x_2995_, 1, v_tree_2991_);
v___x_2996_ = lean_apply_2(v_toPure_2990_, lean_box(0), v___x_2995_);
return v___x_2996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object* v_toPure_2997_, lean_object* v_tree_2998_, lean_object* v_____do__lift_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_2997_, v_tree_2998_, v_____do__lift_2999_);
lean_dec(v_____do__lift_2999_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object* v_assignment_3001_, lean_object* v_toPure_3002_, lean_object* v_toBind_3003_, lean_object* v_ctx_x3f_3004_, lean_object* v_tree_3005_){
_start:
{
lean_object* v_tree_3006_; lean_object* v___f_3007_; lean_object* v___x_3008_; 
v_tree_3006_ = l_Lean_Elab_InfoTree_substitute(v_tree_3005_, v_assignment_3001_);
v___f_3007_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3007_, 0, v_toPure_3002_);
lean_closure_set(v___f_3007_, 1, v_tree_3006_);
v___x_3008_ = lean_apply_4(v_toBind_3003_, lean_box(0), lean_box(0), v_ctx_x3f_3004_, v___f_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object* v_assignment_3009_, lean_object* v_toPure_3010_, lean_object* v_toBind_3011_, lean_object* v_ctx_x3f_3012_, lean_object* v_tree_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(v_assignment_3009_, v_toPure_3010_, v_toBind_3011_, v_ctx_x3f_3012_, v_tree_3013_);
lean_dec_ref(v_assignment_3009_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object* v_toPure_3015_, lean_object* v_toBind_3016_, lean_object* v_ctx_x3f_3017_, lean_object* v_inst_3018_, lean_object* v___f_3019_, lean_object* v_st_3020_){
_start:
{
lean_object* v_assignment_3021_; lean_object* v_trees_3022_; lean_object* v___f_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v_assignment_3021_ = lean_ctor_get(v_st_3020_, 0);
lean_inc_ref(v_assignment_3021_);
v_trees_3022_ = lean_ctor_get(v_st_3020_, 2);
lean_inc_ref(v_trees_3022_);
lean_dec_ref(v_st_3020_);
lean_inc(v_toBind_3016_);
v___f_3023_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_3023_, 0, v_assignment_3021_);
lean_closure_set(v___f_3023_, 1, v_toPure_3015_);
lean_closure_set(v___f_3023_, 2, v_toBind_3016_);
lean_closure_set(v___f_3023_, 3, v_ctx_x3f_3017_);
v___x_3024_ = l_Lean_PersistentArray_mapM___redArg(v_inst_3018_, v___f_3023_, v_trees_3022_);
v___x_3025_ = lean_apply_4(v_toBind_3016_, lean_box(0), lean_box(0), v___x_3024_, v___f_3019_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object* v_toFunctor_3026_, lean_object* v_modifyInfoState_3027_, lean_object* v_toPure_3028_, lean_object* v_toBind_3029_, lean_object* v_ctx_x3f_3030_, lean_object* v_inst_3031_, lean_object* v_getInfoState_3032_, lean_object* v_inst_3033_, lean_object* v_x_3034_, lean_object* v___f_3035_, lean_object* v_treesSaved_3036_){
_start:
{
lean_object* v_map_3037_; lean_object* v___f_3038_; lean_object* v___f_3039_; lean_object* v___f_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v_map_3037_ = lean_ctor_get(v_toFunctor_3026_, 0);
lean_inc(v_map_3037_);
lean_dec_ref(v_toFunctor_3026_);
v___f_3038_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3038_, 0, v_treesSaved_3036_);
lean_closure_set(v___f_3038_, 1, v_modifyInfoState_3027_);
lean_inc(v_toBind_3029_);
v___f_3039_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4), 6, 5);
lean_closure_set(v___f_3039_, 0, v_toPure_3028_);
lean_closure_set(v___f_3039_, 1, v_toBind_3029_);
lean_closure_set(v___f_3039_, 2, v_ctx_x3f_3030_);
lean_closure_set(v___f_3039_, 3, v_inst_3031_);
lean_closure_set(v___f_3039_, 4, v___f_3038_);
v___f_3040_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3040_, 0, v_toBind_3029_);
lean_closure_set(v___f_3040_, 1, v_getInfoState_3032_);
lean_closure_set(v___f_3040_, 2, v___f_3039_);
v___x_3041_ = lean_apply_4(v_inst_3033_, lean_box(0), lean_box(0), v_x_3034_, v___f_3040_);
v___x_3042_ = lean_apply_4(v_map_3037_, lean_box(0), lean_box(0), v___f_3035_, v___x_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object* v_inst_3043_, lean_object* v_inst_3044_, lean_object* v_inst_3045_, lean_object* v_x_3046_, lean_object* v_ctx_x3f_3047_){
_start:
{
lean_object* v_toApplicative_3048_; lean_object* v_toBind_3049_; lean_object* v_getInfoState_3050_; lean_object* v_modifyInfoState_3051_; lean_object* v_toFunctor_3052_; lean_object* v_toPure_3053_; lean_object* v___f_3054_; lean_object* v___f_3055_; lean_object* v___f_3056_; lean_object* v___x_3057_; 
v_toApplicative_3048_ = lean_ctor_get(v_inst_3043_, 0);
v_toBind_3049_ = lean_ctor_get(v_inst_3043_, 1);
lean_inc_n(v_toBind_3049_, 3);
v_getInfoState_3050_ = lean_ctor_get(v_inst_3044_, 0);
lean_inc_n(v_getInfoState_3050_, 2);
v_modifyInfoState_3051_ = lean_ctor_get(v_inst_3044_, 1);
v_toFunctor_3052_ = lean_ctor_get(v_toApplicative_3048_, 0);
v_toPure_3053_ = lean_ctor_get(v_toApplicative_3048_, 1);
v___f_3054_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3046_);
lean_inc_ref(v_inst_3043_);
lean_inc(v_toPure_3053_);
lean_inc(v_modifyInfoState_3051_);
lean_inc_ref(v_toFunctor_3052_);
v___f_3055_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6), 11, 10);
lean_closure_set(v___f_3055_, 0, v_toFunctor_3052_);
lean_closure_set(v___f_3055_, 1, v_modifyInfoState_3051_);
lean_closure_set(v___f_3055_, 2, v_toPure_3053_);
lean_closure_set(v___f_3055_, 3, v_toBind_3049_);
lean_closure_set(v___f_3055_, 4, v_ctx_x3f_3047_);
lean_closure_set(v___f_3055_, 5, v_inst_3043_);
lean_closure_set(v___f_3055_, 6, v_getInfoState_3050_);
lean_closure_set(v___f_3055_, 7, v_inst_3045_);
lean_closure_set(v___f_3055_, 8, v_x_3046_);
lean_closure_set(v___f_3055_, 9, v___f_3054_);
v___f_3056_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3056_, 0, v_x_3046_);
lean_closure_set(v___f_3056_, 1, v_inst_3043_);
lean_closure_set(v___f_3056_, 2, v_inst_3044_);
lean_closure_set(v___f_3056_, 3, v_toBind_3049_);
lean_closure_set(v___f_3056_, 4, v___f_3055_);
v___x_3057_ = lean_apply_4(v_toBind_3049_, lean_box(0), lean_box(0), v_getInfoState_3050_, v___f_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object* v_m_3058_, lean_object* v_inst_3059_, lean_object* v_inst_3060_, lean_object* v_00_u03b1_3061_, lean_object* v_inst_3062_, lean_object* v_x_3063_, lean_object* v_ctx_x3f_3064_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3059_, v_inst_3060_, v_inst_3062_, v_x_3063_, v_ctx_x3f_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object* v_toPure_3066_, lean_object* v_____do__lift_3067_){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3068_, 0, v_____do__lift_3067_);
v___x_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
v___x_3070_ = lean_apply_2(v_toPure_3066_, lean_box(0), v___x_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object* v_inst_3071_, lean_object* v_inst_3072_, lean_object* v_inst_3073_, lean_object* v_inst_3074_, lean_object* v_inst_3075_, lean_object* v_inst_3076_, lean_object* v_inst_3077_, lean_object* v_inst_3078_, lean_object* v_inst_3079_, lean_object* v_x_3080_){
_start:
{
lean_object* v_toApplicative_3081_; lean_object* v_toBind_3082_; lean_object* v_toPure_3083_; lean_object* v___x_3084_; lean_object* v___f_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v_toApplicative_3081_ = lean_ctor_get(v_inst_3071_, 0);
v_toBind_3082_ = lean_ctor_get(v_inst_3071_, 1);
v_toPure_3083_ = lean_ctor_get(v_toApplicative_3081_, 1);
lean_inc_ref(v_inst_3071_);
v___x_3084_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_3071_, v_inst_3075_, v_inst_3077_, v_inst_3076_, v_inst_3078_, v_inst_3073_, v_inst_3079_);
lean_inc(v_toPure_3083_);
v___f_3085_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3085_, 0, v_toPure_3083_);
lean_inc(v_toBind_3082_);
v___x_3086_ = lean_apply_4(v_toBind_3082_, lean_box(0), lean_box(0), v___x_3084_, v___f_3085_);
v___x_3087_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3071_, v_inst_3072_, v_inst_3074_, v_x_3080_, v___x_3086_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object* v_m_3088_, lean_object* v_inst_3089_, lean_object* v_inst_3090_, lean_object* v_00_u03b1_3091_, lean_object* v_inst_3092_, lean_object* v_inst_3093_, lean_object* v_inst_3094_, lean_object* v_inst_3095_, lean_object* v_inst_3096_, lean_object* v_inst_3097_, lean_object* v_inst_3098_, lean_object* v_x_3099_){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = l_Lean_Elab_withSaveInfoContext___redArg(v_inst_3089_, v_inst_3090_, v_inst_3092_, v_inst_3093_, v_inst_3094_, v_inst_3095_, v_inst_3096_, v_inst_3097_, v_inst_3098_, v_x_3099_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object* v_toPure_3101_, lean_object* v_____x_3102_){
_start:
{
if (lean_obj_tag(v_____x_3102_) == 1)
{
lean_object* v_val_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3112_; 
v_val_3103_ = lean_ctor_get(v_____x_3102_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_____x_3102_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3105_ = v_____x_3102_;
v_isShared_3106_ = v_isSharedCheck_3112_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_val_3103_);
lean_dec(v_____x_3102_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3112_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3107_; lean_object* v___x_3109_; 
v___x_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3107_, 0, v_val_3103_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v___x_3107_);
v___x_3109_ = v___x_3105_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3107_);
v___x_3109_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
lean_object* v___x_3110_; 
v___x_3110_ = lean_apply_2(v_toPure_3101_, lean_box(0), v___x_3109_);
return v___x_3110_;
}
}
}
else
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
lean_dec(v_____x_3102_);
v___x_3113_ = lean_box(0);
v___x_3114_ = lean_apply_2(v_toPure_3101_, lean_box(0), v___x_3113_);
return v___x_3114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object* v_inst_3115_, lean_object* v_inst_3116_, lean_object* v_inst_3117_, lean_object* v_inst_3118_, lean_object* v_x_3119_){
_start:
{
lean_object* v_toApplicative_3120_; lean_object* v_toBind_3121_; lean_object* v_toPure_3122_; lean_object* v___f_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v_toApplicative_3120_ = lean_ctor_get(v_inst_3115_, 0);
v_toBind_3121_ = lean_ctor_get(v_inst_3115_, 1);
v_toPure_3122_ = lean_ctor_get(v_toApplicative_3120_, 1);
lean_inc(v_toPure_3122_);
v___f_3123_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3123_, 0, v_toPure_3122_);
lean_inc(v_toBind_3121_);
v___x_3124_ = lean_apply_4(v_toBind_3121_, lean_box(0), lean_box(0), v_inst_3118_, v___f_3123_);
v___x_3125_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3115_, v_inst_3116_, v_inst_3117_, v_x_3119_, v___x_3124_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object* v_m_3126_, lean_object* v_inst_3127_, lean_object* v_inst_3128_, lean_object* v_00_u03b1_3129_, lean_object* v_inst_3130_, lean_object* v_inst_3131_, lean_object* v_x_3132_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(v_inst_3127_, v_inst_3128_, v_inst_3130_, v_inst_3131_, v_x_3132_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object* v_toPure_3134_, lean_object* v_autoImplicits_3135_){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3136_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3136_, 0, v_autoImplicits_3135_);
v___x_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
v___x_3138_ = lean_apply_2(v_toPure_3134_, lean_box(0), v___x_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object* v_inst_3139_, lean_object* v_inst_3140_, lean_object* v_inst_3141_, lean_object* v_inst_3142_, lean_object* v_x_3143_){
_start:
{
lean_object* v_toApplicative_3144_; lean_object* v_toBind_3145_; lean_object* v_toPure_3146_; lean_object* v___f_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v_toApplicative_3144_ = lean_ctor_get(v_inst_3139_, 0);
v_toBind_3145_ = lean_ctor_get(v_inst_3139_, 1);
v_toPure_3146_ = lean_ctor_get(v_toApplicative_3144_, 1);
lean_inc(v_toPure_3146_);
v___f_3147_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3147_, 0, v_toPure_3146_);
lean_inc(v_toBind_3145_);
v___x_3148_ = lean_apply_4(v_toBind_3145_, lean_box(0), lean_box(0), v_inst_3142_, v___f_3147_);
v___x_3149_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3139_, v_inst_3140_, v_inst_3141_, v_x_3143_, v___x_3148_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object* v_m_3150_, lean_object* v_inst_3151_, lean_object* v_inst_3152_, lean_object* v_00_u03b1_3153_, lean_object* v_inst_3154_, lean_object* v_inst_3155_, lean_object* v_x_3156_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(v_inst_3151_, v_inst_3152_, v_inst_3154_, v_inst_3155_, v_x_3156_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object* v___x_3158_, lean_object* v___x_3159_, lean_object* v_mvarId_3160_, lean_object* v_toPure_3161_, lean_object* v_____do__lift_3162_){
_start:
{
lean_object* v_assignment_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v_assignment_3163_ = lean_ctor_get(v_____do__lift_3162_, 0);
v___x_3164_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_3158_, v___x_3159_, v_assignment_3163_, v_mvarId_3160_);
v___x_3165_ = lean_apply_2(v_toPure_3161_, lean_box(0), v___x_3164_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object* v___x_3166_, lean_object* v___x_3167_, lean_object* v_mvarId_3168_, lean_object* v_toPure_3169_, lean_object* v_____do__lift_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(v___x_3166_, v___x_3167_, v_mvarId_3168_, v_toPure_3169_, v_____do__lift_3170_);
lean_dec_ref(v_____do__lift_3170_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object* v_inst_3174_, lean_object* v_inst_3175_, lean_object* v_mvarId_3176_){
_start:
{
lean_object* v_toApplicative_3177_; lean_object* v_toBind_3178_; lean_object* v_getInfoState_3179_; lean_object* v_toPure_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___f_3183_; lean_object* v___x_3184_; 
v_toApplicative_3177_ = lean_ctor_get(v_inst_3174_, 0);
lean_inc_ref(v_toApplicative_3177_);
v_toBind_3178_ = lean_ctor_get(v_inst_3174_, 1);
lean_inc(v_toBind_3178_);
lean_dec_ref(v_inst_3174_);
v_getInfoState_3179_ = lean_ctor_get(v_inst_3175_, 0);
lean_inc(v_getInfoState_3179_);
lean_dec_ref(v_inst_3175_);
v_toPure_3180_ = lean_ctor_get(v_toApplicative_3177_, 1);
lean_inc(v_toPure_3180_);
lean_dec_ref(v_toApplicative_3177_);
v___x_3181_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3182_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___f_3183_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3183_, 0, v___x_3181_);
lean_closure_set(v___f_3183_, 1, v___x_3182_);
lean_closure_set(v___f_3183_, 2, v_mvarId_3176_);
lean_closure_set(v___f_3183_, 3, v_toPure_3180_);
v___x_3184_ = lean_apply_4(v_toBind_3178_, lean_box(0), lean_box(0), v_getInfoState_3179_, v___f_3183_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* v_m_3185_, lean_object* v_inst_3186_, lean_object* v_inst_3187_, lean_object* v_mvarId_3188_){
_start:
{
lean_object* v___x_3189_; 
v___x_3189_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3186_, v_inst_3187_, v_mvarId_3188_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object* v___x_3190_, lean_object* v___x_3191_, lean_object* v_mvarId_3192_, lean_object* v_infoTree_3193_, lean_object* v_s_3194_){
_start:
{
uint8_t v_enabled_3195_; lean_object* v_assignment_3196_; lean_object* v_lazyAssignment_3197_; lean_object* v_trees_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3206_; 
v_enabled_3195_ = lean_ctor_get_uint8(v_s_3194_, sizeof(void*)*3);
v_assignment_3196_ = lean_ctor_get(v_s_3194_, 0);
v_lazyAssignment_3197_ = lean_ctor_get(v_s_3194_, 1);
v_trees_3198_ = lean_ctor_get(v_s_3194_, 2);
v_isSharedCheck_3206_ = !lean_is_exclusive(v_s_3194_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3200_ = v_s_3194_;
v_isShared_3201_ = v_isSharedCheck_3206_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_trees_3198_);
lean_inc(v_lazyAssignment_3197_);
lean_inc(v_assignment_3196_);
lean_dec(v_s_3194_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3206_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3202_; lean_object* v___x_3204_; 
v___x_3202_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3190_, v___x_3191_, v_assignment_3196_, v_mvarId_3192_, v_infoTree_3193_);
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 0, v___x_3202_);
v___x_3204_ = v___x_3200_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v_lazyAssignment_3197_);
lean_ctor_set(v_reuseFailAlloc_3205_, 2, v_trees_3198_);
lean_ctor_set_uint8(v_reuseFailAlloc_3205_, sizeof(void*)*3, v_enabled_3195_);
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
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3210_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2));
v___x_3211_ = lean_unsigned_to_nat(2u);
v___x_3212_ = lean_unsigned_to_nat(380u);
v___x_3213_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1));
v___x_3214_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0));
v___x_3215_ = l_mkPanicMessageWithDecl(v___x_3214_, v___x_3213_, v___x_3212_, v___x_3211_, v___x_3210_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object* v_inst_3216_, lean_object* v___f_3217_, lean_object* v___x_3218_, lean_object* v_____do__lift_3219_){
_start:
{
if (lean_obj_tag(v_____do__lift_3219_) == 0)
{
lean_object* v_modifyInfoState_3220_; lean_object* v___x_3221_; 
v_modifyInfoState_3220_ = lean_ctor_get(v_inst_3216_, 1);
lean_inc(v_modifyInfoState_3220_);
lean_dec_ref(v_inst_3216_);
v___x_3221_ = lean_apply_1(v_modifyInfoState_3220_, v___f_3217_);
return v___x_3221_;
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_dec_ref(v___f_3217_);
lean_dec_ref(v_inst_3216_);
v___x_3222_ = lean_obj_once(&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3, &l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3_once, _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3);
v___x_3223_ = l_panic___redArg(v___x_3218_, v___x_3222_);
return v___x_3223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object* v_inst_3224_, lean_object* v___f_3225_, lean_object* v___x_3226_, lean_object* v_____do__lift_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(v_inst_3224_, v___f_3225_, v___x_3226_, v_____do__lift_3227_);
lean_dec(v_____do__lift_3227_);
lean_dec(v___x_3226_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object* v_inst_3229_, lean_object* v_inst_3230_, lean_object* v_mvarId_3231_, lean_object* v_infoTree_3232_){
_start:
{
lean_object* v_toBind_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___f_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___f_3240_; lean_object* v___x_3241_; 
v_toBind_3233_ = lean_ctor_get(v_inst_3229_, 1);
lean_inc(v_toBind_3233_);
v___x_3234_ = lean_box(0);
v___x_3235_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3236_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
lean_inc(v_mvarId_3231_);
v___f_3237_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__0), 5, 4);
lean_closure_set(v___f_3237_, 0, v___x_3235_);
lean_closure_set(v___f_3237_, 1, v___x_3236_);
lean_closure_set(v___f_3237_, 2, v_mvarId_3231_);
lean_closure_set(v___f_3237_, 3, v_infoTree_3232_);
lean_inc_ref(v_inst_3230_);
lean_inc_ref(v_inst_3229_);
v___x_3238_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3229_, v_inst_3230_, v_mvarId_3231_);
v___x_3239_ = l_instInhabitedOfMonad___redArg(v_inst_3229_, v___x_3234_);
v___f_3240_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3240_, 0, v_inst_3230_);
lean_closure_set(v___f_3240_, 1, v___f_3237_);
lean_closure_set(v___f_3240_, 2, v___x_3239_);
v___x_3241_ = lean_apply_4(v_toBind_3233_, lean_box(0), lean_box(0), v___x_3238_, v___f_3240_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* v_m_3242_, lean_object* v_inst_3243_, lean_object* v_inst_3244_, lean_object* v_mvarId_3245_, lean_object* v_infoTree_3246_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Lean_Elab_assignInfoHoleId___redArg(v_inst_3243_, v_inst_3244_, v_mvarId_3245_, v_infoTree_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object* v_stx_3248_, lean_object* v_output_3249_, lean_object* v_toPure_3250_, lean_object* v_____do__lift_3251_){
_start:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3252_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3252_, 0, v_____do__lift_3251_);
lean_ctor_set(v___x_3252_, 1, v_stx_3248_);
lean_ctor_set(v___x_3252_, 2, v_output_3249_);
v___x_3253_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3252_);
v___x_3254_ = lean_apply_2(v_toPure_3250_, lean_box(0), v___x_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object* v_inst_3255_, lean_object* v_inst_3256_, lean_object* v_inst_3257_, lean_object* v_inst_3258_, lean_object* v_stx_3259_, lean_object* v_output_3260_, lean_object* v_x_3261_){
_start:
{
lean_object* v_toApplicative_3262_; lean_object* v_toBind_3263_; lean_object* v_toPure_3264_; lean_object* v___f_3265_; lean_object* v_mkInfo_3266_; lean_object* v___f_3267_; lean_object* v___x_3268_; 
v_toApplicative_3262_ = lean_ctor_get(v_inst_3256_, 0);
v_toBind_3263_ = lean_ctor_get(v_inst_3256_, 1);
v_toPure_3264_ = lean_ctor_get(v_toApplicative_3262_, 1);
lean_inc_n(v_toPure_3264_, 2);
v___f_3265_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3265_, 0, v_stx_3259_);
lean_closure_set(v___f_3265_, 1, v_output_3260_);
lean_closure_set(v___f_3265_, 2, v_toPure_3264_);
lean_inc_n(v_toBind_3263_, 2);
v_mkInfo_3266_ = lean_apply_4(v_toBind_3263_, lean_box(0), lean_box(0), v_inst_3258_, v___f_3265_);
v___f_3267_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3267_, 0, v_toPure_3264_);
lean_closure_set(v___f_3267_, 1, v_toBind_3263_);
lean_closure_set(v___f_3267_, 2, v_mkInfo_3266_);
v___x_3268_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3256_, v_inst_3257_, v_inst_3255_, v_x_3261_, v___f_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* v_m_3269_, lean_object* v_00_u03b1_3270_, lean_object* v_inst_3271_, lean_object* v_inst_3272_, lean_object* v_inst_3273_, lean_object* v_inst_3274_, lean_object* v_stx_3275_, lean_object* v_output_3276_, lean_object* v_x_3277_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l_Lean_Elab_withMacroExpansionInfo___redArg(v_inst_3271_, v_inst_3272_, v_inst_3273_, v_inst_3274_, v_stx_3275_, v_output_3276_, v_x_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object* v_treesSaved_3279_, lean_object* v___x_3280_, lean_object* v___x_3281_, lean_object* v___x_3282_, lean_object* v_mvarId_3283_, lean_object* v_s_3284_){
_start:
{
lean_object* v_trees_3285_; uint8_t v_enabled_3286_; lean_object* v_assignment_3287_; lean_object* v_lazyAssignment_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3305_; 
v_trees_3285_ = lean_ctor_get(v_s_3284_, 2);
v_enabled_3286_ = lean_ctor_get_uint8(v_s_3284_, sizeof(void*)*3);
v_assignment_3287_ = lean_ctor_get(v_s_3284_, 0);
v_lazyAssignment_3288_ = lean_ctor_get(v_s_3284_, 1);
v_isSharedCheck_3305_ = !lean_is_exclusive(v_s_3284_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3290_ = v_s_3284_;
v_isShared_3291_ = v_isSharedCheck_3305_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_trees_3285_);
lean_inc(v_lazyAssignment_3288_);
lean_inc(v_assignment_3287_);
lean_dec(v_s_3284_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3305_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v_size_3292_; lean_object* v___x_3293_; uint8_t v___x_3294_; 
v_size_3292_ = lean_ctor_get(v_trees_3285_, 2);
v___x_3293_ = lean_unsigned_to_nat(0u);
v___x_3294_ = lean_nat_dec_lt(v___x_3293_, v_size_3292_);
if (v___x_3294_ == 0)
{
lean_object* v___x_3296_; 
lean_dec_ref(v_trees_3285_);
lean_dec(v_mvarId_3283_);
lean_dec_ref(v___x_3282_);
lean_dec_ref(v___x_3281_);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 2, v_treesSaved_3279_);
v___x_3296_ = v___x_3290_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_assignment_3287_);
lean_ctor_set(v_reuseFailAlloc_3297_, 1, v_lazyAssignment_3288_);
lean_ctor_set(v_reuseFailAlloc_3297_, 2, v_treesSaved_3279_);
lean_ctor_set_uint8(v_reuseFailAlloc_3297_, sizeof(void*)*3, v_enabled_3286_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
else
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3303_; 
v___x_3298_ = lean_unsigned_to_nat(1u);
v___x_3299_ = lean_nat_sub(v_size_3292_, v___x_3298_);
v___x_3300_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3280_, v_trees_3285_, v___x_3299_);
lean_dec(v___x_3299_);
lean_dec_ref(v_trees_3285_);
v___x_3301_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3281_, v___x_3282_, v_assignment_3287_, v_mvarId_3283_, v___x_3300_);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 2, v_treesSaved_3279_);
lean_ctor_set(v___x_3290_, 0, v___x_3301_);
v___x_3303_ = v___x_3290_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3301_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_lazyAssignment_3288_);
lean_ctor_set(v_reuseFailAlloc_3304_, 2, v_treesSaved_3279_);
lean_ctor_set_uint8(v_reuseFailAlloc_3304_, sizeof(void*)*3, v_enabled_3286_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1___boxed(lean_object* v_treesSaved_3306_, lean_object* v___x_3307_, lean_object* v___x_3308_, lean_object* v___x_3309_, lean_object* v_mvarId_3310_, lean_object* v_s_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Lean_Elab_withInfoHole___redArg___lam__1(v_treesSaved_3306_, v___x_3307_, v___x_3308_, v___x_3309_, v_mvarId_3310_, v_s_3311_);
lean_dec_ref(v___x_3307_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object* v_modifyInfoState_3313_, lean_object* v___f_3314_, lean_object* v_x_3315_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = lean_apply_1(v_modifyInfoState_3313_, v___f_3314_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object* v_modifyInfoState_3317_, lean_object* v___f_3318_, lean_object* v_x_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_3317_, v___f_3318_, v_x_3319_);
lean_dec(v_x_3319_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object* v_toFunctor_3321_, lean_object* v___x_3322_, lean_object* v___x_3323_, lean_object* v___x_3324_, lean_object* v_mvarId_3325_, lean_object* v_modifyInfoState_3326_, lean_object* v_inst_3327_, lean_object* v_x_3328_, lean_object* v___f_3329_, lean_object* v_treesSaved_3330_){
_start:
{
lean_object* v_map_3331_; lean_object* v___f_3332_; lean_object* v___f_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v_map_3331_ = lean_ctor_get(v_toFunctor_3321_, 0);
lean_inc(v_map_3331_);
lean_dec_ref(v_toFunctor_3321_);
v___f_3332_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_3332_, 0, v_treesSaved_3330_);
lean_closure_set(v___f_3332_, 1, v___x_3322_);
lean_closure_set(v___f_3332_, 2, v___x_3323_);
lean_closure_set(v___f_3332_, 3, v___x_3324_);
lean_closure_set(v___f_3332_, 4, v_mvarId_3325_);
v___f_3333_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3333_, 0, v_modifyInfoState_3326_);
lean_closure_set(v___f_3333_, 1, v___f_3332_);
v___x_3334_ = lean_apply_4(v_inst_3327_, lean_box(0), lean_box(0), v_x_3328_, v___f_3333_);
v___x_3335_ = lean_apply_4(v_map_3331_, lean_box(0), lean_box(0), v___f_3329_, v___x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object* v_inst_3336_, lean_object* v_inst_3337_, lean_object* v_inst_3338_, lean_object* v_mvarId_3339_, lean_object* v_x_3340_){
_start:
{
lean_object* v_toApplicative_3341_; lean_object* v_toBind_3342_; lean_object* v_getInfoState_3343_; lean_object* v_modifyInfoState_3344_; lean_object* v_toFunctor_3345_; lean_object* v___f_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___f_3350_; lean_object* v___f_3351_; lean_object* v___x_3352_; 
v_toApplicative_3341_ = lean_ctor_get(v_inst_3337_, 0);
v_toBind_3342_ = lean_ctor_get(v_inst_3337_, 1);
lean_inc_n(v_toBind_3342_, 2);
v_getInfoState_3343_ = lean_ctor_get(v_inst_3338_, 0);
lean_inc(v_getInfoState_3343_);
v_modifyInfoState_3344_ = lean_ctor_get(v_inst_3338_, 1);
v_toFunctor_3345_ = lean_ctor_get(v_toApplicative_3341_, 0);
v___f_3346_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
v___x_3347_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3348_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3349_ = l_Lean_Elab_instInhabitedInfoTree_default;
lean_inc(v_x_3340_);
lean_inc(v_modifyInfoState_3344_);
lean_inc_ref(v_toFunctor_3345_);
v___f_3350_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3350_, 0, v_toFunctor_3345_);
lean_closure_set(v___f_3350_, 1, v___x_3349_);
lean_closure_set(v___f_3350_, 2, v___x_3347_);
lean_closure_set(v___f_3350_, 3, v___x_3348_);
lean_closure_set(v___f_3350_, 4, v_mvarId_3339_);
lean_closure_set(v___f_3350_, 5, v_modifyInfoState_3344_);
lean_closure_set(v___f_3350_, 6, v_inst_3336_);
lean_closure_set(v___f_3350_, 7, v_x_3340_);
lean_closure_set(v___f_3350_, 8, v___f_3346_);
v___f_3351_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3351_, 0, v_x_3340_);
lean_closure_set(v___f_3351_, 1, v_inst_3337_);
lean_closure_set(v___f_3351_, 2, v_inst_3338_);
lean_closure_set(v___f_3351_, 3, v_toBind_3342_);
lean_closure_set(v___f_3351_, 4, v___f_3350_);
v___x_3352_ = lean_apply_4(v_toBind_3342_, lean_box(0), lean_box(0), v_getInfoState_3343_, v___f_3351_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object* v_m_3353_, lean_object* v_00_u03b1_3354_, lean_object* v_inst_3355_, lean_object* v_inst_3356_, lean_object* v_inst_3357_, lean_object* v_mvarId_3358_, lean_object* v_x_3359_){
_start:
{
lean_object* v_toApplicative_3360_; lean_object* v_toBind_3361_; lean_object* v_getInfoState_3362_; lean_object* v_modifyInfoState_3363_; lean_object* v_toFunctor_3364_; lean_object* v___f_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___f_3369_; lean_object* v___f_3370_; lean_object* v___x_3371_; 
v_toApplicative_3360_ = lean_ctor_get(v_inst_3356_, 0);
v_toBind_3361_ = lean_ctor_get(v_inst_3356_, 1);
lean_inc_n(v_toBind_3361_, 2);
v_getInfoState_3362_ = lean_ctor_get(v_inst_3357_, 0);
lean_inc(v_getInfoState_3362_);
v_modifyInfoState_3363_ = lean_ctor_get(v_inst_3357_, 1);
v_toFunctor_3364_ = lean_ctor_get(v_toApplicative_3360_, 0);
v___f_3365_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
v___x_3366_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3367_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3368_ = l_Lean_Elab_instInhabitedInfoTree_default;
lean_inc(v_x_3359_);
lean_inc(v_modifyInfoState_3363_);
lean_inc_ref(v_toFunctor_3364_);
v___f_3369_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3369_, 0, v_toFunctor_3364_);
lean_closure_set(v___f_3369_, 1, v___x_3368_);
lean_closure_set(v___f_3369_, 2, v___x_3366_);
lean_closure_set(v___f_3369_, 3, v___x_3367_);
lean_closure_set(v___f_3369_, 4, v_mvarId_3358_);
lean_closure_set(v___f_3369_, 5, v_modifyInfoState_3363_);
lean_closure_set(v___f_3369_, 6, v_inst_3355_);
lean_closure_set(v___f_3369_, 7, v_x_3359_);
lean_closure_set(v___f_3369_, 8, v___f_3365_);
v___f_3370_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3370_, 0, v_x_3359_);
lean_closure_set(v___f_3370_, 1, v_inst_3356_);
lean_closure_set(v___f_3370_, 2, v_inst_3357_);
lean_closure_set(v___f_3370_, 3, v_toBind_3361_);
lean_closure_set(v___f_3370_, 4, v___f_3369_);
v___x_3371_ = lean_apply_4(v_toBind_3361_, lean_box(0), lean_box(0), v_getInfoState_3362_, v___f_3370_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t v_flag_3372_, lean_object* v_s_3373_){
_start:
{
lean_object* v_assignment_3374_; lean_object* v_lazyAssignment_3375_; lean_object* v_trees_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
v_assignment_3374_ = lean_ctor_get(v_s_3373_, 0);
v_lazyAssignment_3375_ = lean_ctor_get(v_s_3373_, 1);
v_trees_3376_ = lean_ctor_get(v_s_3373_, 2);
v_isSharedCheck_3383_ = !lean_is_exclusive(v_s_3373_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v_s_3373_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_trees_3376_);
lean_inc(v_lazyAssignment_3375_);
lean_inc(v_assignment_3374_);
lean_dec(v_s_3373_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_assignment_3374_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_lazyAssignment_3375_);
lean_ctor_set(v_reuseFailAlloc_3382_, 2, v_trees_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
lean_ctor_set_uint8(v___x_3381_, sizeof(void*)*3, v_flag_3372_);
return v___x_3381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object* v_flag_3384_, lean_object* v_s_3385_){
_start:
{
uint8_t v_flag_boxed_3386_; lean_object* v_res_3387_; 
v_flag_boxed_3386_ = lean_unbox(v_flag_3384_);
v_res_3387_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_3386_, v_s_3385_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object* v_inst_3388_, uint8_t v_flag_3389_){
_start:
{
lean_object* v_modifyInfoState_3390_; lean_object* v___x_3391_; lean_object* v___f_3392_; lean_object* v___x_3393_; 
v_modifyInfoState_3390_ = lean_ctor_get(v_inst_3388_, 1);
lean_inc(v_modifyInfoState_3390_);
lean_dec_ref(v_inst_3388_);
v___x_3391_ = lean_box(v_flag_3389_);
v___f_3392_ = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3392_, 0, v___x_3391_);
v___x_3393_ = lean_apply_1(v_modifyInfoState_3390_, v___f_3392_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object* v_inst_3394_, lean_object* v_flag_3395_){
_start:
{
uint8_t v_flag_boxed_3396_; lean_object* v_res_3397_; 
v_flag_boxed_3396_ = lean_unbox(v_flag_3395_);
v_res_3397_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3394_, v_flag_boxed_3396_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object* v_m_3398_, lean_object* v_inst_3399_, uint8_t v_flag_3400_){
_start:
{
lean_object* v___x_3401_; 
v___x_3401_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3399_, v_flag_3400_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object* v_m_3402_, lean_object* v_inst_3403_, lean_object* v_flag_3404_){
_start:
{
uint8_t v_flag_boxed_3405_; lean_object* v_res_3406_; 
v_flag_boxed_3405_ = lean_unbox(v_flag_3404_);
v_res_3406_ = l_Lean_Elab_enableInfoTree(v_m_3402_, v_inst_3403_, v_flag_boxed_3405_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object* v_x_3407_){
_start:
{
lean_object* v_fst_3408_; 
v_fst_3408_ = lean_ctor_get(v_x_3407_, 0);
lean_inc(v_fst_3408_);
return v_fst_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object* v_x_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_3409_);
lean_dec_ref(v_x_3409_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object* v_x_3411_, lean_object* v_____r_3412_){
_start:
{
lean_inc(v_x_3411_);
return v_x_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object* v_x_3413_, lean_object* v_____r_3414_){
_start:
{
lean_object* v_res_3415_; 
v_res_3415_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_3413_, v_____r_3414_);
lean_dec(v_x_3413_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object* v___x_3416_, lean_object* v_x_3417_){
_start:
{
lean_inc(v___x_3416_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object* v___x_3418_, lean_object* v_x_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_3418_, v_x_3419_);
lean_dec(v_x_3419_);
lean_dec(v___x_3418_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object* v_toFunctor_3421_, lean_object* v_inst_3422_, uint8_t v_flag_3423_, lean_object* v_toBind_3424_, lean_object* v___f_3425_, lean_object* v_inst_3426_, lean_object* v___f_3427_, lean_object* v_____do__lift_3428_){
_start:
{
uint8_t v_enabled_3429_; lean_object* v_map_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___f_3434_; lean_object* v_y_3435_; lean_object* v___x_3436_; 
v_enabled_3429_ = lean_ctor_get_uint8(v_____do__lift_3428_, sizeof(void*)*3);
v_map_3430_ = lean_ctor_get(v_toFunctor_3421_, 0);
lean_inc(v_map_3430_);
lean_dec_ref(v_toFunctor_3421_);
lean_inc_ref(v_inst_3422_);
v___x_3431_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3422_, v_flag_3423_);
v___x_3432_ = lean_apply_4(v_toBind_3424_, lean_box(0), lean_box(0), v___x_3431_, v___f_3425_);
v___x_3433_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3422_, v_enabled_3429_);
v___f_3434_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_3434_, 0, v___x_3433_);
v_y_3435_ = lean_apply_4(v_inst_3426_, lean_box(0), lean_box(0), v___x_3432_, v___f_3434_);
v___x_3436_ = lean_apply_4(v_map_3430_, lean_box(0), lean_box(0), v___f_3427_, v_y_3435_);
return v___x_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object* v_toFunctor_3437_, lean_object* v_inst_3438_, lean_object* v_flag_3439_, lean_object* v_toBind_3440_, lean_object* v___f_3441_, lean_object* v_inst_3442_, lean_object* v___f_3443_, lean_object* v_____do__lift_3444_){
_start:
{
uint8_t v_flag_boxed_3445_; lean_object* v_res_3446_; 
v_flag_boxed_3445_ = lean_unbox(v_flag_3439_);
v_res_3446_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_3437_, v_inst_3438_, v_flag_boxed_3445_, v_toBind_3440_, v___f_3441_, v_inst_3442_, v___f_3443_, v_____do__lift_3444_);
lean_dec_ref(v_____do__lift_3444_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object* v_inst_3448_, lean_object* v_inst_3449_, lean_object* v_inst_3450_, uint8_t v_flag_3451_, lean_object* v_x_3452_){
_start:
{
lean_object* v_toApplicative_3453_; lean_object* v_toBind_3454_; lean_object* v_getInfoState_3455_; lean_object* v_toFunctor_3456_; lean_object* v___f_3457_; lean_object* v___f_3458_; lean_object* v___x_3459_; lean_object* v___f_3460_; lean_object* v___x_3461_; 
v_toApplicative_3453_ = lean_ctor_get(v_inst_3448_, 0);
lean_inc_ref(v_toApplicative_3453_);
v_toBind_3454_ = lean_ctor_get(v_inst_3448_, 1);
lean_inc_n(v_toBind_3454_, 2);
lean_dec_ref(v_inst_3448_);
v_getInfoState_3455_ = lean_ctor_get(v_inst_3449_, 0);
lean_inc(v_getInfoState_3455_);
v_toFunctor_3456_ = lean_ctor_get(v_toApplicative_3453_, 0);
lean_inc_ref(v_toFunctor_3456_);
lean_dec_ref(v_toApplicative_3453_);
v___f_3457_ = ((lean_object*)(l_Lean_Elab_withEnableInfoTree___redArg___closed__0));
v___f_3458_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3458_, 0, v_x_3452_);
v___x_3459_ = lean_box(v_flag_3451_);
v___f_3460_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_3460_, 0, v_toFunctor_3456_);
lean_closure_set(v___f_3460_, 1, v_inst_3449_);
lean_closure_set(v___f_3460_, 2, v___x_3459_);
lean_closure_set(v___f_3460_, 3, v_toBind_3454_);
lean_closure_set(v___f_3460_, 4, v___f_3458_);
lean_closure_set(v___f_3460_, 5, v_inst_3450_);
lean_closure_set(v___f_3460_, 6, v___f_3457_);
v___x_3461_ = lean_apply_4(v_toBind_3454_, lean_box(0), lean_box(0), v_getInfoState_3455_, v___f_3460_);
return v___x_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object* v_inst_3462_, lean_object* v_inst_3463_, lean_object* v_inst_3464_, lean_object* v_flag_3465_, lean_object* v_x_3466_){
_start:
{
uint8_t v_flag_boxed_3467_; lean_object* v_res_3468_; 
v_flag_boxed_3467_ = lean_unbox(v_flag_3465_);
v_res_3468_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3462_, v_inst_3463_, v_inst_3464_, v_flag_boxed_3467_, v_x_3466_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object* v_m_3469_, lean_object* v_00_u03b1_3470_, lean_object* v_inst_3471_, lean_object* v_inst_3472_, lean_object* v_inst_3473_, uint8_t v_flag_3474_, lean_object* v_x_3475_){
_start:
{
lean_object* v___x_3476_; 
v___x_3476_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3471_, v_inst_3472_, v_inst_3473_, v_flag_3474_, v_x_3475_);
return v___x_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object* v_m_3477_, lean_object* v_00_u03b1_3478_, lean_object* v_inst_3479_, lean_object* v_inst_3480_, lean_object* v_inst_3481_, lean_object* v_flag_3482_, lean_object* v_x_3483_){
_start:
{
uint8_t v_flag_boxed_3484_; lean_object* v_res_3485_; 
v_flag_boxed_3484_ = lean_unbox(v_flag_3482_);
v_res_3485_ = l_Lean_Elab_withEnableInfoTree(v_m_3477_, v_00_u03b1_3478_, v_inst_3479_, v_inst_3480_, v_inst_3481_, v_flag_boxed_3484_, v_x_3483_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object* v_toPure_3486_, lean_object* v_____do__lift_3487_){
_start:
{
lean_object* v_trees_3488_; lean_object* v___x_3489_; 
v_trees_3488_ = lean_ctor_get(v_____do__lift_3487_, 2);
lean_inc_ref(v_trees_3488_);
lean_dec_ref(v_____do__lift_3487_);
v___x_3489_ = lean_apply_2(v_toPure_3486_, lean_box(0), v_trees_3488_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object* v_inst_3490_, lean_object* v_inst_3491_){
_start:
{
lean_object* v_toApplicative_3492_; lean_object* v_toBind_3493_; lean_object* v_getInfoState_3494_; lean_object* v_toPure_3495_; lean_object* v___f_3496_; lean_object* v___x_3497_; 
v_toApplicative_3492_ = lean_ctor_get(v_inst_3491_, 0);
lean_inc_ref(v_toApplicative_3492_);
v_toBind_3493_ = lean_ctor_get(v_inst_3491_, 1);
lean_inc(v_toBind_3493_);
lean_dec_ref(v_inst_3491_);
v_getInfoState_3494_ = lean_ctor_get(v_inst_3490_, 0);
lean_inc(v_getInfoState_3494_);
lean_dec_ref(v_inst_3490_);
v_toPure_3495_ = lean_ctor_get(v_toApplicative_3492_, 1);
lean_inc(v_toPure_3495_);
lean_dec_ref(v_toApplicative_3492_);
v___f_3496_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3496_, 0, v_toPure_3495_);
v___x_3497_ = lean_apply_4(v_toBind_3493_, lean_box(0), lean_box(0), v_getInfoState_3494_, v___f_3496_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object* v_m_3498_, lean_object* v_inst_3499_, lean_object* v_inst_3500_){
_start:
{
lean_object* v___x_3501_; 
v___x_3501_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_3499_, v_inst_3500_);
return v___x_3501_;
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
