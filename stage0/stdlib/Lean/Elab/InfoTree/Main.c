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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
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
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "<InfoTree>"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15;
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
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_unsigned_to_nat(32u);
v___x_181_ = lean_mk_empty_array_with_capacity(v___x_180_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1(void){
_start:
{
size_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_183_ = ((size_t)5ULL);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_unsigned_to_nat(32u);
v___x_186_ = lean_mk_empty_array_with_capacity(v___x_185_);
v___x_187_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0);
v___x_188_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
lean_ctor_set(v___x_188_, 2, v___x_184_);
lean_ctor_set(v___x_188_, 3, v___x_184_);
lean_ctor_set_usize(v___x_188_, 4, v___x_183_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2(void){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_189_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2);
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = l_Lean_NameSet_empty;
v___x_195_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
lean_ctor_set(v___x_196_, 2, v___x_194_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = lean_unsigned_to_nat(1u);
v___x_198_ = l_Lean_firstFrontendMacroScope;
v___x_199_ = lean_nat_add(v___x_198_, v___x_197_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8(void){
_start:
{
lean_object* v___x_204_; uint64_t v___x_205_; lean_object* v___x_206_; 
v___x_204_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_205_ = 0ULL;
v___x_206_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set_uint64(v___x_206_, sizeof(void*)*1, v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; 
v___x_207_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_208_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3);
v___x_209_ = 1;
v___x_210_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_208_);
lean_ctor_set(v___x_210_, 2, v___x_207_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*3, v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = l_Lean_Options_empty;
v___x_218_ = l_Lean_Core_getMaxHeartbeats(v___x_217_);
return v___x_218_;
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
lean_object* v_a_229_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_toCommandContextInfo_236_; lean_object* v_env_237_; lean_object* v_options_238_; lean_object* v_currNamespace_239_; lean_object* v_openDecls_240_; lean_object* v_ngen_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; lean_object* v_env_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___y_255_; uint8_t v___y_256_; lean_object* v_fileName_257_; lean_object* v_fileMap_258_; lean_object* v_currNamespace_259_; lean_object* v_openDecls_260_; lean_object* v_initHeartbeats_261_; lean_object* v_maxHeartbeats_262_; lean_object* v_quotContext_263_; lean_object* v_currMacroScope_264_; lean_object* v_cancelTk_x3f_265_; lean_object* v_inheritedTraceOptions_266_; lean_object* v_currRecDepth_267_; lean_object* v_ref_268_; uint8_t v_suppressElabErrors_269_; lean_object* v___y_270_; lean_object* v___y_307_; uint8_t v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_326_; lean_object* v___y_327_; uint8_t v___y_328_; lean_object* v___y_329_; uint8_t v___y_330_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v_env_362_; lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v___y_366_; lean_object* v___y_367_; uint8_t v___y_405_; uint8_t v___x_425_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4);
v___x_234_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5);
v___x_235_ = lean_io_get_num_heartbeats();
v_toCommandContextInfo_236_ = lean_ctor_get(v_info_225_, 0);
lean_inc_ref(v_toCommandContextInfo_236_);
lean_dec_ref(v_info_225_);
v_env_237_ = lean_ctor_get(v_toCommandContextInfo_236_, 0);
lean_inc_ref(v_env_237_);
v_options_238_ = lean_ctor_get(v_toCommandContextInfo_236_, 4);
lean_inc_ref(v_options_238_);
v_currNamespace_239_ = lean_ctor_get(v_toCommandContextInfo_236_, 5);
lean_inc(v_currNamespace_239_);
v_openDecls_240_ = lean_ctor_get(v_toCommandContextInfo_236_, 6);
lean_inc(v_openDecls_240_);
v_ngen_241_ = lean_ctor_get(v_toCommandContextInfo_236_, 7);
lean_inc_ref(v_ngen_241_);
lean_dec_ref(v_toCommandContextInfo_236_);
v___x_242_ = l_Lean_firstFrontendMacroScope;
v___x_243_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6);
v___x_244_ = 0;
v_env_245_ = l_Lean_Environment_setExporting(v_env_237_, v___x_244_);
v___x_246_ = lean_box(0);
v___x_247_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7));
v___x_248_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_249_ = 1;
v___x_250_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9);
v___x_251_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10));
v___x_252_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_252_, 0, v_env_245_);
lean_ctor_set(v___x_252_, 1, v___x_243_);
lean_ctor_set(v___x_252_, 2, v_ngen_241_);
lean_ctor_set(v___x_252_, 3, v___x_247_);
lean_ctor_set(v___x_252_, 4, v___x_248_);
lean_ctor_set(v___x_252_, 5, v___x_233_);
lean_ctor_set(v___x_252_, 6, v___x_234_);
lean_ctor_set(v___x_252_, 7, v___x_250_);
lean_ctor_set(v___x_252_, 8, v___x_251_);
v___x_253_ = lean_st_mk_ref(v___x_252_);
v___x_350_ = l_Lean_inheritedTraceOptions;
v___x_351_ = lean_st_ref_get(v___x_350_);
v___x_352_ = lean_st_ref_get(v___x_253_);
v___x_353_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14));
v___x_354_ = l_Lean_instInhabitedFileMap_default;
v___x_355_ = l_Lean_Options_empty;
v___x_356_ = lean_unsigned_to_nat(1000u);
v___x_357_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15);
v___x_358_ = lean_box(0);
v___x_359_ = lean_box(0);
v___x_360_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_360_, 0, v___x_353_);
lean_ctor_set(v___x_360_, 1, v___x_354_);
lean_ctor_set(v___x_360_, 2, v___x_355_);
lean_ctor_set(v___x_360_, 3, v___x_356_);
lean_ctor_set(v___x_360_, 4, v_currNamespace_239_);
lean_ctor_set(v___x_360_, 5, v_openDecls_240_);
lean_ctor_set(v___x_360_, 6, v___x_235_);
lean_ctor_set(v___x_360_, 7, v___x_357_);
lean_ctor_set(v___x_360_, 8, v___x_246_);
lean_ctor_set(v___x_360_, 9, v___x_242_);
lean_ctor_set(v___x_360_, 10, v___x_358_);
lean_ctor_set(v___x_360_, 11, v___x_351_);
v___x_361_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v___x_232_);
lean_ctor_set(v___x_361_, 2, v___x_359_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*3, v___x_244_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*3 + 1, v___x_244_);
v_env_362_ = lean_ctor_get(v___x_352_, 0);
lean_inc_ref(v_env_362_);
lean_dec(v___x_352_);
v___x_363_ = l_Lean_diagnostics;
v___x_364_ = lean_uint8_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16);
v___x_425_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_362_);
lean_dec_ref(v_env_362_);
if (v___x_364_ == 0)
{
if (v___x_425_ == 0)
{
lean_inc(v___x_253_);
v___y_366_ = v___x_361_;
v___y_367_ = v___x_253_;
goto v___jp_365_;
}
else
{
v___y_405_ = v___x_364_;
goto v___jp_404_;
}
}
else
{
v___y_405_ = v___x_425_;
goto v___jp_404_;
}
v___jp_228_:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_mk_io_user_error(v_a_229_);
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
v___jp_254_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_271_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v_options_238_, v___y_255_);
v___x_272_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_272_, 0, v_fileName_257_);
lean_ctor_set(v___x_272_, 1, v_fileMap_258_);
lean_ctor_set(v___x_272_, 2, v_options_238_);
lean_ctor_set(v___x_272_, 3, v___x_271_);
lean_ctor_set(v___x_272_, 4, v_currNamespace_259_);
lean_ctor_set(v___x_272_, 5, v_openDecls_260_);
lean_ctor_set(v___x_272_, 6, v_initHeartbeats_261_);
lean_ctor_set(v___x_272_, 7, v_maxHeartbeats_262_);
lean_ctor_set(v___x_272_, 8, v_quotContext_263_);
lean_ctor_set(v___x_272_, 9, v_currMacroScope_264_);
lean_ctor_set(v___x_272_, 10, v_cancelTk_x3f_265_);
lean_ctor_set(v___x_272_, 11, v_inheritedTraceOptions_266_);
v___x_273_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v_currRecDepth_267_);
lean_ctor_set(v___x_273_, 2, v_ref_268_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*3, v___y_256_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*3 + 1, v_suppressElabErrors_269_);
v___x_274_ = lean_apply_3(v_x_226_, v___x_273_, v___y_270_, lean_box(0));
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
v___x_279_ = lean_st_ref_get(v___x_253_);
lean_dec(v___x_253_);
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
lean_dec(v___x_253_);
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
v___x_297_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11));
v___x_298_ = l_Lean_Name_toString(v_a_296_, v___x_249_);
v___x_299_ = lean_string_append(v___x_297_, v___x_298_);
lean_dec_ref(v___x_298_);
v_a_229_ = v___x_299_;
goto v___jp_228_;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec_ref_known(v___x_295_, 1);
v___x_300_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12));
v___x_301_ = l_Nat_reprFast(v_id_294_);
v___x_302_ = lean_string_append(v___x_300_, v___x_301_);
lean_dec_ref(v___x_301_);
v___x_303_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13));
v___x_304_ = lean_string_append(v___x_302_, v___x_303_);
v_a_229_ = v___x_304_;
goto v___jp_228_;
}
}
}
}
}
v___jp_306_:
{
lean_object* v_toCold_311_; lean_object* v_currRecDepth_312_; lean_object* v_ref_313_; uint8_t v_suppressElabErrors_314_; lean_object* v_fileName_315_; lean_object* v_fileMap_316_; lean_object* v_currNamespace_317_; lean_object* v_openDecls_318_; lean_object* v_initHeartbeats_319_; lean_object* v_maxHeartbeats_320_; lean_object* v_quotContext_321_; lean_object* v_currMacroScope_322_; lean_object* v_cancelTk_x3f_323_; lean_object* v_inheritedTraceOptions_324_; 
v_toCold_311_ = lean_ctor_get(v___y_309_, 0);
lean_inc_ref(v_toCold_311_);
v_currRecDepth_312_ = lean_ctor_get(v___y_309_, 1);
lean_inc(v_currRecDepth_312_);
v_ref_313_ = lean_ctor_get(v___y_309_, 2);
lean_inc(v_ref_313_);
v_suppressElabErrors_314_ = lean_ctor_get_uint8(v___y_309_, sizeof(void*)*3 + 1);
lean_dec_ref(v___y_309_);
v_fileName_315_ = lean_ctor_get(v_toCold_311_, 0);
lean_inc_ref(v_fileName_315_);
v_fileMap_316_ = lean_ctor_get(v_toCold_311_, 1);
lean_inc_ref(v_fileMap_316_);
v_currNamespace_317_ = lean_ctor_get(v_toCold_311_, 4);
lean_inc(v_currNamespace_317_);
v_openDecls_318_ = lean_ctor_get(v_toCold_311_, 5);
lean_inc(v_openDecls_318_);
v_initHeartbeats_319_ = lean_ctor_get(v_toCold_311_, 6);
lean_inc(v_initHeartbeats_319_);
v_maxHeartbeats_320_ = lean_ctor_get(v_toCold_311_, 7);
lean_inc(v_maxHeartbeats_320_);
v_quotContext_321_ = lean_ctor_get(v_toCold_311_, 8);
lean_inc(v_quotContext_321_);
v_currMacroScope_322_ = lean_ctor_get(v_toCold_311_, 9);
lean_inc(v_currMacroScope_322_);
v_cancelTk_x3f_323_ = lean_ctor_get(v_toCold_311_, 10);
lean_inc(v_cancelTk_x3f_323_);
v_inheritedTraceOptions_324_ = lean_ctor_get(v_toCold_311_, 11);
lean_inc_ref(v_inheritedTraceOptions_324_);
lean_dec_ref(v_toCold_311_);
v___y_255_ = v___y_307_;
v___y_256_ = v___y_308_;
v_fileName_257_ = v_fileName_315_;
v_fileMap_258_ = v_fileMap_316_;
v_currNamespace_259_ = v_currNamespace_317_;
v_openDecls_260_ = v_openDecls_318_;
v_initHeartbeats_261_ = v_initHeartbeats_319_;
v_maxHeartbeats_262_ = v_maxHeartbeats_320_;
v_quotContext_263_ = v_quotContext_321_;
v_currMacroScope_264_ = v_currMacroScope_322_;
v_cancelTk_x3f_265_ = v_cancelTk_x3f_323_;
v_inheritedTraceOptions_266_ = v_inheritedTraceOptions_324_;
v_currRecDepth_267_ = v_currRecDepth_312_;
v_ref_268_ = v_ref_313_;
v_suppressElabErrors_269_ = v_suppressElabErrors_314_;
v___y_270_ = v___y_310_;
goto v___jp_254_;
}
v___jp_325_:
{
if (v___y_330_ == 0)
{
lean_object* v___x_331_; lean_object* v_env_332_; lean_object* v_nextMacroScope_333_; lean_object* v_ngen_334_; lean_object* v_auxDeclNGen_335_; lean_object* v_traceState_336_; lean_object* v_messages_337_; lean_object* v_infoState_338_; lean_object* v_snapshotTasks_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_348_; 
v___x_331_ = lean_st_ref_take(v___y_329_);
v_env_332_ = lean_ctor_get(v___x_331_, 0);
v_nextMacroScope_333_ = lean_ctor_get(v___x_331_, 1);
v_ngen_334_ = lean_ctor_get(v___x_331_, 2);
v_auxDeclNGen_335_ = lean_ctor_get(v___x_331_, 3);
v_traceState_336_ = lean_ctor_get(v___x_331_, 4);
v_messages_337_ = lean_ctor_get(v___x_331_, 6);
v_infoState_338_ = lean_ctor_get(v___x_331_, 7);
v_snapshotTasks_339_ = lean_ctor_get(v___x_331_, 8);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_348_ == 0)
{
lean_object* v_unused_349_; 
v_unused_349_ = lean_ctor_get(v___x_331_, 5);
lean_dec(v_unused_349_);
v___x_341_ = v___x_331_;
v_isShared_342_ = v_isSharedCheck_348_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_snapshotTasks_339_);
lean_inc(v_infoState_338_);
lean_inc(v_messages_337_);
lean_inc(v_traceState_336_);
lean_inc(v_auxDeclNGen_335_);
lean_inc(v_ngen_334_);
lean_inc(v_nextMacroScope_333_);
lean_inc(v_env_332_);
lean_dec(v___x_331_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_348_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_343_ = l_Lean_Kernel_enableDiag(v_env_332_, v___y_328_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 5, v___x_233_);
lean_ctor_set(v___x_341_, 0, v___x_343_);
v___x_345_ = v___x_341_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_343_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_nextMacroScope_333_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_ngen_334_);
lean_ctor_set(v_reuseFailAlloc_347_, 3, v_auxDeclNGen_335_);
lean_ctor_set(v_reuseFailAlloc_347_, 4, v_traceState_336_);
lean_ctor_set(v_reuseFailAlloc_347_, 5, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_347_, 6, v_messages_337_);
lean_ctor_set(v_reuseFailAlloc_347_, 7, v_infoState_338_);
lean_ctor_set(v_reuseFailAlloc_347_, 8, v_snapshotTasks_339_);
v___x_345_ = v_reuseFailAlloc_347_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_346_; 
v___x_346_ = lean_st_ref_put(v___y_329_, v___x_345_);
v___y_307_ = v___y_326_;
v___y_308_ = v___y_328_;
v___y_309_ = v___y_327_;
v___y_310_ = v___y_329_;
goto v___jp_306_;
}
}
}
else
{
v___y_307_ = v___y_326_;
v___y_308_ = v___y_328_;
v___y_309_ = v___y_327_;
v___y_310_ = v___y_329_;
goto v___jp_306_;
}
}
v___jp_365_:
{
lean_object* v___x_368_; lean_object* v_toCold_369_; lean_object* v_currRecDepth_370_; lean_object* v_ref_371_; uint8_t v_suppressElabErrors_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_403_; 
v___x_368_ = lean_st_ref_get(v___y_367_);
v_toCold_369_ = lean_ctor_get(v___y_366_, 0);
v_currRecDepth_370_ = lean_ctor_get(v___y_366_, 1);
v_ref_371_ = lean_ctor_get(v___y_366_, 2);
v_suppressElabErrors_372_ = lean_ctor_get_uint8(v___y_366_, sizeof(void*)*3 + 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v___y_366_);
if (v_isSharedCheck_403_ == 0)
{
v___x_374_ = v___y_366_;
v_isShared_375_ = v_isSharedCheck_403_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_ref_371_);
lean_inc(v_currRecDepth_370_);
lean_inc(v_toCold_369_);
lean_dec(v___y_366_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_403_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v_fileName_376_; lean_object* v_fileMap_377_; lean_object* v_currNamespace_378_; lean_object* v_openDecls_379_; lean_object* v_initHeartbeats_380_; lean_object* v_maxHeartbeats_381_; lean_object* v_quotContext_382_; lean_object* v_currMacroScope_383_; lean_object* v_cancelTk_x3f_384_; lean_object* v_inheritedTraceOptions_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_400_; 
v_fileName_376_ = lean_ctor_get(v_toCold_369_, 0);
v_fileMap_377_ = lean_ctor_get(v_toCold_369_, 1);
v_currNamespace_378_ = lean_ctor_get(v_toCold_369_, 4);
v_openDecls_379_ = lean_ctor_get(v_toCold_369_, 5);
v_initHeartbeats_380_ = lean_ctor_get(v_toCold_369_, 6);
v_maxHeartbeats_381_ = lean_ctor_get(v_toCold_369_, 7);
v_quotContext_382_ = lean_ctor_get(v_toCold_369_, 8);
v_currMacroScope_383_ = lean_ctor_get(v_toCold_369_, 9);
v_cancelTk_x3f_384_ = lean_ctor_get(v_toCold_369_, 10);
v_inheritedTraceOptions_385_ = lean_ctor_get(v_toCold_369_, 11);
v_isSharedCheck_400_ = !lean_is_exclusive(v_toCold_369_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; lean_object* v_unused_402_; 
v_unused_401_ = lean_ctor_get(v_toCold_369_, 3);
lean_dec(v_unused_401_);
v_unused_402_ = lean_ctor_get(v_toCold_369_, 2);
lean_dec(v_unused_402_);
v___x_387_ = v_toCold_369_;
v_isShared_388_ = v_isSharedCheck_400_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_inheritedTraceOptions_385_);
lean_inc(v_cancelTk_x3f_384_);
lean_inc(v_currMacroScope_383_);
lean_inc(v_quotContext_382_);
lean_inc(v_maxHeartbeats_381_);
lean_inc(v_initHeartbeats_380_);
lean_inc(v_openDecls_379_);
lean_inc(v_currNamespace_378_);
lean_inc(v_fileMap_377_);
lean_inc(v_fileName_376_);
lean_dec(v_toCold_369_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_400_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v_env_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v_env_389_ = lean_ctor_get(v___x_368_, 0);
lean_inc_ref(v_env_389_);
lean_dec(v___x_368_);
v___x_390_ = l_Lean_maxRecDepth;
v___x_391_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17);
lean_inc_ref(v_inheritedTraceOptions_385_);
lean_inc(v_cancelTk_x3f_384_);
lean_inc(v_currMacroScope_383_);
lean_inc(v_quotContext_382_);
lean_inc(v_maxHeartbeats_381_);
lean_inc(v_initHeartbeats_380_);
lean_inc(v_openDecls_379_);
lean_inc(v_currNamespace_378_);
lean_inc_ref(v_fileMap_377_);
lean_inc_ref(v_fileName_376_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 3, v___x_391_);
lean_ctor_set(v___x_387_, 2, v___x_355_);
v___x_393_ = v___x_387_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_fileName_376_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_fileMap_377_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_399_, 3, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_399_, 4, v_currNamespace_378_);
lean_ctor_set(v_reuseFailAlloc_399_, 5, v_openDecls_379_);
lean_ctor_set(v_reuseFailAlloc_399_, 6, v_initHeartbeats_380_);
lean_ctor_set(v_reuseFailAlloc_399_, 7, v_maxHeartbeats_381_);
lean_ctor_set(v_reuseFailAlloc_399_, 8, v_quotContext_382_);
lean_ctor_set(v_reuseFailAlloc_399_, 9, v_currMacroScope_383_);
lean_ctor_set(v_reuseFailAlloc_399_, 10, v_cancelTk_x3f_384_);
lean_ctor_set(v_reuseFailAlloc_399_, 11, v_inheritedTraceOptions_385_);
v___x_393_ = v_reuseFailAlloc_399_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_395_; 
lean_inc(v_ref_371_);
lean_inc(v_currRecDepth_370_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_393_);
v___x_395_ = v___x_374_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_currRecDepth_370_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_ref_371_);
lean_ctor_set_uint8(v_reuseFailAlloc_398_, sizeof(void*)*3 + 1, v_suppressElabErrors_372_);
v___x_395_ = v_reuseFailAlloc_398_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
uint8_t v___x_396_; uint8_t v___x_397_; 
lean_ctor_set_uint8(v___x_395_, sizeof(void*)*3, v___x_364_);
v___x_396_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v_options_238_, v___x_363_);
v___x_397_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_389_);
lean_dec_ref(v_env_389_);
if (v___x_396_ == 0)
{
if (v___x_397_ == 0)
{
lean_dec_ref(v___x_395_);
v___y_255_ = v___x_390_;
v___y_256_ = v___x_396_;
v_fileName_257_ = v_fileName_376_;
v_fileMap_258_ = v_fileMap_377_;
v_currNamespace_259_ = v_currNamespace_378_;
v_openDecls_260_ = v_openDecls_379_;
v_initHeartbeats_261_ = v_initHeartbeats_380_;
v_maxHeartbeats_262_ = v_maxHeartbeats_381_;
v_quotContext_263_ = v_quotContext_382_;
v_currMacroScope_264_ = v_currMacroScope_383_;
v_cancelTk_x3f_265_ = v_cancelTk_x3f_384_;
v_inheritedTraceOptions_266_ = v_inheritedTraceOptions_385_;
v_currRecDepth_267_ = v_currRecDepth_370_;
v_ref_268_ = v_ref_371_;
v_suppressElabErrors_269_ = v_suppressElabErrors_372_;
v___y_270_ = v___y_367_;
goto v___jp_254_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_385_);
lean_dec(v_cancelTk_x3f_384_);
lean_dec(v_currMacroScope_383_);
lean_dec(v_quotContext_382_);
lean_dec(v_maxHeartbeats_381_);
lean_dec(v_initHeartbeats_380_);
lean_dec(v_openDecls_379_);
lean_dec(v_currNamespace_378_);
lean_dec_ref(v_fileMap_377_);
lean_dec_ref(v_fileName_376_);
lean_dec(v_ref_371_);
lean_dec(v_currRecDepth_370_);
v___y_326_ = v___x_390_;
v___y_327_ = v___x_395_;
v___y_328_ = v___x_396_;
v___y_329_ = v___y_367_;
v___y_330_ = v___x_396_;
goto v___jp_325_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_385_);
lean_dec(v_cancelTk_x3f_384_);
lean_dec(v_currMacroScope_383_);
lean_dec(v_quotContext_382_);
lean_dec(v_maxHeartbeats_381_);
lean_dec(v_initHeartbeats_380_);
lean_dec(v_openDecls_379_);
lean_dec(v_currNamespace_378_);
lean_dec_ref(v_fileMap_377_);
lean_dec_ref(v_fileName_376_);
lean_dec(v_ref_371_);
lean_dec(v_currRecDepth_370_);
v___y_326_ = v___x_390_;
v___y_327_ = v___x_395_;
v___y_328_ = v___x_396_;
v___y_329_ = v___y_367_;
v___y_330_ = v___x_397_;
goto v___jp_325_;
}
}
}
}
}
}
v___jp_404_:
{
if (v___y_405_ == 0)
{
lean_object* v___x_406_; lean_object* v_env_407_; lean_object* v_nextMacroScope_408_; lean_object* v_ngen_409_; lean_object* v_auxDeclNGen_410_; lean_object* v_traceState_411_; lean_object* v_messages_412_; lean_object* v_infoState_413_; lean_object* v_snapshotTasks_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_423_; 
v___x_406_ = lean_st_ref_take(v___x_253_);
v_env_407_ = lean_ctor_get(v___x_406_, 0);
v_nextMacroScope_408_ = lean_ctor_get(v___x_406_, 1);
v_ngen_409_ = lean_ctor_get(v___x_406_, 2);
v_auxDeclNGen_410_ = lean_ctor_get(v___x_406_, 3);
v_traceState_411_ = lean_ctor_get(v___x_406_, 4);
v_messages_412_ = lean_ctor_get(v___x_406_, 6);
v_infoState_413_ = lean_ctor_get(v___x_406_, 7);
v_snapshotTasks_414_ = lean_ctor_get(v___x_406_, 8);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v___x_406_, 5);
lean_dec(v_unused_424_);
v___x_416_ = v___x_406_;
v_isShared_417_ = v_isSharedCheck_423_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_snapshotTasks_414_);
lean_inc(v_infoState_413_);
lean_inc(v_messages_412_);
lean_inc(v_traceState_411_);
lean_inc(v_auxDeclNGen_410_);
lean_inc(v_ngen_409_);
lean_inc(v_nextMacroScope_408_);
lean_inc(v_env_407_);
lean_dec(v___x_406_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_423_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_418_ = l_Lean_Kernel_enableDiag(v_env_407_, v___x_364_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 5, v___x_233_);
lean_ctor_set(v___x_416_, 0, v___x_418_);
v___x_420_ = v___x_416_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_nextMacroScope_408_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v_ngen_409_);
lean_ctor_set(v_reuseFailAlloc_422_, 3, v_auxDeclNGen_410_);
lean_ctor_set(v_reuseFailAlloc_422_, 4, v_traceState_411_);
lean_ctor_set(v_reuseFailAlloc_422_, 5, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_422_, 6, v_messages_412_);
lean_ctor_set(v_reuseFailAlloc_422_, 7, v_infoState_413_);
lean_ctor_set(v_reuseFailAlloc_422_, 8, v_snapshotTasks_414_);
v___x_420_ = v_reuseFailAlloc_422_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v___x_421_; 
v___x_421_ = lean_st_ref_put(v___x_253_, v___x_420_);
lean_inc(v___x_253_);
v___y_366_ = v___x_361_;
v___y_367_ = v___x_253_;
goto v___jp_365_;
}
}
}
else
{
lean_inc(v___x_253_);
v___y_366_ = v___x_361_;
v___y_367_ = v___x_253_;
goto v___jp_365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___boxed(lean_object* v_info_426_, lean_object* v_x_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_426_, v_x_427_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM(lean_object* v_00_u03b1_430_, lean_object* v_info_431_, lean_object* v_x_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_431_, v_x_432_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___boxed(lean_object* v_00_u03b1_435_, lean_object* v_info_436_, lean_object* v_x_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Elab_ContextInfo_runCoreM(v_00_u03b1_435_, v_info_436_, v_x_437_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(lean_object* v___x_440_, lean_object* v_x_441_, lean_object* v___x_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_st_mk_ref(v___x_440_);
lean_inc(v___x_446_);
v___x_447_ = lean_apply_5(v_x_441_, v___x_442_, v___x_446_, v___y_443_, v___y_444_, lean_box(0));
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_457_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_457_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_457_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_457_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_452_ = lean_st_ref_get(v___x_446_);
lean_dec(v___x_446_);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v_a_448_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_453_);
v___x_455_ = v___x_450_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_dec(v___x_446_);
v_a_458_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_447_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_447_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed(lean_object* v___x_466_, lean_object* v_x_467_, lean_object* v___x_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(v___x_466_, v_x_467_, v___x_468_, v___y_469_, v___y_470_);
return v_res_472_;
}
}
static uint64_t _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1(void){
_start:
{
lean_object* v___x_479_; uint64_t v___x_480_; 
v___x_479_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_480_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2(void){
_start:
{
uint64_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = lean_uint64_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1);
v___x_482_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_483_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set_uint64(v___x_483_, sizeof(void*)*1, v___x_481_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4(void){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_486_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_490_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
lean_ctor_set(v___x_490_, 2, v___x_489_);
lean_ctor_set(v___x_490_, 3, v___x_489_);
lean_ctor_set(v___x_490_, 4, v___x_489_);
lean_ctor_set(v___x_490_, 5, v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_unsigned_to_nat(32u);
v___x_492_ = lean_mk_empty_array_with_capacity(v___x_491_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8(void){
_start:
{
size_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_494_ = ((size_t)5ULL);
v___x_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = lean_unsigned_to_nat(32u);
v___x_497_ = lean_mk_empty_array_with_capacity(v___x_496_);
v___x_498_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7);
v___x_499_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___x_497_);
lean_ctor_set(v___x_499_, 2, v___x_495_);
lean_ctor_set(v___x_499_, 3, v___x_495_);
lean_ctor_set_usize(v___x_499_, 4, v___x_494_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
lean_ctor_set(v___x_501_, 2, v___x_500_);
lean_ctor_set(v___x_501_, 3, v___x_500_);
lean_ctor_set(v___x_501_, 4, v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object* v_info_502_, lean_object* v_lctx_503_, lean_object* v_x_504_){
_start:
{
lean_object* v___x_506_; uint8_t v___x_507_; uint8_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v_toCommandContextInfo_514_; lean_object* v_mctx_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___f_520_; lean_object* v___x_521_; 
v___x_506_ = lean_box(1);
v___x_507_ = 0;
v___x_508_ = 1;
v___x_509_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2);
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3));
v___x_512_ = lean_box(0);
v___x_513_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_513_, 0, v___x_509_);
lean_ctor_set(v___x_513_, 1, v___x_506_);
lean_ctor_set(v___x_513_, 2, v_lctx_503_);
lean_ctor_set(v___x_513_, 3, v___x_511_);
lean_ctor_set(v___x_513_, 4, v___x_512_);
lean_ctor_set(v___x_513_, 5, v___x_510_);
lean_ctor_set(v___x_513_, 6, v___x_512_);
lean_ctor_set_uint8(v___x_513_, sizeof(void*)*7, v___x_507_);
lean_ctor_set_uint8(v___x_513_, sizeof(void*)*7 + 1, v___x_507_);
lean_ctor_set_uint8(v___x_513_, sizeof(void*)*7 + 2, v___x_507_);
lean_ctor_set_uint8(v___x_513_, sizeof(void*)*7 + 3, v___x_508_);
v_toCommandContextInfo_514_ = lean_ctor_get(v_info_502_, 0);
v_mctx_515_ = lean_ctor_get(v_toCommandContextInfo_514_, 3);
v___x_516_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6);
v___x_517_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8);
v___x_518_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9);
lean_inc_ref(v_mctx_515_);
v___x_519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_519_, 0, v_mctx_515_);
lean_ctor_set(v___x_519_, 1, v___x_516_);
lean_ctor_set(v___x_519_, 2, v___x_506_);
lean_ctor_set(v___x_519_, 3, v___x_517_);
lean_ctor_set(v___x_519_, 4, v___x_518_);
v___f_520_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_520_, 0, v___x_519_);
lean_closure_set(v___f_520_, 1, v_x_504_);
lean_closure_set(v___f_520_, 2, v___x_513_);
v___x_521_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_502_, v___f_520_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_530_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_530_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_fst_526_; lean_object* v___x_528_; 
v_fst_526_ = lean_ctor_get(v_a_522_, 0);
lean_inc(v_fst_526_);
lean_dec(v_a_522_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v_fst_526_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_fst_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
v_a_531_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_521_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_521_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object* v_info_539_, lean_object* v_lctx_540_, lean_object* v_x_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_539_, v_lctx_540_, v_x_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object* v_00_u03b1_544_, lean_object* v_info_545_, lean_object* v_lctx_546_, lean_object* v_x_547_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_545_, v_lctx_546_, v_x_547_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object* v_00_u03b1_550_, lean_object* v_info_551_, lean_object* v_lctx_552_, lean_object* v_x_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_Elab_ContextInfo_runMetaM(v_00_u03b1_550_, v_info_551_, v_lctx_552_, v_x_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object* v_info_556_, lean_object* v_lctx_557_){
_start:
{
lean_object* v_toCommandContextInfo_558_; lean_object* v_env_559_; lean_object* v_mctx_560_; lean_object* v_options_561_; lean_object* v_currNamespace_562_; lean_object* v_openDecls_563_; lean_object* v___x_564_; 
v_toCommandContextInfo_558_ = lean_ctor_get(v_info_556_, 0);
v_env_559_ = lean_ctor_get(v_toCommandContextInfo_558_, 0);
v_mctx_560_ = lean_ctor_get(v_toCommandContextInfo_558_, 3);
v_options_561_ = lean_ctor_get(v_toCommandContextInfo_558_, 4);
v_currNamespace_562_ = lean_ctor_get(v_toCommandContextInfo_558_, 5);
v_openDecls_563_ = lean_ctor_get(v_toCommandContextInfo_558_, 6);
lean_inc(v_openDecls_563_);
lean_inc(v_currNamespace_562_);
lean_inc_ref(v_options_561_);
lean_inc_ref(v_mctx_560_);
lean_inc_ref(v_env_559_);
v___x_564_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_564_, 0, v_env_559_);
lean_ctor_set(v___x_564_, 1, v_mctx_560_);
lean_ctor_set(v___x_564_, 2, v_lctx_557_);
lean_ctor_set(v___x_564_, 3, v_options_561_);
lean_ctor_set(v___x_564_, 4, v_currNamespace_562_);
lean_ctor_set(v___x_564_, 5, v_openDecls_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object* v_info_565_, lean_object* v_lctx_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_565_, v_lctx_566_);
lean_dec_ref(v_info_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object* v_info_568_, lean_object* v_lctx_569_, lean_object* v_stx_570_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_568_, v_lctx_569_);
v___x_573_ = l_Lean_ppTerm(v___x_572_, v_stx_570_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object* v_info_575_, lean_object* v_lctx_576_, lean_object* v_stx_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Elab_ContextInfo_ppSyntax(v_info_575_, v_lctx_576_, v_stx_577_);
lean_dec_ref(v_info_575_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(lean_object* v_ctx_595_, lean_object* v_pos_596_, lean_object* v_info_597_){
_start:
{
lean_object* v_toCommandContextInfo_598_; lean_object* v_fileMap_599_; lean_object* v___x_600_; lean_object* v_line_601_; lean_object* v_column_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_625_; 
v_toCommandContextInfo_598_ = lean_ctor_get(v_ctx_595_, 0);
lean_inc_ref(v_toCommandContextInfo_598_);
lean_dec_ref(v_ctx_595_);
v_fileMap_599_ = lean_ctor_get(v_toCommandContextInfo_598_, 2);
lean_inc_ref(v_fileMap_599_);
lean_dec_ref(v_toCommandContextInfo_598_);
v___x_600_ = l_Lean_FileMap_toPosition(v_fileMap_599_, v_pos_596_);
v_line_601_ = lean_ctor_get(v___x_600_, 0);
v_column_602_ = lean_ctor_get(v___x_600_, 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_625_ == 0)
{
v___x_604_ = v___x_600_;
v_isShared_605_ = v_isSharedCheck_625_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_column_602_);
lean_inc(v_line_601_);
lean_dec(v___x_600_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_625_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_606_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_607_ = l_Nat_reprFast(v_line_601_);
v___x_608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
if (v_isShared_605_ == 0)
{
lean_ctor_set_tag(v___x_604_, 5);
lean_ctor_set(v___x_604_, 1, v___x_608_);
lean_ctor_set(v___x_604_, 0, v___x_606_);
v___x_610_ = v___x_604_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v___x_608_);
v___x_610_ = v_reuseFailAlloc_624_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v_pos_617_; 
v___x_611_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
v___x_612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = l_Nat_reprFast(v_column_602_);
v___x_614_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
v___x_615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_612_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v_pos_617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_pos_617_, 0, v___x_615_);
lean_ctor_set(v_pos_617_, 1, v___x_616_);
switch(lean_obj_tag(v_info_597_))
{
case 0:
{
return v_pos_617_;
}
case 1:
{
uint8_t v_canonical_621_; 
v_canonical_621_ = lean_ctor_get_uint8(v_info_597_, sizeof(void*)*2);
if (v_canonical_621_ == 1)
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9));
v___x_623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_623_, 0, v_pos_617_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
return v___x_623_;
}
else
{
goto v___jp_618_;
}
}
default: 
{
goto v___jp_618_;
}
}
v___jp_618_:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7));
v___x_620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_620_, 0, v_pos_617_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
return v___x_620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(lean_object* v_ctx_626_, lean_object* v_pos_627_, lean_object* v_info_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_626_, v_pos_627_, v_info_628_);
lean_dec(v_info_628_);
lean_dec(v_pos_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(lean_object* v_ctx_633_, lean_object* v_stx_634_){
_start:
{
lean_object* v___y_636_; lean_object* v___y_637_; uint8_t v___x_645_; lean_object* v___y_647_; lean_object* v___x_650_; 
v___x_645_ = 0;
v___x_650_ = l_Lean_Syntax_getPos_x3f(v_stx_634_, v___x_645_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v___x_651_; 
v___x_651_ = lean_unsigned_to_nat(0u);
v___y_647_ = v___x_651_;
goto v___jp_646_;
}
else
{
lean_object* v_val_652_; 
v_val_652_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_val_652_);
lean_dec_ref_known(v___x_650_, 1);
v___y_647_ = v_val_652_;
goto v___jp_646_;
}
v___jp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_638_ = l_Lean_Syntax_getHeadInfo(v_stx_634_);
lean_inc_ref(v_ctx_633_);
v___x_639_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_633_, v___y_636_, v___x_638_);
lean_dec(v___x_638_);
lean_dec(v___y_636_);
v___x_640_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = l_Lean_Syntax_getTailInfo(v_stx_634_);
v___x_643_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_633_, v___y_637_, v___x_642_);
lean_dec(v___x_642_);
lean_dec(v___y_637_);
v___x_644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_641_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
return v___x_644_;
}
v___jp_646_:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Syntax_getTailPos_x3f(v_stx_634_, v___x_645_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_inc(v___y_647_);
v___y_636_ = v___y_647_;
v___y_637_ = v___y_647_;
goto v___jp_635_;
}
else
{
lean_object* v_val_649_; 
v_val_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_val_649_);
lean_dec_ref_known(v___x_648_, 1);
v___y_636_ = v___y_647_;
v___y_637_ = v_val_649_;
goto v___jp_635_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(lean_object* v_ctx_653_, lean_object* v_stx_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_653_, v_stx_654_);
lean_dec(v_stx_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(lean_object* v_ctx_659_, lean_object* v_info_660_){
_start:
{
lean_object* v_elaborator_661_; lean_object* v_stx_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_677_; 
v_elaborator_661_ = lean_ctor_get(v_info_660_, 0);
v_stx_662_ = lean_ctor_get(v_info_660_, 1);
v_isSharedCheck_677_ = !lean_is_exclusive(v_info_660_);
if (v_isSharedCheck_677_ == 0)
{
v___x_664_ = v_info_660_;
v_isShared_665_ = v_isSharedCheck_677_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_stx_662_);
lean_inc(v_elaborator_661_);
lean_dec(v_info_660_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_677_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
uint8_t v___x_666_; 
v___x_666_ = l_Lean_Name_isAnonymous(v_elaborator_661_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_667_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_659_, v_stx_662_);
lean_dec(v_stx_662_);
v___x_668_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
if (v_isShared_665_ == 0)
{
lean_ctor_set_tag(v___x_664_, 5);
lean_ctor_set(v___x_664_, 1, v___x_668_);
lean_ctor_set(v___x_664_, 0, v___x_667_);
v___x_670_ = v___x_664_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v___x_668_);
v___x_670_ = v_reuseFailAlloc_675_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
uint8_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_671_ = 1;
v___x_672_ = l_Lean_Name_toString(v_elaborator_661_, v___x_671_);
v___x_673_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
v___x_674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_670_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
return v___x_674_;
}
}
else
{
lean_object* v___x_676_; 
lean_del_object(v___x_664_);
lean_dec(v_elaborator_661_);
v___x_676_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_659_, v_stx_662_);
lean_dec(v_stx_662_);
return v___x_676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object* v_info_678_, lean_object* v_ctx_679_, lean_object* v_x_680_){
_start:
{
lean_object* v_lctx_682_; lean_object* v___x_683_; 
v_lctx_682_ = lean_ctor_get(v_info_678_, 1);
lean_inc_ref(v_lctx_682_);
lean_dec_ref(v_info_678_);
v___x_683_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_679_, v_lctx_682_, v_x_680_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(lean_object* v_info_684_, lean_object* v_ctx_685_, lean_object* v_x_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_684_, v_ctx_685_, v_x_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM(lean_object* v_00_u03b1_689_, lean_object* v_info_690_, lean_object* v_ctx_691_, lean_object* v_x_692_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_690_, v_ctx_691_, v_x_692_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___boxed(lean_object* v_00_u03b1_695_, lean_object* v_info_696_, lean_object* v_ctx_697_, lean_object* v_x_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Elab_TermInfo_runMetaM(v_00_u03b1_695_, v_info_696_, v_ctx_697_, v_x_698_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0(lean_object* v_ctx_715_, lean_object* v_toElabInfo_716_, lean_object* v_expr_717_, uint8_t v_isBinder_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v_a_739_; lean_object* v___y_749_; uint8_t v___y_750_; lean_object* v___y_753_; lean_object* v_a_754_; lean_object* v___x_757_; 
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
lean_inc(v___y_720_);
lean_inc_ref(v___y_719_);
lean_inc_ref(v_expr_717_);
v___x_757_ = lean_infer_type(v_expr_717_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_759_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_757_, 1);
v___x_759_ = l_Lean_Meta_ppExpr(v_a_758_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref_known(v___x_759_, 1);
v_a_739_ = v_a_760_;
goto v___jp_738_;
}
else
{
lean_object* v_a_761_; 
v_a_761_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_761_);
v___y_753_ = v___x_759_;
v_a_754_ = v_a_761_;
goto v___jp_752_;
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
v_a_762_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_757_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_757_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
lean_inc(v_a_762_);
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
v___y_753_ = v___x_767_;
v_a_754_ = v_a_762_;
goto v___jp_752_;
}
}
}
v___jp_724_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
lean_inc_ref(v___y_727_);
v___x_728_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_728_, 0, v___y_727_);
v___x_729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_729_, 0, v___y_726_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v___y_725_);
v___x_733_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_715_, v_toElabInfo_716_);
v___x_736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
v___jp_738_:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Meta_ppExpr(v_expr_717_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 1);
v___x_742_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__3));
v___x_743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v_a_741_);
v___x_744_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
v___x_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
if (v_isBinder_718_ == 0)
{
lean_object* v___x_746_; 
v___x_746_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__6));
v___y_725_ = v_a_739_;
v___y_726_ = v___x_745_;
v___y_727_ = v___x_746_;
goto v___jp_724_;
}
else
{
lean_object* v___x_747_; 
v___x_747_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__7));
v___y_725_ = v_a_739_;
v___y_726_ = v___x_745_;
v___y_727_ = v___x_747_;
goto v___jp_724_;
}
}
else
{
lean_dec(v_a_739_);
lean_dec_ref(v_toElabInfo_716_);
lean_dec_ref(v_ctx_715_);
return v___x_740_;
}
}
v___jp_748_:
{
if (v___y_750_ == 0)
{
lean_object* v___x_751_; 
lean_dec_ref(v___y_749_);
v___x_751_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__9));
v_a_739_ = v___x_751_;
goto v___jp_738_;
}
else
{
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec_ref(v_expr_717_);
lean_dec_ref(v_toElabInfo_716_);
lean_dec_ref(v_ctx_715_);
return v___y_749_;
}
}
v___jp_752_:
{
uint8_t v___x_755_; 
v___x_755_ = l_Lean_Exception_isInterrupt(v_a_754_);
if (v___x_755_ == 0)
{
uint8_t v___x_756_; 
v___x_756_ = l_Lean_Exception_isRuntime(v_a_754_);
v___y_749_ = v___y_753_;
v___y_750_ = v___x_756_;
goto v___jp_748_;
}
else
{
lean_dec_ref(v_a_754_);
v___y_749_ = v___y_753_;
v___y_750_ = v___x_755_;
goto v___jp_748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0___boxed(lean_object* v_ctx_770_, lean_object* v_toElabInfo_771_, lean_object* v_expr_772_, lean_object* v_isBinder_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
uint8_t v_isBinder_boxed_779_; lean_object* v_res_780_; 
v_isBinder_boxed_779_ = lean_unbox(v_isBinder_773_);
v_res_780_ = l_Lean_Elab_TermInfo_format___lam__0(v_ctx_770_, v_toElabInfo_771_, v_expr_772_, v_isBinder_boxed_779_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format(lean_object* v_ctx_781_, lean_object* v_info_782_){
_start:
{
lean_object* v_toElabInfo_784_; lean_object* v_expr_785_; uint8_t v_isBinder_786_; lean_object* v___x_787_; lean_object* v___f_788_; lean_object* v___x_789_; 
v_toElabInfo_784_ = lean_ctor_get(v_info_782_, 0);
v_expr_785_ = lean_ctor_get(v_info_782_, 3);
v_isBinder_786_ = lean_ctor_get_uint8(v_info_782_, sizeof(void*)*4);
v___x_787_ = lean_box(v_isBinder_786_);
lean_inc_ref(v_expr_785_);
lean_inc_ref(v_toElabInfo_784_);
lean_inc_ref(v_ctx_781_);
v___f_788_ = lean_alloc_closure((void*)(l_Lean_Elab_TermInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_788_, 0, v_ctx_781_);
lean_closure_set(v___f_788_, 1, v_toElabInfo_784_);
lean_closure_set(v___f_788_, 2, v_expr_785_);
lean_closure_set(v___f_788_, 3, v___x_787_);
v___x_789_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_782_, v_ctx_781_, v___f_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___boxed(lean_object* v_ctx_790_, lean_object* v_info_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_Elab_TermInfo_format(v_ctx_790_, v_info_791_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialTermInfo_format(lean_object* v_ctx_797_, lean_object* v_info_798_){
_start:
{
lean_object* v_toElabInfo_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_toElabInfo_799_ = lean_ctor_get(v_info_798_, 0);
lean_inc_ref(v_toElabInfo_799_);
lean_dec_ref(v_info_798_);
v___x_800_ = ((lean_object*)(l_Lean_Elab_PartialTermInfo_format___closed__1));
v___x_801_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_797_, v_toElabInfo_799_);
v___x_802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(lean_object* v_x_809_){
_start:
{
if (lean_obj_tag(v_x_809_) == 0)
{
lean_object* v___x_810_; 
v___x_810_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_810_;
}
else
{
lean_object* v_val_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_821_; 
v_val_811_ = lean_ctor_get(v_x_809_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v_x_809_);
if (v_isSharedCheck_821_ == 0)
{
v___x_813_ = v_x_809_;
v_isShared_814_ = v_isSharedCheck_821_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_val_811_);
lean_dec(v_x_809_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_821_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_815_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_816_ = lean_expr_dbg_to_string(v_val_811_);
lean_dec(v_val_811_);
if (v_isShared_814_ == 0)
{
lean_ctor_set_tag(v___x_813_, 3);
lean_ctor_set(v___x_813_, 0, v___x_816_);
v___x_818_ = v___x_813_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_820_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; 
v___x_819_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_815_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
return v___x_819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0(lean_object* v_ctx_828_, lean_object* v_lctx_829_, lean_object* v_stx_830_, lean_object* v_expectedType_x3f_831_, lean_object* v_info_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___x_838_; lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_857_; 
v___x_838_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_828_, v_lctx_829_, v_stx_830_);
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_857_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_857_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_857_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_843_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__1));
v___x_844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
lean_ctor_set(v___x_844_, 1, v_a_839_);
v___x_845_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_844_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_831_);
v___x_848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = l_Lean_Elab_CompletionInfo_stx(v_info_832_);
v___x_852_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_828_, v___x_851_);
lean_dec(v___x_851_);
v___x_853_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_850_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_853_);
v___x_855_ = v___x_841_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___boxed(lean_object* v_ctx_858_, lean_object* v_lctx_859_, lean_object* v_stx_860_, lean_object* v_expectedType_x3f_861_, lean_object* v_info_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Elab_CompletionInfo_format___lam__0(v_ctx_858_, v_lctx_859_, v_stx_860_, v_expectedType_x3f_861_, v_info_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec_ref(v_info_862_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format(lean_object* v_ctx_875_, lean_object* v_info_876_){
_start:
{
switch(lean_obj_tag(v_info_876_))
{
case 0:
{
lean_object* v_termInfo_878_; lean_object* v_expectedType_x3f_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_900_; 
v_termInfo_878_ = lean_ctor_get(v_info_876_, 0);
v_expectedType_x3f_879_ = lean_ctor_get(v_info_876_, 1);
v_isSharedCheck_900_ = !lean_is_exclusive(v_info_876_);
if (v_isSharedCheck_900_ == 0)
{
v___x_881_ = v_info_876_;
v_isShared_882_ = v_isSharedCheck_900_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_expectedType_x3f_879_);
lean_inc(v_termInfo_878_);
lean_dec(v_info_876_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_900_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_Elab_TermInfo_format(v_ctx_875_, v_termInfo_878_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_899_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_899_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_899_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_899_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_888_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__1));
if (v_isShared_882_ == 0)
{
lean_ctor_set_tag(v___x_881_, 5);
lean_ctor_set(v___x_881_, 1, v_a_884_);
lean_ctor_set(v___x_881_, 0, v___x_888_);
v___x_890_ = v___x_881_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_a_884_);
v___x_890_ = v_reuseFailAlloc_898_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_891_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_879_);
v___x_894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_894_);
v___x_896_ = v___x_886_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
else
{
lean_del_object(v___x_881_);
lean_dec(v_expectedType_x3f_879_);
return v___x_883_;
}
}
}
case 1:
{
lean_object* v_stx_901_; lean_object* v_lctx_902_; lean_object* v_expectedType_x3f_903_; lean_object* v___f_904_; lean_object* v___x_905_; 
v_stx_901_ = lean_ctor_get(v_info_876_, 0);
lean_inc(v_stx_901_);
v_lctx_902_ = lean_ctor_get(v_info_876_, 2);
lean_inc_ref_n(v_lctx_902_, 2);
v_expectedType_x3f_903_ = lean_ctor_get(v_info_876_, 3);
lean_inc(v_expectedType_x3f_903_);
lean_inc_ref(v_ctx_875_);
v___f_904_ = lean_alloc_closure((void*)(l_Lean_Elab_CompletionInfo_format___lam__0___boxed), 10, 5);
lean_closure_set(v___f_904_, 0, v_ctx_875_);
lean_closure_set(v___f_904_, 1, v_lctx_902_);
lean_closure_set(v___f_904_, 2, v_stx_901_);
lean_closure_set(v___f_904_, 3, v_expectedType_x3f_903_);
lean_closure_set(v___f_904_, 4, v_info_876_);
v___x_905_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_875_, v_lctx_902_, v___f_904_);
return v___x_905_;
}
default: 
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_906_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__3));
v___x_907_ = l_Lean_Elab_CompletionInfo_stx(v_info_876_);
lean_dec_ref(v_info_876_);
v___x_908_ = lean_box(0);
v___x_909_ = 0;
lean_inc(v___x_907_);
v___x_910_ = l_Lean_Syntax_formatStx(v___x_907_, v___x_908_, v___x_909_);
v___x_911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_906_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_875_, v___x_907_);
lean_dec(v___x_907_);
v___x_915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___boxed(lean_object* v_ctx_917_, lean_object* v_info_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Elab_CompletionInfo_format(v_ctx_917_, v_info_918_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format(lean_object* v_ctx_924_, lean_object* v_info_925_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format___boxed(lean_object* v_ctx_931_, lean_object* v_info_932_, lean_object* v_a_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_Elab_CommandInfo_format(v_ctx_931_, v_info_932_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format(lean_object* v_ctx_938_, lean_object* v_info_939_){
_start:
{
lean_object* v_stx_941_; lean_object* v_optionName_942_; lean_object* v___x_943_; uint8_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v_stx_941_ = lean_ctor_get(v_info_939_, 0);
lean_inc(v_stx_941_);
v_optionName_942_ = lean_ctor_get(v_info_939_, 1);
lean_inc(v_optionName_942_);
lean_dec_ref(v_info_939_);
v___x_943_ = ((lean_object*)(l_Lean_Elab_OptionInfo_format___closed__1));
v___x_944_ = 1;
v___x_945_ = l_Lean_Name_toString(v_optionName_942_, v___x_944_);
v___x_946_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
v___x_947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_943_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_947_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_938_, v_stx_941_);
lean_dec(v_stx_941_);
v___x_951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_949_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format___boxed(lean_object* v_ctx_953_, lean_object* v_info_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Elab_OptionInfo_format(v_ctx_953_, v_info_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format(lean_object* v_ctx_960_, lean_object* v_info_961_){
_start:
{
lean_object* v_stx_963_; lean_object* v_errorName_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_980_; 
v_stx_963_ = lean_ctor_get(v_info_961_, 0);
v_errorName_964_ = lean_ctor_get(v_info_961_, 1);
v_isSharedCheck_980_ = !lean_is_exclusive(v_info_961_);
if (v_isSharedCheck_980_ == 0)
{
v___x_966_ = v_info_961_;
v_isShared_967_ = v_isSharedCheck_980_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_errorName_964_);
lean_inc(v_stx_963_);
lean_dec(v_info_961_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_980_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_968_ = ((lean_object*)(l_Lean_Elab_ErrorNameInfo_format___closed__1));
v___x_969_ = 1;
v___x_970_ = l_Lean_Name_toString(v_errorName_964_, v___x_969_);
v___x_971_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
if (v_isShared_967_ == 0)
{
lean_ctor_set_tag(v___x_966_, 5);
lean_ctor_set(v___x_966_, 1, v___x_971_);
lean_ctor_set(v___x_966_, 0, v___x_968_);
v___x_973_ = v___x_966_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v___x_971_);
v___x_973_ = v_reuseFailAlloc_979_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_974_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_960_, v_stx_963_);
lean_dec(v_stx_963_);
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
return v___x_978_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format___boxed(lean_object* v_ctx_981_, lean_object* v_info_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_981_, v_info_982_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0(lean_object* v_val_991_, lean_object* v_fieldName_992_, lean_object* v_ctx_993_, lean_object* v_stx_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
lean_inc(v___y_998_);
lean_inc_ref(v___y_997_);
lean_inc(v___y_996_);
lean_inc_ref(v___y_995_);
lean_inc_ref(v_val_991_);
v___x_1000_ = lean_infer_type(v_val_991_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = l_Lean_Meta_ppExpr(v_a_1001_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1033_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1033_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1033_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_Meta_ppExpr(v_val_991_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1032_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1010_ = v___x_1007_;
v_isShared_1011_ = v_isSharedCheck_1032_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1032_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; uint8_t v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1012_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__1));
v___x_1013_ = 1;
v___x_1014_ = l_Lean_Name_toString(v_fieldName_992_, v___x_1013_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set_tag(v___x_1005_, 3);
lean_ctor_set(v___x_1005_, 0, v___x_1014_);
v___x_1016_ = v___x_1005_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1012_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v_a_1003_);
v___x_1021_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__3));
v___x_1022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v_a_1008_);
v___x_1024_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1023_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_993_, v_stx_994_);
v___x_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1027_);
v___x_1029_ = v___x_1010_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
else
{
lean_del_object(v___x_1005_);
lean_dec(v_a_1003_);
lean_dec_ref(v_ctx_993_);
lean_dec(v_fieldName_992_);
return v___x_1007_;
}
}
}
else
{
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec_ref(v_ctx_993_);
lean_dec(v_fieldName_992_);
lean_dec_ref(v_val_991_);
return v___x_1002_;
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec_ref(v_ctx_993_);
lean_dec(v_fieldName_992_);
lean_dec_ref(v_val_991_);
v_a_1034_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1000_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1000_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0___boxed(lean_object* v_val_1042_, lean_object* v_fieldName_1043_, lean_object* v_ctx_1044_, lean_object* v_stx_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_Elab_FieldInfo_format___lam__0(v_val_1042_, v_fieldName_1043_, v_ctx_1044_, v_stx_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v_stx_1045_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format(lean_object* v_ctx_1052_, lean_object* v_info_1053_){
_start:
{
lean_object* v_fieldName_1055_; lean_object* v_lctx_1056_; lean_object* v_val_1057_; lean_object* v_stx_1058_; lean_object* v___f_1059_; lean_object* v___x_1060_; 
v_fieldName_1055_ = lean_ctor_get(v_info_1053_, 1);
lean_inc(v_fieldName_1055_);
v_lctx_1056_ = lean_ctor_get(v_info_1053_, 2);
lean_inc_ref(v_lctx_1056_);
v_val_1057_ = lean_ctor_get(v_info_1053_, 3);
lean_inc_ref(v_val_1057_);
v_stx_1058_ = lean_ctor_get(v_info_1053_, 4);
lean_inc(v_stx_1058_);
lean_dec_ref(v_info_1053_);
lean_inc_ref(v_ctx_1052_);
v___f_1059_ = lean_alloc_closure((void*)(l_Lean_Elab_FieldInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1059_, 0, v_val_1057_);
lean_closure_set(v___f_1059_, 1, v_fieldName_1055_);
lean_closure_set(v___f_1059_, 2, v_ctx_1052_);
lean_closure_set(v___f_1059_, 3, v_stx_1058_);
v___x_1060_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1052_, v_lctx_1056_, v___f_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___boxed(lean_object* v_ctx_1061_, lean_object* v_info_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_Elab_FieldInfo_format(v_ctx_1061_, v_info_1062_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(lean_object* v_pre_1065_, lean_object* v_x_1066_, lean_object* v_x_1067_){
_start:
{
if (lean_obj_tag(v_x_1067_) == 0)
{
lean_dec(v_pre_1065_);
return v_x_1066_;
}
else
{
lean_object* v_head_1068_; lean_object* v_tail_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1078_; 
v_head_1068_ = lean_ctor_get(v_x_1067_, 0);
v_tail_1069_ = lean_ctor_get(v_x_1067_, 1);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_x_1067_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1071_ = v_x_1067_;
v_isShared_1072_ = v_isSharedCheck_1078_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_tail_1069_);
lean_inc(v_head_1068_);
lean_dec(v_x_1067_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1078_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
lean_inc(v_pre_1065_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set_tag(v___x_1071_, 5);
lean_ctor_set(v___x_1071_, 1, v_pre_1065_);
lean_ctor_set(v___x_1071_, 0, v_x_1066_);
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_x_1066_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_pre_1065_);
v___x_1074_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v_head_1068_);
v_x_1066_ = v___x_1075_;
v_x_1067_ = v_tail_1069_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(lean_object* v_pre_1079_, lean_object* v_x_1080_){
_start:
{
if (lean_obj_tag(v_x_1080_) == 0)
{
lean_object* v___x_1081_; 
lean_dec(v_pre_1079_);
v___x_1081_ = lean_box(0);
return v___x_1081_;
}
else
{
lean_object* v_head_1082_; lean_object* v_tail_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1091_; 
v_head_1082_ = lean_ctor_get(v_x_1080_, 0);
v_tail_1083_ = lean_ctor_get(v_x_1080_, 1);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_x_1080_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1085_ = v_x_1080_;
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_tail_1083_);
lean_inc(v_head_1082_);
lean_dec(v_x_1080_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
lean_inc(v_pre_1079_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 5);
lean_ctor_set(v___x_1085_, 1, v_head_1082_);
lean_ctor_set(v___x_1085_, 0, v_pre_1079_);
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_pre_1079_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_head_1082_);
v___x_1088_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(v_pre_1079_, v___x_1088_, v_tail_1083_);
return v___x_1089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(lean_object* v_x_1092_, lean_object* v_x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
if (lean_obj_tag(v_x_1092_) == 0)
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = l_List_reverse___redArg(v_x_1093_);
v___x_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
return v___x_1100_;
}
else
{
lean_object* v_head_1101_; lean_object* v_tail_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1120_; 
v_head_1101_ = lean_ctor_get(v_x_1092_, 0);
v_tail_1102_ = lean_ctor_get(v_x_1092_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_x_1092_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1104_ = v_x_1092_;
v_isShared_1105_ = v_isSharedCheck_1120_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_tail_1102_);
lean_inc(v_head_1101_);
lean_dec(v_x_1092_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1120_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_Meta_ppGoal(v_head_1101_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v_head_1101_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1109_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___x_1106_, 1);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 1, v_x_1093_);
lean_ctor_set(v___x_1104_, 0, v_a_1107_);
v___x_1109_ = v___x_1104_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1107_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_x_1093_);
v___x_1109_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
v_x_1092_ = v_tail_1102_;
v_x_1093_ = v___x_1109_;
goto _start;
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_del_object(v___x_1104_);
lean_dec(v_tail_1102_);
lean_dec(v_x_1093_);
v_a_1112_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1106_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1106_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(lean_object* v_x_1121_, lean_object* v_x_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_x_1121_, v_x_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0(lean_object* v_goals_1132_, lean_object* v___x_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_goals_1132_, v___x_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1149_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1149_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1149_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1144_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1145_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1144_, v_a_1140_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1145_);
v___x_1147_ = v___x_1142_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
v_a_1150_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1139_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1139_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(lean_object* v_goals_1158_, lean_object* v___x_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0(v_goals_1158_, v___x_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
return v_res_1165_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0(void){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1166_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__0, &l_Lean_Elab_ContextInfo_ppGoals___closed__0_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0);
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1169_ = lean_unsigned_to_nat(32u);
v___x_1170_ = lean_mk_empty_array_with_capacity(v___x_1169_);
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
return v___x_1171_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3(void){
_start:
{
size_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1172_ = ((size_t)5ULL);
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = lean_unsigned_to_nat(32u);
v___x_1175_ = lean_mk_empty_array_with_capacity(v___x_1174_);
v___x_1176_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_1177_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
lean_ctor_set(v___x_1177_, 1, v___x_1175_);
lean_ctor_set(v___x_1177_, 2, v___x_1173_);
lean_ctor_set(v___x_1177_, 3, v___x_1173_);
lean_ctor_set_usize(v___x_1177_, 4, v___x_1172_);
return v___x_1177_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1178_ = lean_box(1);
v___x_1179_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_1180_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__1, &l_Lean_Elab_ContextInfo_ppGoals___closed__1_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1);
v___x_1181_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set(v___x_1181_, 1, v___x_1179_);
lean_ctor_set(v___x_1181_, 2, v___x_1178_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object* v_ctx_1185_, lean_object* v_goals_1186_){
_start:
{
uint8_t v___x_1188_; 
v___x_1188_ = l_List_isEmpty___redArg(v_goals_1186_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___f_1191_; lean_object* v___x_1192_; 
v___x_1189_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__4, &l_Lean_Elab_ContextInfo_ppGoals___closed__4_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4);
v___x_1190_ = lean_box(0);
v___f_1191_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1191_, 0, v_goals_1186_);
lean_closure_set(v___f_1191_, 1, v___x_1190_);
v___x_1192_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1185_, v___x_1189_, v___f_1191_);
return v___x_1192_;
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec(v_goals_1186_);
lean_dec_ref(v_ctx_1185_);
v___x_1193_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___closed__6));
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object* v_ctx_1195_, lean_object* v_goals_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctx_1195_, v_goals_1196_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format(lean_object* v_ctx_1208_, lean_object* v_info_1209_){
_start:
{
lean_object* v_toCommandContextInfo_1211_; lean_object* v_parentDecl_x3f_1212_; lean_object* v_autoImplicits_1213_; lean_object* v_env_1214_; lean_object* v_cmdEnv_x3f_1215_; lean_object* v_fileMap_1216_; lean_object* v_options_1217_; lean_object* v_currNamespace_1218_; lean_object* v_openDecls_1219_; lean_object* v_ngen_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1262_; 
v_toCommandContextInfo_1211_ = lean_ctor_get(v_ctx_1208_, 0);
lean_inc_ref(v_toCommandContextInfo_1211_);
v_parentDecl_x3f_1212_ = lean_ctor_get(v_ctx_1208_, 1);
v_autoImplicits_1213_ = lean_ctor_get(v_ctx_1208_, 2);
v_env_1214_ = lean_ctor_get(v_toCommandContextInfo_1211_, 0);
v_cmdEnv_x3f_1215_ = lean_ctor_get(v_toCommandContextInfo_1211_, 1);
v_fileMap_1216_ = lean_ctor_get(v_toCommandContextInfo_1211_, 2);
v_options_1217_ = lean_ctor_get(v_toCommandContextInfo_1211_, 4);
v_currNamespace_1218_ = lean_ctor_get(v_toCommandContextInfo_1211_, 5);
v_openDecls_1219_ = lean_ctor_get(v_toCommandContextInfo_1211_, 6);
v_ngen_1220_ = lean_ctor_get(v_toCommandContextInfo_1211_, 7);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_toCommandContextInfo_1211_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v_toCommandContextInfo_1211_, 3);
lean_dec(v_unused_1263_);
v___x_1222_ = v_toCommandContextInfo_1211_;
v_isShared_1223_ = v_isSharedCheck_1262_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_ngen_1220_);
lean_inc(v_openDecls_1219_);
lean_inc(v_currNamespace_1218_);
lean_inc(v_options_1217_);
lean_inc(v_fileMap_1216_);
lean_inc(v_cmdEnv_x3f_1215_);
lean_inc(v_env_1214_);
lean_dec(v_toCommandContextInfo_1211_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1262_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v_toElabInfo_1224_; lean_object* v_mctxBefore_1225_; lean_object* v_goalsBefore_1226_; lean_object* v_mctxAfter_1227_; lean_object* v_goalsAfter_1228_; lean_object* v___x_1230_; 
v_toElabInfo_1224_ = lean_ctor_get(v_info_1209_, 0);
lean_inc_ref(v_toElabInfo_1224_);
v_mctxBefore_1225_ = lean_ctor_get(v_info_1209_, 1);
lean_inc_ref(v_mctxBefore_1225_);
v_goalsBefore_1226_ = lean_ctor_get(v_info_1209_, 2);
lean_inc(v_goalsBefore_1226_);
v_mctxAfter_1227_ = lean_ctor_get(v_info_1209_, 3);
lean_inc_ref(v_mctxAfter_1227_);
v_goalsAfter_1228_ = lean_ctor_get(v_info_1209_, 4);
lean_inc(v_goalsAfter_1228_);
lean_dec_ref(v_info_1209_);
lean_inc_ref(v_ngen_1220_);
lean_inc(v_openDecls_1219_);
lean_inc(v_currNamespace_1218_);
lean_inc_ref(v_options_1217_);
lean_inc_ref(v_fileMap_1216_);
lean_inc(v_cmdEnv_x3f_1215_);
lean_inc_ref(v_env_1214_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 3, v_mctxBefore_1225_);
v___x_1230_ = v___x_1222_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_env_1214_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_cmdEnv_x3f_1215_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_fileMap_1216_);
lean_ctor_set(v_reuseFailAlloc_1261_, 3, v_mctxBefore_1225_);
lean_ctor_set(v_reuseFailAlloc_1261_, 4, v_options_1217_);
lean_ctor_set(v_reuseFailAlloc_1261_, 5, v_currNamespace_1218_);
lean_ctor_set(v_reuseFailAlloc_1261_, 6, v_openDecls_1219_);
lean_ctor_set(v_reuseFailAlloc_1261_, 7, v_ngen_1220_);
v___x_1230_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v_ctxB_1231_; lean_object* v___x_1232_; 
lean_inc_ref(v_autoImplicits_1213_);
lean_inc(v_parentDecl_x3f_1212_);
v_ctxB_1231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxB_1231_, 0, v___x_1230_);
lean_ctor_set(v_ctxB_1231_, 1, v_parentDecl_x3f_1212_);
lean_ctor_set(v_ctxB_1231_, 2, v_autoImplicits_1213_);
v___x_1232_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxB_1231_, v_goalsBefore_1226_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1234_; lean_object* v_ctxA_1235_; lean_object* v___x_1236_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 1);
v___x_1234_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1234_, 0, v_env_1214_);
lean_ctor_set(v___x_1234_, 1, v_cmdEnv_x3f_1215_);
lean_ctor_set(v___x_1234_, 2, v_fileMap_1216_);
lean_ctor_set(v___x_1234_, 3, v_mctxAfter_1227_);
lean_ctor_set(v___x_1234_, 4, v_options_1217_);
lean_ctor_set(v___x_1234_, 5, v_currNamespace_1218_);
lean_ctor_set(v___x_1234_, 6, v_openDecls_1219_);
lean_ctor_set(v___x_1234_, 7, v_ngen_1220_);
lean_inc_ref(v_autoImplicits_1213_);
lean_inc(v_parentDecl_x3f_1212_);
v_ctxA_1235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxA_1235_, 0, v___x_1234_);
lean_ctor_set(v_ctxA_1235_, 1, v_parentDecl_x3f_1212_);
lean_ctor_set(v_ctxA_1235_, 2, v_autoImplicits_1213_);
v___x_1236_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxA_1235_, v_goalsAfter_1228_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1260_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1239_ = v___x_1236_;
v_isShared_1240_ = v_isSharedCheck_1260_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1260_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v_stx_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1258_; 
v_stx_1241_ = lean_ctor_get(v_toElabInfo_1224_, 1);
lean_inc(v_stx_1241_);
v___x_1242_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__1));
v___x_1243_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1208_, v_toElabInfo_1224_);
v___x_1244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1242_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1244_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = lean_box(0);
v___x_1248_ = 0;
v___x_1249_ = l_Lean_Syntax_formatStx(v_stx_1241_, v___x_1247_, v___x_1248_);
v___x_1250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1246_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__3));
v___x_1252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v_a_1233_);
v___x_1254_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__5));
v___x_1255_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1253_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
v___x_1256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
lean_ctor_set(v___x_1256_, 1, v_a_1237_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1256_);
v___x_1258_ = v___x_1239_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
else
{
lean_dec(v_a_1233_);
lean_dec_ref(v_toElabInfo_1224_);
lean_dec_ref(v_ctx_1208_);
return v___x_1236_;
}
}
else
{
lean_dec(v_goalsAfter_1228_);
lean_dec_ref(v_mctxAfter_1227_);
lean_dec_ref(v_toElabInfo_1224_);
lean_dec_ref(v_ngen_1220_);
lean_dec(v_openDecls_1219_);
lean_dec(v_currNamespace_1218_);
lean_dec_ref(v_options_1217_);
lean_dec_ref(v_fileMap_1216_);
lean_dec(v_cmdEnv_x3f_1215_);
lean_dec_ref(v_env_1214_);
lean_dec_ref(v_ctx_1208_);
return v___x_1232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format___boxed(lean_object* v_ctx_1264_, lean_object* v_info_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_Elab_TacticInfo_format(v_ctx_1264_, v_info_1265_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object* v_ctx_1274_, lean_object* v_info_1275_){
_start:
{
lean_object* v_lctx_1277_; lean_object* v_stx_1278_; lean_object* v_output_1279_; lean_object* v___x_1280_; lean_object* v_a_1281_; lean_object* v___x_1282_; lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1295_; 
v_lctx_1277_ = lean_ctor_get(v_info_1275_, 0);
lean_inc_ref_n(v_lctx_1277_, 2);
v_stx_1278_ = lean_ctor_get(v_info_1275_, 1);
lean_inc(v_stx_1278_);
v_output_1279_ = lean_ctor_get(v_info_1275_, 2);
lean_inc(v_output_1279_);
lean_dec_ref(v_info_1275_);
v___x_1280_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1274_, v_lctx_1277_, v_stx_1278_);
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref(v___x_1280_);
v___x_1282_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1274_, v_lctx_1277_, v_output_1279_);
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1295_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1295_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1287_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__1));
v___x_1288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
lean_ctor_set(v___x_1288_, 1, v_a_1281_);
v___x_1289_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__3));
v___x_1290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v_a_1283_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1291_);
v___x_1293_ = v___x_1285_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object* v_ctx_1296_, lean_object* v_info_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1296_, v_info_1297_);
lean_dec_ref(v_ctx_1296_);
return v_res_1299_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__0(void){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1300_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__1(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__0, &l_Lean_Elab_UserWidgetInfo_format___closed__0_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__0);
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
return v___x_1302_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__2(void){
_start:
{
uint8_t v___x_1303_; size_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1303_ = 1;
v___x_1304_ = ((size_t)0ULL);
v___x_1305_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__1, &l_Lean_Elab_UserWidgetInfo_format___closed__1_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__1);
v___x_1306_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
lean_ctor_set_usize(v___x_1306_, 2, v___x_1304_);
lean_ctor_set_uint8(v___x_1306_, sizeof(void*)*3, v___x_1303_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_UserWidgetInfo_format(lean_object* v_info_1310_){
_start:
{
lean_object* v_toWidgetInstance_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1340_; 
v_toWidgetInstance_1311_ = lean_ctor_get(v_info_1310_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_info_1310_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; 
v_unused_1341_ = lean_ctor_get(v_info_1310_, 1);
lean_dec(v_unused_1341_);
v___x_1313_ = v_info_1310_;
v_isShared_1314_ = v_isSharedCheck_1340_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_toWidgetInstance_1311_);
lean_dec(v_info_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1340_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v_id_1315_; lean_object* v_props_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v_fst_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1338_; 
v_id_1315_ = lean_ctor_get(v_toWidgetInstance_1311_, 0);
lean_inc(v_id_1315_);
v_props_1316_ = lean_ctor_get(v_toWidgetInstance_1311_, 1);
lean_inc_ref(v_props_1316_);
lean_dec_ref(v_toWidgetInstance_1311_);
v___x_1317_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__2, &l_Lean_Elab_UserWidgetInfo_format___closed__2_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__2);
v___x_1318_ = lean_apply_1(v_props_1316_, v___x_1317_);
v_fst_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1338_ == 0)
{
lean_object* v_unused_1339_; 
v_unused_1339_ = lean_ctor_get(v___x_1318_, 1);
lean_dec(v_unused_1339_);
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1338_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_fst_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1338_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; uint8_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1323_ = ((lean_object*)(l_Lean_Elab_UserWidgetInfo_format___closed__4));
v___x_1324_ = 1;
v___x_1325_ = l_Lean_Name_toString(v_id_1315_, v___x_1324_);
v___x_1326_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set_tag(v___x_1321_, 5);
lean_ctor_set(v___x_1321_, 1, v___x_1326_);
lean_ctor_set(v___x_1321_, 0, v___x_1323_);
v___x_1328_ = v___x_1321_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1329_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
if (v_isShared_1314_ == 0)
{
lean_ctor_set_tag(v___x_1313_, 5);
lean_ctor_set(v___x_1313_, 1, v___x_1329_);
lean_ctor_set(v___x_1313_, 0, v___x_1328_);
v___x_1331_ = v___x_1313_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1332_ = lean_unsigned_to_nat(80u);
v___x_1333_ = l_Lean_Json_pretty(v_fst_1319_, v___x_1332_);
v___x_1334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
v___x_1335_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1331_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
return v___x_1335_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FVarAliasInfo_format(lean_object* v_info_1348_){
_start:
{
lean_object* v_userName_1349_; lean_object* v_id_1350_; lean_object* v_baseId_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v_userName_1349_ = lean_ctor_get(v_info_1348_, 0);
lean_inc(v_userName_1349_);
v_id_1350_ = lean_ctor_get(v_info_1348_, 1);
lean_inc(v_id_1350_);
v_baseId_1351_ = lean_ctor_get(v_info_1348_, 2);
lean_inc(v_baseId_1351_);
lean_dec_ref(v_info_1348_);
v___x_1352_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__1));
v___x_1353_ = l_Lean_Name_eraseMacroScopes(v_userName_1349_);
lean_dec(v_userName_1349_);
v___x_1354_ = 1;
v___x_1355_ = l_Lean_Name_toString(v___x_1353_, v___x_1354_);
v___x_1356_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
v___x_1357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1352_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_1359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = l_Lean_Name_toString(v_id_1350_, v___x_1354_);
v___x_1361_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
v___x_1362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1359_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v___x_1363_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__3));
v___x_1364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1362_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v___x_1365_ = l_Lean_Name_toString(v_baseId_1351_, v___x_1354_);
v___x_1366_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
v___x_1367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1364_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format(lean_object* v_ctx_1371_, lean_object* v_info_1372_){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1373_ = ((lean_object*)(l_Lean_Elab_FieldRedeclInfo_format___closed__1));
v___x_1374_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1371_, v_info_1372_);
v___x_1375_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format___boxed(lean_object* v_ctx_1376_, lean_object* v_info_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1376_, v_info_1377_);
lean_dec(v_info_1377_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f(lean_object* v_ppCtx_1381_, lean_object* v_info_1382_){
_start:
{
lean_object* v_mkDocString_x3f_1384_; 
v_mkDocString_x3f_1384_ = lean_ctor_get(v_info_1382_, 2);
lean_inc(v_mkDocString_x3f_1384_);
lean_dec_ref(v_info_1382_);
if (lean_obj_tag(v_mkDocString_x3f_1384_) == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_dec_ref(v_ppCtx_1381_);
v___x_1385_ = lean_box(0);
v___x_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
return v___x_1386_;
}
else
{
lean_object* v_val_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1419_; 
v_val_1387_ = lean_ctor_get(v_mkDocString_x3f_1384_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_mkDocString_x3f_1384_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1389_ = v_mkDocString_x3f_1384_;
v_isShared_1390_ = v_isSharedCheck_1419_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_val_1387_);
lean_dec(v_mkDocString_x3f_1384_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1419_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_apply_2(v_val_1387_, v_ppCtx_1381_, lean_box(0));
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1402_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1394_ = v___x_1391_;
v_isShared_1395_ = v_isSharedCheck_1402_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1391_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1402_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v_a_1392_);
v___x_1397_ = v___x_1389_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1399_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1397_);
v___x_1399_ = v___x_1394_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1418_; 
v_a_1403_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1405_ = v___x_1391_;
v_isShared_1406_ = v_isSharedCheck_1418_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1391_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1418_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1407_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0));
v___x_1408_ = lean_io_error_to_string(v_a_1403_);
v___x_1409_ = lean_string_append(v___x_1407_, v___x_1408_);
lean_dec_ref(v___x_1408_);
v___x_1410_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1411_ = lean_string_append(v___x_1409_, v___x_1410_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1411_);
v___x_1413_ = v___x_1389_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1415_; 
if (v_isShared_1406_ == 0)
{
lean_ctor_set_tag(v___x_1405_, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1413_);
v___x_1415_ = v___x_1405_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___boxed(lean_object* v_ppCtx_1420_, lean_object* v_info_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_ppCtx_1420_, v_info_1421_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(lean_object* v_x_1424_, lean_object* v_x_1425_){
_start:
{
if (lean_obj_tag(v_x_1424_) == 0)
{
lean_object* v___x_1426_; 
v___x_1426_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_1426_;
}
else
{
lean_object* v_val_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1438_; 
v_val_1427_ = lean_ctor_get(v_x_1424_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_x_1424_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1429_ = v_x_1424_;
v_isShared_1430_ = v_isSharedCheck_1438_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_val_1427_);
lean_dec(v_x_1424_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1438_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1431_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_1432_ = l_String_quote(v_val_1427_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set_tag(v___x_1429_, 3);
lean_ctor_set(v___x_1429_, 0, v___x_1432_);
v___x_1434_ = v___x_1429_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1431_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = l_Repr_addAppParen(v___x_1435_, v_x_1425_);
return v___x_1436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(lean_object* v_x_1439_, lean_object* v_x_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_x_1439_, v_x_1440_);
lean_dec(v_x_1440_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object* v_ctx_1456_, lean_object* v_info_1457_){
_start:
{
lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v_toTermInfo_1465_; lean_object* v_location_x3f_1466_; uint8_t v_explicit_1467_; lean_object* v___y_1469_; 
v_toTermInfo_1465_ = lean_ctor_get(v_info_1457_, 0);
lean_inc_ref(v_toTermInfo_1465_);
v_location_x3f_1466_ = lean_ctor_get(v_info_1457_, 1);
lean_inc(v_location_x3f_1466_);
v_explicit_1467_ = lean_ctor_get_uint8(v_info_1457_, sizeof(void*)*3);
if (lean_obj_tag(v_location_x3f_1466_) == 1)
{
lean_object* v_val_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1551_; 
v_val_1490_ = lean_ctor_get(v_location_x3f_1466_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_location_x3f_1466_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1492_ = v_location_x3f_1466_;
v_isShared_1493_ = v_isSharedCheck_1551_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_val_1490_);
lean_dec(v_location_x3f_1466_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1551_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v_range_1494_; lean_object* v_pos_1495_; lean_object* v_endPos_1496_; lean_object* v_module_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1549_; 
v_range_1494_ = lean_ctor_get(v_val_1490_, 1);
v_pos_1495_ = lean_ctor_get(v_range_1494_, 0);
lean_inc_ref(v_pos_1495_);
v_endPos_1496_ = lean_ctor_get(v_range_1494_, 2);
lean_inc_ref(v_endPos_1496_);
v_module_1497_ = lean_ctor_get(v_val_1490_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_val_1490_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; 
v_unused_1550_ = lean_ctor_get(v_val_1490_, 1);
lean_dec(v_unused_1550_);
v___x_1499_ = v_val_1490_;
v_isShared_1500_ = v_isSharedCheck_1549_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_module_1497_);
lean_dec(v_val_1490_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1549_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v_line_1501_; lean_object* v_column_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1548_; 
v_line_1501_ = lean_ctor_get(v_pos_1495_, 0);
v_column_1502_ = lean_ctor_get(v_pos_1495_, 1);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_pos_1495_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1504_ = v_pos_1495_;
v_isShared_1505_ = v_isSharedCheck_1548_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_column_1502_);
lean_inc(v_line_1501_);
lean_dec(v_pos_1495_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1548_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v_line_1506_; lean_object* v_column_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1547_; 
v_line_1506_ = lean_ctor_get(v_endPos_1496_, 0);
v_column_1507_ = lean_ctor_get(v_endPos_1496_, 1);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_endPos_1496_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1509_ = v_endPos_1496_;
v_isShared_1510_ = v_isSharedCheck_1547_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_column_1507_);
lean_inc(v_line_1506_);
lean_dec(v_endPos_1496_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1547_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
uint8_t v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1511_ = 1;
v___x_1512_ = l_Lean_Name_toString(v_module_1497_, v___x_1511_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set_tag(v___x_1492_, 3);
lean_ctor_set(v___x_1492_, 0, v___x_1512_);
v___x_1514_ = v___x_1492_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1515_; lean_object* v___x_1517_; 
v___x_1515_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
if (v_isShared_1510_ == 0)
{
lean_ctor_set_tag(v___x_1509_, 5);
lean_ctor_set(v___x_1509_, 1, v___x_1515_);
lean_ctor_set(v___x_1509_, 0, v___x_1514_);
v___x_1517_ = v___x_1509_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1518_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_1519_ = l_Nat_reprFast(v_line_1501_);
v___x_1520_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set_tag(v___x_1504_, 5);
lean_ctor_set(v___x_1504_, 1, v___x_1520_);
lean_ctor_set(v___x_1504_, 0, v___x_1518_);
v___x_1522_ = v___x_1504_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1523_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
if (v_isShared_1500_ == 0)
{
lean_ctor_set_tag(v___x_1499_, 5);
lean_ctor_set(v___x_1499_, 1, v___x_1523_);
lean_ctor_set(v___x_1499_, 0, v___x_1522_);
v___x_1525_ = v___x_1499_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1526_ = l_Nat_reprFast(v_column_1502_);
v___x_1527_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
v___x_1528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1525_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v___x_1530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1517_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_1533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = l_Nat_reprFast(v_line_1506_);
v___x_1535_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
v___x_1536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1518_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
lean_ctor_set(v___x_1537_, 1, v___x_1523_);
v___x_1538_ = l_Nat_reprFast(v_column_1507_);
v___x_1539_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
v___x_1540_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1537_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
lean_ctor_set(v___x_1541_, 1, v___x_1529_);
v___x_1542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1533_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___y_1469_ = v___x_1542_;
goto v___jp_1468_;
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
lean_object* v___x_1552_; 
lean_dec(v_location_x3f_1466_);
v___x_1552_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
v___y_1469_ = v___x_1552_;
goto v___jp_1468_;
}
v___jp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_inc_ref(v___y_1461_);
v___x_1462_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1462_, 0, v___y_1461_);
v___x_1463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___y_1460_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
return v___x_1464_;
}
v___jp_1468_:
{
lean_object* v_lctx_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v_a_1473_; lean_object* v___x_1474_; 
v_lctx_1470_ = lean_ctor_get(v_toTermInfo_1465_, 1);
lean_inc_ref(v_lctx_1470_);
v___x_1471_ = l_Lean_Elab_ContextInfo_toPPContext(v_ctx_1456_, v_lctx_1470_);
v___x_1472_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v___x_1471_, v_info_1457_);
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref(v___x_1472_);
v___x_1474_ = l_Lean_Elab_TermInfo_format(v_ctx_1456_, v_toTermInfo_1465_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
v___x_1476_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__1));
v___x_1477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
lean_ctor_set(v___x_1477_, 1, v_a_1475_);
v___x_1478_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__3));
v___x_1479_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1477_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
lean_ctor_set(v___x_1480_, 1, v___y_1469_);
v___x_1481_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__5));
v___x_1482_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1480_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = lean_unsigned_to_nat(0u);
v___x_1484_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_a_1473_, v___x_1483_);
v___x_1485_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1482_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
v___x_1486_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__7));
v___x_1487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
if (v_explicit_1467_ == 0)
{
lean_object* v___x_1488_; 
v___x_1488_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__8));
v___y_1460_ = v___x_1487_;
v___y_1461_ = v___x_1488_;
goto v___jp_1459_;
}
else
{
lean_object* v___x_1489_; 
v___x_1489_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__9));
v___y_1460_ = v___x_1487_;
v___y_1461_ = v___x_1489_;
goto v___jp_1459_;
}
}
else
{
lean_dec(v_a_1473_);
lean_dec(v___y_1469_);
return v___x_1474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object* v_ctx_1553_, lean_object* v_info_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1553_, v_info_1554_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object* v_ctx_1560_, lean_object* v_info_1561_){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = ((lean_object*)(l_Lean_Elab_ChoiceInfo_format___closed__1));
v___x_1563_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1560_, v_info_1561_);
v___x_1564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object* v_ctx_1568_, lean_object* v_info_1569_){
_start:
{
lean_object* v_stx_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v_stx_1570_ = lean_ctor_get(v_info_1569_, 1);
v___x_1571_ = ((lean_object*)(l_Lean_Elab_DocInfo_format___closed__1));
lean_inc(v_stx_1570_);
v___x_1572_ = l_Lean_Syntax_getKind(v_stx_1570_);
v___x_1573_ = 1;
v___x_1574_ = l_Lean_Name_toString(v___x_1572_, v___x_1573_);
v___x_1575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
v___x_1576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1571_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1576_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1568_, v_info_1569_);
v___x_1580_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object* v_ctx_1590_, lean_object* v_info_1591_){
_start:
{
lean_object* v_toElabInfo_1592_; lean_object* v_name_1593_; uint8_t v_kind_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_toElabInfo_1592_ = lean_ctor_get(v_info_1591_, 0);
lean_inc_ref(v_toElabInfo_1592_);
v_name_1593_ = lean_ctor_get(v_info_1591_, 1);
lean_inc(v_name_1593_);
v_kind_1594_ = lean_ctor_get_uint8(v_info_1591_, sizeof(void*)*2);
lean_dec_ref(v_info_1591_);
v___x_1595_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__1));
v___x_1596_ = 1;
v___x_1597_ = l_Lean_Name_toString(v_name_1593_, v___x_1596_);
v___x_1598_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
v___x_1599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1595_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__3));
v___x_1601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = lean_unsigned_to_nat(0u);
v___x_1603_ = l_Lean_Elab_instReprDocElabKind_repr(v_kind_1594_, v___x_1602_);
v___x_1604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1601_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
v___x_1605_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__5));
v___x_1606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1604_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1590_, v_toElabInfo_1592_);
v___x_1608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object* v_ctx_1609_, lean_object* v_x_1610_){
_start:
{
switch(lean_obj_tag(v_x_1610_))
{
case 0:
{
lean_object* v_i_1612_; lean_object* v___x_1613_; 
v_i_1612_ = lean_ctor_get(v_x_1610_, 0);
lean_inc_ref(v_i_1612_);
lean_dec_ref_known(v_x_1610_, 1);
v___x_1613_ = l_Lean_Elab_TacticInfo_format(v_ctx_1609_, v_i_1612_);
return v___x_1613_;
}
case 1:
{
lean_object* v_i_1614_; lean_object* v___x_1615_; 
v_i_1614_ = lean_ctor_get(v_x_1610_, 0);
lean_inc_ref(v_i_1614_);
lean_dec_ref_known(v_x_1610_, 1);
v___x_1615_ = l_Lean_Elab_TermInfo_format(v_ctx_1609_, v_i_1614_);
return v___x_1615_;
}
case 2:
{
lean_object* v_i_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1624_; 
v_i_1616_ = lean_ctor_get(v_x_1610_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_x_1610_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1618_ = v_x_1610_;
v_isShared_1619_ = v_isSharedCheck_1624_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_i_1616_);
lean_dec(v_x_1610_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1624_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1622_; 
v___x_1620_ = l_Lean_Elab_PartialTermInfo_format(v_ctx_1609_, v_i_1616_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set_tag(v___x_1618_, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1620_);
v___x_1622_ = v___x_1618_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
case 3:
{
lean_object* v_i_1625_; lean_object* v___x_1626_; 
v_i_1625_ = lean_ctor_get(v_x_1610_, 0);
lean_inc_ref(v_i_1625_);
lean_dec_ref_known(v_x_1610_, 1);
v___x_1626_ = l_Lean_Elab_CommandInfo_format(v_ctx_1609_, v_i_1625_);
return v___x_1626_;
}
case 4:
{
lean_object* v_i_1627_; lean_object* v___x_1628_; 
v_i_1627_ = lean_ctor_get(v_x_1610_, 0);
lean_inc_ref(v_i_1627_);
lean_dec_ref_known(v_x_1610_, 1);
v___x_1628_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1609_, v_i_1627_);
lean_dec_ref(v_ctx_1609_);
return v___x_1628_;
}
case 5:
{
lean_object* v_i_1629_; lean_object* v___x_1630_; 
v_i_1629_ = lean_ctor_get(v_x_1610_, 0);
lean_inc_ref(v_i_1629_);
lean_dec_ref_known(v_x_1610_, 1);
v___x_1630_ = l_Lean_Elab_OptionInfo_format(v_ctx_1609_, v_i_1629_);
return v___x_1630_;
}
case 6:
{
lean_object* v_i_1631_; lean_object* v___x_1632_; 
v_i_1631_ = lean_ctor_get(v_x_1610_, 0);
lean_inc_ref(v_i_1631_);
lean_dec_ref_known(v_x_1610_, 1);
v___x_1632_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_1609_, v_i_1631_);
return v___x_1632_;
}
case 7:
{
lean_object* v_i_1633_; lean_object* v___x_1634_; 
v_i_1633_ = lean_ctor_get(v_x_1610_, 0);
lean_inc_ref(v_i_1633_);
lean_dec_ref_known(v_x_1610_, 1);
v___x_1634_ = l_Lean_Elab_FieldInfo_format(v_ctx_1609_, v_i_1633_);
return v___x_1634_;
}
case 8:
{
lean_object* v_i_1635_; lean_object* v___x_1636_; 
v_i_1635_ = lean_ctor_get(v_x_1610_, 0);
lean_inc_ref(v_i_1635_);
lean_dec_ref_known(v_x_1610_, 1);
v___x_1636_ = l_Lean_Elab_CompletionInfo_format(v_ctx_1609_, v_i_1635_);
return v___x_1636_;
}
case 9:
{
lean_object* v_i_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1645_; 
lean_dec_ref(v_ctx_1609_);
v_i_1637_ = lean_ctor_get(v_x_1610_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_x_1610_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1639_ = v_x_1610_;
v_isShared_1640_ = v_isSharedCheck_1645_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_i_1637_);
lean_dec(v_x_1610_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1645_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1641_ = l_Lean_Elab_UserWidgetInfo_format(v_i_1637_);
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
case 10:
{
lean_object* v_i_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1654_; 
lean_dec_ref(v_ctx_1609_);
v_i_1646_ = lean_ctor_get(v_x_1610_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_x_1610_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1648_ = v_x_1610_;
v_isShared_1649_ = v_isSharedCheck_1654_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_i_1646_);
lean_dec(v_x_1610_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1654_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = l_Lean_Elab_CustomInfo_format(v_i_1646_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set_tag(v___x_1648_, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1650_);
v___x_1652_ = v___x_1648_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
case 11:
{
lean_object* v_i_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1663_; 
lean_dec_ref(v_ctx_1609_);
v_i_1655_ = lean_ctor_get(v_x_1610_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_x_1610_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1657_ = v_x_1610_;
v_isShared_1658_ = v_isSharedCheck_1663_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_i_1655_);
lean_dec(v_x_1610_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1663_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1659_ = l_Lean_Elab_FVarAliasInfo_format(v_i_1655_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set_tag(v___x_1657_, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1659_);
v___x_1661_ = v___x_1657_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
case 12:
{
lean_object* v_i_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1672_; 
v_i_1664_ = lean_ctor_get(v_x_1610_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_x_1610_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1666_ = v_x_1610_;
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_i_1664_);
lean_dec(v_x_1610_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1668_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1609_, v_i_1664_);
lean_dec(v_i_1664_);
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
case 13:
{
lean_object* v_i_1673_; lean_object* v___x_1674_; 
v_i_1673_ = lean_ctor_get(v_x_1610_, 0);
lean_inc_ref(v_i_1673_);
lean_dec_ref_known(v_x_1610_, 1);
v___x_1674_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1609_, v_i_1673_);
return v___x_1674_;
}
case 14:
{
lean_object* v_i_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1683_; 
v_i_1675_ = lean_ctor_get(v_x_1610_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_x_1610_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1677_ = v_x_1610_;
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_i_1675_);
lean_dec(v_x_1610_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = l_Lean_Elab_ChoiceInfo_format(v_ctx_1609_, v_i_1675_);
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
case 15:
{
lean_object* v_i_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1692_; 
v_i_1684_ = lean_ctor_get(v_x_1610_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_x_1610_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1686_ = v_x_1610_;
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_i_1684_);
lean_dec(v_x_1610_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1688_ = l_Lean_Elab_DocInfo_format(v_ctx_1609_, v_i_1684_);
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
default: 
{
lean_object* v_i_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1701_; 
v_i_1693_ = lean_ctor_get(v_x_1610_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_x_1610_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1695_ = v_x_1610_;
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_i_1693_);
lean_dec(v_x_1610_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1697_ = l_Lean_Elab_DocElabInfo_format(v_ctx_1609_, v_i_1693_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object* v_ctx_1702_, lean_object* v_x_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_Elab_Info_format(v_ctx_1702_, v_x_1703_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object* v_x_1706_, lean_object* v_x_1707_){
_start:
{
if (lean_obj_tag(v_x_1707_) == 0)
{
return v_x_1706_;
}
else
{
lean_object* v_head_1708_; lean_object* v_tail_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_head_1708_ = lean_ctor_get(v_x_1707_, 0);
v_tail_1709_ = lean_ctor_get(v_x_1707_, 1);
v___x_1710_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2));
v___x_1711_ = lean_string_append(v_x_1706_, v___x_1710_);
v___x_1712_ = lean_expr_dbg_to_string(v_head_1708_);
v___x_1713_ = lean_string_append(v___x_1711_, v___x_1712_);
lean_dec_ref(v___x_1712_);
v_x_1706_ = v___x_1713_;
v_x_1707_ = v_tail_1709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object* v_x_1715_, lean_object* v_x_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v_x_1715_, v_x_1716_);
lean_dec(v_x_1716_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object* v_x_1720_){
_start:
{
if (lean_obj_tag(v_x_1720_) == 0)
{
lean_object* v___x_1721_; 
v___x_1721_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0));
return v___x_1721_;
}
else
{
lean_object* v_tail_1722_; 
v_tail_1722_ = lean_ctor_get(v_x_1720_, 1);
if (lean_obj_tag(v_tail_1722_) == 0)
{
lean_object* v_head_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v_head_1723_ = lean_ctor_get(v_x_1720_, 0);
v___x_1724_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1725_ = lean_expr_dbg_to_string(v_head_1723_);
v___x_1726_ = lean_string_append(v___x_1724_, v___x_1725_);
lean_dec_ref(v___x_1725_);
v___x_1727_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1728_ = lean_string_append(v___x_1726_, v___x_1727_);
return v___x_1728_;
}
else
{
lean_object* v_head_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; uint32_t v___x_1734_; lean_object* v___x_1735_; 
v_head_1729_ = lean_ctor_get(v_x_1720_, 0);
v___x_1730_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1731_ = lean_expr_dbg_to_string(v_head_1729_);
v___x_1732_ = lean_string_append(v___x_1730_, v___x_1731_);
lean_dec_ref(v___x_1731_);
v___x_1733_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v___x_1732_, v_tail_1722_);
v___x_1734_ = 93;
v___x_1735_ = lean_string_push(v___x_1733_, v___x_1734_);
return v___x_1735_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object* v_x_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v_x_1736_);
lean_dec(v_x_1736_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object* v_ctx_1744_){
_start:
{
switch(lean_obj_tag(v_ctx_1744_))
{
case 0:
{
lean_object* v___x_1745_; 
lean_dec_ref_known(v_ctx_1744_, 1);
v___x_1745_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__1));
return v___x_1745_;
}
case 1:
{
lean_object* v_parentDecl_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1759_; 
v_parentDecl_1746_ = lean_ctor_get(v_ctx_1744_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_ctx_1744_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1748_ = v_ctx_1744_;
v_isShared_1749_ = v_isSharedCheck_1759_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_parentDecl_1746_);
lean_dec(v_ctx_1744_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1759_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1750_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__2));
v___x_1751_ = 1;
v___x_1752_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_parentDecl_1746_, v___x_1751_);
v___x_1753_ = lean_string_append(v___x_1750_, v___x_1752_);
lean_dec_ref(v___x_1752_);
v___x_1754_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1755_ = lean_string_append(v___x_1753_, v___x_1754_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set_tag(v___x_1748_, 3);
lean_ctor_set(v___x_1748_, 0, v___x_1755_);
v___x_1757_ = v___x_1748_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
default: 
{
lean_object* v_autoImplicits_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1775_; 
v_autoImplicits_1760_ = lean_ctor_get(v_ctx_1744_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_ctx_1744_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1762_ = v_ctx_1744_;
v_isShared_1763_ = v_isSharedCheck_1775_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_autoImplicits_1760_);
lean_dec(v_ctx_1744_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1775_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1764_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__3));
v___x_1765_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__4));
v___x_1766_ = lean_array_to_list(v_autoImplicits_1760_);
v___x_1767_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v___x_1766_);
lean_dec(v___x_1766_);
v___x_1768_ = lean_string_append(v___x_1765_, v___x_1767_);
lean_dec_ref(v___x_1767_);
v___x_1769_ = lean_string_append(v___x_1764_, v___x_1768_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1771_ = lean_string_append(v___x_1769_, v___x_1770_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set_tag(v___x_1762_, 3);
lean_ctor_set(v___x_1762_, 0, v___x_1771_);
v___x_1773_ = v___x_1762_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format(lean_object* v_tree_1785_, lean_object* v_ctx_x3f_1786_){
_start:
{
switch(lean_obj_tag(v_tree_1785_))
{
case 0:
{
lean_object* v_i_1788_; lean_object* v_t_1789_; lean_object* v___x_1790_; 
v_i_1788_ = lean_ctor_get(v_tree_1785_, 0);
lean_inc_ref(v_i_1788_);
v_t_1789_ = lean_ctor_get(v_tree_1785_, 1);
lean_inc_ref(v_t_1789_);
lean_dec_ref_known(v_tree_1785_, 2);
v___x_1790_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1788_, v_ctx_x3f_1786_);
v_tree_1785_ = v_t_1789_;
v_ctx_x3f_1786_ = v___x_1790_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_ctx_x3f_1786_) == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_dec_ref_known(v_tree_1785_, 2);
v___x_1792_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__1));
v___x_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
return v___x_1793_;
}
else
{
lean_object* v_i_1794_; lean_object* v_children_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1845_; 
v_i_1794_ = lean_ctor_get(v_tree_1785_, 0);
v_children_1795_ = lean_ctor_get(v_tree_1785_, 1);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_tree_1785_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1797_ = v_tree_1785_;
v_isShared_1798_ = v_isSharedCheck_1845_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_children_1795_);
lean_inc(v_i_1794_);
lean_dec(v_tree_1785_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1845_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v_val_1799_; lean_object* v___x_1800_; 
v_val_1799_ = lean_ctor_get(v_ctx_x3f_1786_, 0);
lean_inc_ref(v_i_1794_);
lean_inc(v_val_1799_);
v___x_1800_ = l_Lean_Elab_Info_format(v_val_1799_, v_i_1794_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1844_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1844_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1844_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v_size_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v_size_1805_ = lean_ctor_get(v_children_1795_, 2);
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = lean_nat_dec_eq(v_size_1805_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_del_object(v___x_1803_);
v___x_1808_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_1786_, v_i_1794_);
lean_dec_ref(v_i_1794_);
v___x_1809_ = l_Lean_PersistentArray_toList___redArg(v_children_1795_);
lean_dec_ref(v_children_1795_);
v___x_1810_ = lean_box(0);
v___x_1811_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1808_, v___x_1809_, v___x_1810_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1827_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1827_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1827_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1816_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1798_ == 0)
{
lean_ctor_set_tag(v___x_1797_, 5);
lean_ctor_set(v___x_1797_, 1, v_a_1801_);
lean_ctor_set(v___x_1797_, 0, v___x_1816_);
v___x_1818_ = v___x_1797_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_a_1801_);
v___x_1818_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1819_ = lean_box(1);
v___x_1820_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1819_, v_a_1812_);
v___x_1821_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1818_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = l_Std_Format_nestD(v___x_1821_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v___x_1822_);
v___x_1824_ = v___x_1814_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
lean_dec(v_a_1801_);
lean_del_object(v___x_1797_);
v_a_1828_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1811_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1811_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
else
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
lean_dec_ref(v_children_1795_);
lean_dec_ref(v_i_1794_);
lean_dec_ref_known(v_ctx_x3f_1786_, 1);
v___x_1836_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1798_ == 0)
{
lean_ctor_set_tag(v___x_1797_, 5);
lean_ctor_set(v___x_1797_, 1, v_a_1801_);
lean_ctor_set(v___x_1797_, 0, v___x_1836_);
v___x_1838_ = v___x_1797_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_a_1801_);
v___x_1838_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1839_ = l_Std_Format_nestD(v___x_1838_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1839_);
v___x_1841_ = v___x_1803_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
}
else
{
lean_del_object(v___x_1797_);
lean_dec_ref(v_children_1795_);
lean_dec_ref(v_i_1794_);
lean_dec_ref_known(v_ctx_x3f_1786_, 1);
return v___x_1800_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v_ctx_x3f_1786_);
v_mvarId_1846_ = lean_ctor_get(v_tree_1785_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_tree_1785_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1848_ = v_tree_1785_;
v_isShared_1849_ = v_isSharedCheck_1859_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_mvarId_1846_);
lean_dec(v_tree_1785_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1859_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; uint8_t v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1850_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__5));
v___x_1851_ = 1;
v___x_1852_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_1846_, v___x_1851_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 3);
lean_ctor_set(v___x_1848_, 0, v___x_1852_);
v___x_1854_ = v___x_1848_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1850_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = l_Std_Format_nestD(v___x_1855_);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object* v___x_1860_, lean_object* v_x_1861_, lean_object* v_x_1862_){
_start:
{
if (lean_obj_tag(v_x_1861_) == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
lean_dec(v___x_1860_);
v___x_1864_ = l_List_reverse___redArg(v_x_1862_);
v___x_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
return v___x_1865_;
}
else
{
lean_object* v_head_1866_; lean_object* v_tail_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1885_; 
v_head_1866_ = lean_ctor_get(v_x_1861_, 0);
v_tail_1867_ = lean_ctor_get(v_x_1861_, 1);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_x_1861_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1869_ = v_x_1861_;
v_isShared_1870_ = v_isSharedCheck_1885_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_tail_1867_);
lean_inc(v_head_1866_);
lean_dec(v_x_1861_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1885_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; 
lean_inc(v___x_1860_);
v___x_1871_ = l_Lean_Elab_InfoTree_format(v_head_1866_, v___x_1860_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1871_, 1);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 1, v_x_1862_);
lean_ctor_set(v___x_1869_, 0, v_a_1872_);
v___x_1874_ = v___x_1869_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1872_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_x_1862_);
v___x_1874_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
v_x_1861_ = v_tail_1867_;
v_x_1862_ = v___x_1874_;
goto _start;
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_del_object(v___x_1869_);
lean_dec(v_tail_1867_);
lean_dec(v_x_1862_);
lean_dec(v___x_1860_);
v_a_1877_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1871_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1871_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
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
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object* v___x_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1886_, v_x_1887_, v_x_1888_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object* v_tree_1891_, lean_object* v_ctx_x3f_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_Elab_InfoTree_format(v_tree_1891_, v_ctx_x3f_1892_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object* v_f_1895_, lean_object* v_s_1896_){
_start:
{
uint8_t v_enabled_1897_; lean_object* v_assignment_1898_; lean_object* v_lazyAssignment_1899_; lean_object* v_trees_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1908_; 
v_enabled_1897_ = lean_ctor_get_uint8(v_s_1896_, sizeof(void*)*3);
v_assignment_1898_ = lean_ctor_get(v_s_1896_, 0);
v_lazyAssignment_1899_ = lean_ctor_get(v_s_1896_, 1);
v_trees_1900_ = lean_ctor_get(v_s_1896_, 2);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_s_1896_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1902_ = v_s_1896_;
v_isShared_1903_ = v_isSharedCheck_1908_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_trees_1900_);
lean_inc(v_lazyAssignment_1899_);
lean_inc(v_assignment_1898_);
lean_dec(v_s_1896_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1908_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1904_ = lean_apply_1(v_f_1895_, v_trees_1900_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 2, v___x_1904_);
v___x_1906_ = v___x_1902_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_assignment_1898_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_lazyAssignment_1899_);
lean_ctor_set(v_reuseFailAlloc_1907_, 2, v___x_1904_);
lean_ctor_set_uint8(v_reuseFailAlloc_1907_, sizeof(void*)*3, v_enabled_1897_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object* v_inst_1909_, lean_object* v_f_1910_){
_start:
{
lean_object* v_modifyInfoState_1911_; lean_object* v___f_1912_; lean_object* v___x_1913_; 
v_modifyInfoState_1911_ = lean_ctor_get(v_inst_1909_, 1);
lean_inc(v_modifyInfoState_1911_);
lean_dec_ref(v_inst_1909_);
v___f_1912_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1912_, 0, v_f_1910_);
v___x_1913_ = lean_apply_1(v_modifyInfoState_1911_, v___f_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object* v_m_1914_, lean_object* v_inst_1915_, lean_object* v_f_1916_){
_start:
{
lean_object* v_modifyInfoState_1917_; lean_object* v___f_1918_; lean_object* v___x_1919_; 
v_modifyInfoState_1917_ = lean_ctor_get(v_inst_1915_, 1);
lean_inc(v_modifyInfoState_1917_);
lean_dec_ref(v_inst_1915_);
v___f_1918_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1918_, 0, v_f_1916_);
v___x_1919_ = lean_apply_1(v_modifyInfoState_1917_, v___f_1918_);
return v___x_1919_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1920_ = lean_unsigned_to_nat(32u);
v___x_1921_ = lean_mk_empty_array_with_capacity(v___x_1920_);
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
return v___x_1922_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1923_ = ((size_t)5ULL);
v___x_1924_ = lean_unsigned_to_nat(0u);
v___x_1925_ = lean_unsigned_to_nat(32u);
v___x_1926_ = lean_mk_empty_array_with_capacity(v___x_1925_);
v___x_1927_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0);
v___x_1928_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
lean_ctor_set(v___x_1928_, 1, v___x_1926_);
lean_ctor_set(v___x_1928_, 2, v___x_1924_);
lean_ctor_set(v___x_1928_, 3, v___x_1924_);
lean_ctor_set_usize(v___x_1928_, 4, v___x_1923_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object* v_s_1929_){
_start:
{
uint8_t v_enabled_1930_; lean_object* v_assignment_1931_; lean_object* v_lazyAssignment_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1940_; 
v_enabled_1930_ = lean_ctor_get_uint8(v_s_1929_, sizeof(void*)*3);
v_assignment_1931_ = lean_ctor_get(v_s_1929_, 0);
v_lazyAssignment_1932_ = lean_ctor_get(v_s_1929_, 1);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_s_1929_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; 
v_unused_1941_ = lean_ctor_get(v_s_1929_, 2);
lean_dec(v_unused_1941_);
v___x_1934_ = v_s_1929_;
v_isShared_1935_ = v_isSharedCheck_1940_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_lazyAssignment_1932_);
lean_inc(v_assignment_1931_);
lean_dec(v_s_1929_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1940_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1936_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
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
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_assignment_1931_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_lazyAssignment_1932_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v___x_1936_);
lean_ctor_set_uint8(v_reuseFailAlloc_1939_, sizeof(void*)*3, v_enabled_1930_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object* v_toPure_1942_, lean_object* v_trees_1943_, lean_object* v_____r_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = lean_apply_2(v_toPure_1942_, lean_box(0), v_trees_1943_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object* v_toPure_1946_, lean_object* v_modifyInfoState_1947_, lean_object* v___f_1948_, lean_object* v_toBind_1949_, lean_object* v_____do__lift_1950_){
_start:
{
lean_object* v_trees_1951_; lean_object* v___f_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v_trees_1951_ = lean_ctor_get(v_____do__lift_1950_, 2);
lean_inc_ref(v_trees_1951_);
lean_dec_ref(v_____do__lift_1950_);
v___f_1952_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1952_, 0, v_toPure_1946_);
lean_closure_set(v___f_1952_, 1, v_trees_1951_);
v___x_1953_ = lean_apply_1(v_modifyInfoState_1947_, v___f_1948_);
v___x_1954_ = lean_apply_4(v_toBind_1949_, lean_box(0), lean_box(0), v___x_1953_, v___f_1952_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object* v_inst_1956_, lean_object* v_inst_1957_){
_start:
{
lean_object* v_toApplicative_1958_; lean_object* v_toBind_1959_; lean_object* v_getInfoState_1960_; lean_object* v_modifyInfoState_1961_; lean_object* v_toPure_1962_; lean_object* v___f_1963_; lean_object* v___f_1964_; lean_object* v___x_1965_; 
v_toApplicative_1958_ = lean_ctor_get(v_inst_1956_, 0);
lean_inc_ref(v_toApplicative_1958_);
v_toBind_1959_ = lean_ctor_get(v_inst_1956_, 1);
lean_inc_n(v_toBind_1959_, 2);
lean_dec_ref(v_inst_1956_);
v_getInfoState_1960_ = lean_ctor_get(v_inst_1957_, 0);
lean_inc(v_getInfoState_1960_);
v_modifyInfoState_1961_ = lean_ctor_get(v_inst_1957_, 1);
lean_inc(v_modifyInfoState_1961_);
lean_dec_ref(v_inst_1957_);
v_toPure_1962_ = lean_ctor_get(v_toApplicative_1958_, 1);
lean_inc(v_toPure_1962_);
lean_dec_ref(v_toApplicative_1958_);
v___f_1963_ = ((lean_object*)(l_Lean_Elab_getResetInfoTrees___redArg___closed__0));
v___f_1964_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1964_, 0, v_toPure_1962_);
lean_closure_set(v___f_1964_, 1, v_modifyInfoState_1961_);
lean_closure_set(v___f_1964_, 2, v___f_1963_);
lean_closure_set(v___f_1964_, 3, v_toBind_1959_);
v___x_1965_ = lean_apply_4(v_toBind_1959_, lean_box(0), lean_box(0), v_getInfoState_1960_, v___f_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object* v_m_1966_, lean_object* v_inst_1967_, lean_object* v_inst_1968_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_1967_, v_inst_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object* v_t_1970_, lean_object* v_s_1971_){
_start:
{
uint8_t v_enabled_1972_; lean_object* v_assignment_1973_; lean_object* v_lazyAssignment_1974_; lean_object* v_trees_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1983_; 
v_enabled_1972_ = lean_ctor_get_uint8(v_s_1971_, sizeof(void*)*3);
v_assignment_1973_ = lean_ctor_get(v_s_1971_, 0);
v_lazyAssignment_1974_ = lean_ctor_get(v_s_1971_, 1);
v_trees_1975_ = lean_ctor_get(v_s_1971_, 2);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_s_1971_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1977_ = v_s_1971_;
v_isShared_1978_ = v_isSharedCheck_1983_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_trees_1975_);
lean_inc(v_lazyAssignment_1974_);
lean_inc(v_assignment_1973_);
lean_dec(v_s_1971_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1983_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1979_ = l_Lean_PersistentArray_push___redArg(v_trees_1975_, v_t_1970_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 2, v___x_1979_);
v___x_1981_ = v___x_1977_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_assignment_1973_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_lazyAssignment_1974_);
lean_ctor_set(v_reuseFailAlloc_1982_, 2, v___x_1979_);
lean_ctor_set_uint8(v_reuseFailAlloc_1982_, sizeof(void*)*3, v_enabled_1972_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object* v_toPure_1984_, lean_object* v_modifyInfoState_1985_, lean_object* v___f_1986_, lean_object* v_____do__lift_1987_){
_start:
{
uint8_t v_enabled_1988_; 
v_enabled_1988_ = lean_ctor_get_uint8(v_____do__lift_1987_, sizeof(void*)*3);
if (v_enabled_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
lean_dec_ref(v___f_1986_);
lean_dec(v_modifyInfoState_1985_);
v___x_1989_ = lean_box(0);
v___x_1990_ = lean_apply_2(v_toPure_1984_, lean_box(0), v___x_1989_);
return v___x_1990_;
}
else
{
lean_object* v___x_1991_; 
lean_dec(v_toPure_1984_);
v___x_1991_ = lean_apply_1(v_modifyInfoState_1985_, v___f_1986_);
return v___x_1991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object* v_toPure_1992_, lean_object* v_modifyInfoState_1993_, lean_object* v___f_1994_, lean_object* v_____do__lift_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_Elab_pushInfoTree___redArg___lam__1(v_toPure_1992_, v_modifyInfoState_1993_, v___f_1994_, v_____do__lift_1995_);
lean_dec_ref(v_____do__lift_1995_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object* v_inst_1997_, lean_object* v_inst_1998_, lean_object* v_t_1999_){
_start:
{
lean_object* v_toApplicative_2000_; lean_object* v_toBind_2001_; lean_object* v_getInfoState_2002_; lean_object* v_modifyInfoState_2003_; lean_object* v_toPure_2004_; lean_object* v___f_2005_; lean_object* v___f_2006_; lean_object* v___x_2007_; 
v_toApplicative_2000_ = lean_ctor_get(v_inst_1997_, 0);
lean_inc_ref(v_toApplicative_2000_);
v_toBind_2001_ = lean_ctor_get(v_inst_1997_, 1);
lean_inc(v_toBind_2001_);
lean_dec_ref(v_inst_1997_);
v_getInfoState_2002_ = lean_ctor_get(v_inst_1998_, 0);
lean_inc(v_getInfoState_2002_);
v_modifyInfoState_2003_ = lean_ctor_get(v_inst_1998_, 1);
lean_inc(v_modifyInfoState_2003_);
lean_dec_ref(v_inst_1998_);
v_toPure_2004_ = lean_ctor_get(v_toApplicative_2000_, 1);
lean_inc(v_toPure_2004_);
lean_dec_ref(v_toApplicative_2000_);
v___f_2005_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2005_, 0, v_t_1999_);
v___f_2006_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2006_, 0, v_toPure_2004_);
lean_closure_set(v___f_2006_, 1, v_modifyInfoState_2003_);
lean_closure_set(v___f_2006_, 2, v___f_2005_);
v___x_2007_ = lean_apply_4(v_toBind_2001_, lean_box(0), lean_box(0), v_getInfoState_2002_, v___f_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object* v_m_2008_, lean_object* v_inst_2009_, lean_object* v_inst_2010_, lean_object* v_t_2011_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2009_, v_inst_2010_, v_t_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object* v_toPure_2013_, lean_object* v_t_2014_, lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v_____do__lift_2017_){
_start:
{
uint8_t v_enabled_2018_; 
v_enabled_2018_ = lean_ctor_get_uint8(v_____do__lift_2017_, sizeof(void*)*3);
if (v_enabled_2018_ == 0)
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
lean_dec_ref(v_inst_2016_);
lean_dec_ref(v_inst_2015_);
lean_dec_ref(v_t_2014_);
v___x_2019_ = lean_box(0);
v___x_2020_ = lean_apply_2(v_toPure_2013_, lean_box(0), v___x_2019_);
return v___x_2020_;
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
lean_dec(v_toPure_2013_);
v___x_2021_ = lean_unsigned_to_nat(32u);
v___x_2022_ = lean_mk_empty_array_with_capacity(v___x_2021_);
lean_dec_ref(v___x_2022_);
v___x_2023_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2024_, 0, v_t_2014_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
v___x_2025_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2015_, v_inst_2016_, v___x_2024_);
return v___x_2025_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object* v_toPure_2026_, lean_object* v_t_2027_, lean_object* v_inst_2028_, lean_object* v_inst_2029_, lean_object* v_____do__lift_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lean_Elab_pushInfoLeaf___redArg___lam__0(v_toPure_2026_, v_t_2027_, v_inst_2028_, v_inst_2029_, v_____do__lift_2030_);
lean_dec_ref(v_____do__lift_2030_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object* v_inst_2032_, lean_object* v_inst_2033_, lean_object* v_t_2034_){
_start:
{
lean_object* v_toApplicative_2035_; lean_object* v_toBind_2036_; lean_object* v_getInfoState_2037_; lean_object* v_toPure_2038_; lean_object* v___f_2039_; lean_object* v___x_2040_; 
v_toApplicative_2035_ = lean_ctor_get(v_inst_2032_, 0);
v_toBind_2036_ = lean_ctor_get(v_inst_2032_, 1);
lean_inc(v_toBind_2036_);
v_getInfoState_2037_ = lean_ctor_get(v_inst_2033_, 0);
lean_inc(v_getInfoState_2037_);
v_toPure_2038_ = lean_ctor_get(v_toApplicative_2035_, 1);
lean_inc(v_toPure_2038_);
v___f_2039_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2039_, 0, v_toPure_2038_);
lean_closure_set(v___f_2039_, 1, v_t_2034_);
lean_closure_set(v___f_2039_, 2, v_inst_2032_);
lean_closure_set(v___f_2039_, 3, v_inst_2033_);
v___x_2040_ = lean_apply_4(v_toBind_2036_, lean_box(0), lean_box(0), v_getInfoState_2037_, v___f_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object* v_m_2041_, lean_object* v_inst_2042_, lean_object* v_inst_2043_, lean_object* v_t_2044_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2042_, v_inst_2043_, v_t_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object* v_inst_2046_, lean_object* v_inst_2047_, lean_object* v_info_2048_){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2049_, 0, v_info_2048_);
v___x_2050_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2046_, v_inst_2047_, v___x_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object* v_m_2051_, lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_info_2054_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_2052_, v_inst_2053_, v_info_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object* v_stx_2056_, lean_object* v_expectedType_x3f_2057_, lean_object* v_inst_2058_, lean_object* v_inst_2059_, lean_object* v_____do__lift_2060_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2061_ = lean_box(0);
v___x_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
lean_ctor_set(v___x_2062_, 1, v_stx_2056_);
v___x_2063_ = l_Lean_LocalContext_empty;
v___x_2064_ = 0;
v___x_2065_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2065_, 0, v___x_2062_);
lean_ctor_set(v___x_2065_, 1, v___x_2063_);
lean_ctor_set(v___x_2065_, 2, v_expectedType_x3f_2057_);
lean_ctor_set(v___x_2065_, 3, v_____do__lift_2060_);
lean_ctor_set_uint8(v___x_2065_, sizeof(void*)*4, v___x_2064_);
lean_ctor_set_uint8(v___x_2065_, sizeof(void*)*4 + 1, v___x_2064_);
v___x_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
v___x_2067_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2058_, v_inst_2059_, v___x_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object* v_inst_2068_, lean_object* v_inst_2069_, lean_object* v_inst_2070_, lean_object* v_inst_2071_, lean_object* v_stx_2072_, lean_object* v_n_2073_, lean_object* v_expectedType_x3f_2074_){
_start:
{
lean_object* v_toBind_2075_; lean_object* v___f_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v_toBind_2075_ = lean_ctor_get(v_inst_2068_, 1);
lean_inc(v_toBind_2075_);
lean_inc_ref(v_inst_2068_);
v___f_2076_ = lean_alloc_closure((void*)(l_Lean_Elab_addConstInfo___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2076_, 0, v_stx_2072_);
lean_closure_set(v___f_2076_, 1, v_expectedType_x3f_2074_);
lean_closure_set(v___f_2076_, 2, v_inst_2068_);
lean_closure_set(v___f_2076_, 3, v_inst_2069_);
v___x_2077_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_2068_, v_inst_2070_, v_inst_2071_, v_n_2073_);
v___x_2078_ = lean_apply_4(v_toBind_2075_, lean_box(0), lean_box(0), v___x_2077_, v___f_2076_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object* v_m_2079_, lean_object* v_inst_2080_, lean_object* v_inst_2081_, lean_object* v_inst_2082_, lean_object* v_inst_2083_, lean_object* v_stx_2084_, lean_object* v_n_2085_, lean_object* v_expectedType_x3f_2086_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_Elab_addConstInfo___redArg(v_inst_2080_, v_inst_2081_, v_inst_2082_, v_inst_2083_, v_stx_2084_, v_n_2085_, v_expectedType_x3f_2086_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v___x_2091_; lean_object* v_infoState_2092_; uint8_t v_enabled_2093_; 
v___x_2091_ = lean_st_ref_get(v___y_2089_);
v_infoState_2092_ = lean_ctor_get(v___x_2091_, 7);
lean_inc_ref(v_infoState_2092_);
lean_dec(v___x_2091_);
v_enabled_2093_ = lean_ctor_get_uint8(v_infoState_2092_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2092_);
if (v_enabled_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
lean_dec_ref(v_t_2088_);
v___x_2094_ = lean_box(0);
v___x_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
return v___x_2095_;
}
else
{
lean_object* v___x_2096_; lean_object* v_infoState_2097_; lean_object* v_env_2098_; lean_object* v_nextMacroScope_2099_; lean_object* v_ngen_2100_; lean_object* v_auxDeclNGen_2101_; lean_object* v_traceState_2102_; lean_object* v_cache_2103_; lean_object* v_messages_2104_; lean_object* v_snapshotTasks_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2127_; 
v___x_2096_ = lean_st_ref_take(v___y_2089_);
v_infoState_2097_ = lean_ctor_get(v___x_2096_, 7);
v_env_2098_ = lean_ctor_get(v___x_2096_, 0);
v_nextMacroScope_2099_ = lean_ctor_get(v___x_2096_, 1);
v_ngen_2100_ = lean_ctor_get(v___x_2096_, 2);
v_auxDeclNGen_2101_ = lean_ctor_get(v___x_2096_, 3);
v_traceState_2102_ = lean_ctor_get(v___x_2096_, 4);
v_cache_2103_ = lean_ctor_get(v___x_2096_, 5);
v_messages_2104_ = lean_ctor_get(v___x_2096_, 6);
v_snapshotTasks_2105_ = lean_ctor_get(v___x_2096_, 8);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2107_ = v___x_2096_;
v_isShared_2108_ = v_isSharedCheck_2127_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_snapshotTasks_2105_);
lean_inc(v_infoState_2097_);
lean_inc(v_messages_2104_);
lean_inc(v_cache_2103_);
lean_inc(v_traceState_2102_);
lean_inc(v_auxDeclNGen_2101_);
lean_inc(v_ngen_2100_);
lean_inc(v_nextMacroScope_2099_);
lean_inc(v_env_2098_);
lean_dec(v___x_2096_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2127_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
uint8_t v_enabled_2109_; lean_object* v_assignment_2110_; lean_object* v_lazyAssignment_2111_; lean_object* v_trees_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2126_; 
v_enabled_2109_ = lean_ctor_get_uint8(v_infoState_2097_, sizeof(void*)*3);
v_assignment_2110_ = lean_ctor_get(v_infoState_2097_, 0);
v_lazyAssignment_2111_ = lean_ctor_get(v_infoState_2097_, 1);
v_trees_2112_ = lean_ctor_get(v_infoState_2097_, 2);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_infoState_2097_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2114_ = v_infoState_2097_;
v_isShared_2115_ = v_isSharedCheck_2126_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_trees_2112_);
lean_inc(v_lazyAssignment_2111_);
lean_inc(v_assignment_2110_);
lean_dec(v_infoState_2097_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2126_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2116_; lean_object* v___x_2118_; 
v___x_2116_ = l_Lean_PersistentArray_push___redArg(v_trees_2112_, v_t_2088_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 2, v___x_2116_);
v___x_2118_ = v___x_2114_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_assignment_2110_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_lazyAssignment_2111_);
lean_ctor_set(v_reuseFailAlloc_2125_, 2, v___x_2116_);
lean_ctor_set_uint8(v_reuseFailAlloc_2125_, sizeof(void*)*3, v_enabled_2109_);
v___x_2118_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2120_; 
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 7, v___x_2118_);
v___x_2120_ = v___x_2107_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_env_2098_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_nextMacroScope_2099_);
lean_ctor_set(v_reuseFailAlloc_2124_, 2, v_ngen_2100_);
lean_ctor_set(v_reuseFailAlloc_2124_, 3, v_auxDeclNGen_2101_);
lean_ctor_set(v_reuseFailAlloc_2124_, 4, v_traceState_2102_);
lean_ctor_set(v_reuseFailAlloc_2124_, 5, v_cache_2103_);
lean_ctor_set(v_reuseFailAlloc_2124_, 6, v_messages_2104_);
lean_ctor_set(v_reuseFailAlloc_2124_, 7, v___x_2118_);
lean_ctor_set(v_reuseFailAlloc_2124_, 8, v_snapshotTasks_2105_);
v___x_2120_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2121_ = lean_st_ref_put(v___y_2089_, v___x_2120_);
v___x_2122_ = lean_box(0);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
return v___x_2123_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2128_, v___y_2129_);
lean_dec(v___y_2129_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object* v_t_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v___x_2136_; lean_object* v_infoState_2137_; uint8_t v_enabled_2138_; 
v___x_2136_ = lean_st_ref_get(v___y_2134_);
v_infoState_2137_ = lean_ctor_get(v___x_2136_, 7);
lean_inc_ref(v_infoState_2137_);
lean_dec(v___x_2136_);
v_enabled_2138_ = lean_ctor_get_uint8(v_infoState_2137_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2137_);
if (v_enabled_2138_ == 0)
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
lean_dec_ref(v_t_2132_);
v___x_2139_ = lean_box(0);
v___x_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
return v___x_2140_;
}
else
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2141_ = lean_unsigned_to_nat(32u);
v___x_2142_ = lean_mk_empty_array_with_capacity(v___x_2141_);
lean_dec_ref(v___x_2142_);
v___x_2143_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2144_, 0, v_t_2132_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
v___x_2145_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v___x_2144_, v___y_2134_);
return v___x_2145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object* v_t_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
return v_res_2150_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2151_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2152_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
return v___x_2153_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2154_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2155_ = lean_unsigned_to_nat(0u);
v___x_2156_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
lean_ctor_set(v___x_2156_, 2, v___x_2155_);
lean_ctor_set(v___x_2156_, 3, v___x_2155_);
lean_ctor_set(v___x_2156_, 4, v___x_2154_);
lean_ctor_set(v___x_2156_, 5, v___x_2154_);
lean_ctor_set(v___x_2156_, 6, v___x_2154_);
lean_ctor_set(v___x_2156_, 7, v___x_2154_);
lean_ctor_set(v___x_2156_, 8, v___x_2154_);
lean_ctor_set(v___x_2156_, 9, v___x_2154_);
lean_ctor_set(v___x_2156_, 10, v___x_2154_);
return v___x_2156_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2157_ = lean_box(1);
v___x_2158_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_2159_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
lean_ctor_set(v___x_2160_, 1, v___x_2158_);
lean_ctor_set(v___x_2160_, 2, v___x_2157_);
return v___x_2160_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_2163_ = l_Lean_stringToMessageData(v___x_2162_);
return v___x_2163_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_2166_ = l_Lean_stringToMessageData(v___x_2165_);
return v___x_2166_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2168_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_2169_ = l_Lean_stringToMessageData(v___x_2168_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_2172_ = l_Lean_stringToMessageData(v___x_2171_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_2175_ = l_Lean_stringToMessageData(v___x_2174_);
return v___x_2175_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_2178_ = l_Lean_stringToMessageData(v___x_2177_);
return v___x_2178_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_2181_ = l_Lean_stringToMessageData(v___x_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_2182_, lean_object* v_declHint_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v___x_2186_; lean_object* v_env_2187_; uint8_t v___x_2188_; 
v___x_2186_ = lean_st_ref_get(v___y_2184_);
v_env_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc_ref(v_env_2187_);
lean_dec(v___x_2186_);
v___x_2188_ = l_Lean_Name_isAnonymous(v_declHint_2183_);
if (v___x_2188_ == 0)
{
uint8_t v_isExporting_2189_; 
v_isExporting_2189_ = lean_ctor_get_uint8(v_env_2187_, sizeof(void*)*8);
if (v_isExporting_2189_ == 0)
{
lean_object* v___x_2190_; 
lean_dec_ref(v_env_2187_);
lean_dec(v_declHint_2183_);
v___x_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2190_, 0, v_msg_2182_);
return v___x_2190_;
}
else
{
lean_object* v___x_2191_; uint8_t v___x_2192_; 
lean_inc_ref(v_env_2187_);
v___x_2191_ = l_Lean_Environment_setExporting(v_env_2187_, v___x_2188_);
lean_inc(v_declHint_2183_);
lean_inc_ref(v___x_2191_);
v___x_2192_ = l_Lean_Environment_contains(v___x_2191_, v_declHint_2183_, v_isExporting_2189_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; 
lean_dec_ref(v___x_2191_);
lean_dec_ref(v_env_2187_);
lean_dec(v_declHint_2183_);
v___x_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2193_, 0, v_msg_2182_);
return v___x_2193_;
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v_c_2199_; lean_object* v___x_2200_; 
v___x_2194_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_2195_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_2196_ = l_Lean_Options_empty;
v___x_2197_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2191_);
lean_ctor_set(v___x_2197_, 1, v___x_2194_);
lean_ctor_set(v___x_2197_, 2, v___x_2195_);
lean_ctor_set(v___x_2197_, 3, v___x_2196_);
lean_inc(v_declHint_2183_);
v___x_2198_ = l_Lean_MessageData_ofConstName(v_declHint_2183_, v___x_2188_);
v_c_2199_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2199_, 0, v___x_2197_);
lean_ctor_set(v_c_2199_, 1, v___x_2198_);
v___x_2200_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2187_, v_declHint_2183_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_dec_ref(v_env_2187_);
lean_dec(v_declHint_2183_);
v___x_2201_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_2202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v_c_2199_);
v___x_2203_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_2204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = l_Lean_MessageData_note(v___x_2204_);
v___x_2206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2206_, 0, v_msg_2182_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
v___x_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
return v___x_2207_;
}
else
{
lean_object* v_val_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2243_; 
v_val_2208_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2210_ = v___x_2200_;
v_isShared_2211_ = v_isSharedCheck_2243_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_val_2208_);
lean_dec(v___x_2200_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2243_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v_mod_2215_; uint8_t v___x_2216_; 
v___x_2212_ = lean_box(0);
v___x_2213_ = l_Lean_Environment_header(v_env_2187_);
lean_dec_ref(v_env_2187_);
v___x_2214_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2213_);
v_mod_2215_ = lean_array_get(v___x_2212_, v___x_2214_, v_val_2208_);
lean_dec(v_val_2208_);
lean_dec_ref(v___x_2214_);
v___x_2216_ = l_Lean_isPrivateName(v_declHint_2183_);
lean_dec(v_declHint_2183_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2217_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_2218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
lean_ctor_set(v___x_2218_, 1, v_c_2199_);
v___x_2219_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_2220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2218_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v___x_2221_ = l_Lean_MessageData_ofName(v_mod_2215_);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2220_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_2224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2222_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
v___x_2225_ = l_Lean_MessageData_note(v___x_2224_);
v___x_2226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2226_, 0, v_msg_2182_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set_tag(v___x_2210_, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2226_);
v___x_2228_ = v___x_2210_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2241_; 
v___x_2230_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_2231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
lean_ctor_set(v___x_2231_, 1, v_c_2199_);
v___x_2232_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_2233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2231_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
v___x_2234_ = l_Lean_MessageData_ofName(v_mod_2215_);
v___x_2235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2233_);
lean_ctor_set(v___x_2235_, 1, v___x_2234_);
v___x_2236_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_2237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2235_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = l_Lean_MessageData_note(v___x_2237_);
v___x_2239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2239_, 0, v_msg_2182_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set_tag(v___x_2210_, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2239_);
v___x_2241_ = v___x_2210_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2244_; 
lean_dec_ref(v_env_2187_);
lean_dec(v_declHint_2183_);
v___x_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2244_, 0, v_msg_2182_);
return v___x_2244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_2245_, lean_object* v_declHint_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2245_, v_declHint_2246_, v___y_2247_);
lean_dec(v___y_2247_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_2250_, lean_object* v_declHint_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2255_; lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2265_; 
v___x_2255_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2250_, v_declHint_2251_, v___y_2253_);
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2265_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2265_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2263_; 
v___x_2260_ = l_Lean_unknownIdentifierMessageTag;
v___x_2261_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
lean_ctor_set(v___x_2261_, 1, v_a_2256_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v___x_2261_);
v___x_2263_ = v___x_2258_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_2266_, lean_object* v_declHint_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2266_, v_declHint_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object* v_msgData_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v___x_2276_; lean_object* v_toCold_2277_; lean_object* v_env_2278_; lean_object* v_options_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2276_ = lean_st_ref_get(v___y_2274_);
v_toCold_2277_ = lean_ctor_get(v___y_2273_, 0);
v_env_2278_ = lean_ctor_get(v___x_2276_, 0);
lean_inc_ref(v_env_2278_);
lean_dec(v___x_2276_);
v_options_2279_ = lean_ctor_get(v_toCold_2277_, 2);
v___x_2280_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_2281_ = lean_unsigned_to_nat(32u);
v___x_2282_ = lean_mk_empty_array_with_capacity(v___x_2281_);
lean_dec_ref(v___x_2282_);
v___x_2283_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
lean_inc_ref(v_options_2279_);
v___x_2284_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2284_, 0, v_env_2278_);
lean_ctor_set(v___x_2284_, 1, v___x_2280_);
lean_ctor_set(v___x_2284_, 2, v___x_2283_);
lean_ctor_set(v___x_2284_, 3, v_options_2279_);
v___x_2285_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
lean_ctor_set(v___x_2285_, 1, v_msgData_2272_);
v___x_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object* v_msgData_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_2287_, v___y_2288_, v___y_2289_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v_ref_2296_; lean_object* v___x_2297_; lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2306_; 
v_ref_2296_ = lean_ctor_get(v___y_2293_, 2);
v___x_2297_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_2292_, v___y_2293_, v___y_2294_);
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2300_ = v___x_2297_;
v_isShared_2301_ = v_isSharedCheck_2306_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2297_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2306_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; lean_object* v___x_2304_; 
lean_inc(v_ref_2296_);
v___x_2302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2302_, 0, v_ref_2296_);
lean_ctor_set(v___x_2302_, 1, v_a_2298_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set_tag(v___x_2300_, 1);
lean_ctor_set(v___x_2300_, 0, v___x_2302_);
v___x_2304_ = v___x_2300_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_2312_, lean_object* v_msg_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v_toCold_2317_; lean_object* v_currRecDepth_2318_; lean_object* v_ref_2319_; uint8_t v_diag_2320_; uint8_t v_suppressElabErrors_2321_; lean_object* v_ref_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v_toCold_2317_ = lean_ctor_get(v___y_2314_, 0);
v_currRecDepth_2318_ = lean_ctor_get(v___y_2314_, 1);
v_ref_2319_ = lean_ctor_get(v___y_2314_, 2);
v_diag_2320_ = lean_ctor_get_uint8(v___y_2314_, sizeof(void*)*3);
v_suppressElabErrors_2321_ = lean_ctor_get_uint8(v___y_2314_, sizeof(void*)*3 + 1);
v_ref_2322_ = l_Lean_replaceRef(v_ref_2312_, v_ref_2319_);
lean_inc(v_currRecDepth_2318_);
lean_inc_ref(v_toCold_2317_);
v___x_2323_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2323_, 0, v_toCold_2317_);
lean_ctor_set(v___x_2323_, 1, v_currRecDepth_2318_);
lean_ctor_set(v___x_2323_, 2, v_ref_2322_);
lean_ctor_set_uint8(v___x_2323_, sizeof(void*)*3, v_diag_2320_);
lean_ctor_set_uint8(v___x_2323_, sizeof(void*)*3 + 1, v_suppressElabErrors_2321_);
v___x_2324_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2313_, v___x_2323_, v___y_2315_);
lean_dec_ref_known(v___x_2323_, 3);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_2325_, lean_object* v_msg_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2325_, v_msg_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v_ref_2325_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_2331_, lean_object* v_msg_2332_, lean_object* v_declHint_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v___x_2337_; lean_object* v_a_2338_; lean_object* v___x_2339_; 
v___x_2337_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2332_, v_declHint_2333_, v___y_2334_, v___y_2335_);
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref(v___x_2337_);
v___x_2339_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2331_, v_a_2338_, v___y_2334_, v___y_2335_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2340_, lean_object* v_msg_2341_, lean_object* v_declHint_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2340_, v_msg_2341_, v_declHint_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v_ref_2340_);
return v_res_2346_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_2349_ = l_Lean_stringToMessageData(v___x_2348_);
return v___x_2349_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2));
v___x_2352_ = l_Lean_stringToMessageData(v___x_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_2353_, lean_object* v_constName_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2358_; uint8_t v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2358_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_2359_ = 0;
lean_inc(v_constName_2354_);
v___x_2360_ = l_Lean_MessageData_ofConstName(v_constName_2354_, v___x_2359_);
v___x_2361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2358_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v___x_2362_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_2363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2361_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
v___x_2364_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2353_, v___x_2363_, v_constName_2354_, v___y_2355_, v___y_2356_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2365_, lean_object* v_constName_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2365_, v_constName_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v_ref_2365_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v_ref_2375_; lean_object* v___x_2376_; 
v_ref_2375_ = lean_ctor_get(v___y_2372_, 2);
v___x_2376_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2375_, v_constName_2371_, v___y_2372_, v___y_2373_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object* v_constName_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v___x_2386_; lean_object* v_env_2387_; uint8_t v___x_2388_; lean_object* v___x_2389_; 
v___x_2386_ = lean_st_ref_get(v___y_2384_);
v_env_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc_ref(v_env_2387_);
lean_dec(v___x_2386_);
v___x_2388_ = 0;
lean_inc(v_constName_2382_);
v___x_2389_ = l_Lean_Environment_findConstVal_x3f(v_env_2387_, v_constName_2382_, v___x_2388_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v___x_2390_; 
v___x_2390_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2382_, v___y_2383_, v___y_2384_);
return v___x_2390_;
}
else
{
lean_object* v_val_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_dec(v_constName_2382_);
v_val_2391_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2389_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_val_2391_);
lean_dec(v___x_2389_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set_tag(v___x_2393_, 0);
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_val_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
if (lean_obj_tag(v_a_2404_) == 0)
{
lean_object* v___x_2406_; 
v___x_2406_ = l_List_reverse___redArg(v_a_2405_);
return v___x_2406_;
}
else
{
lean_object* v_head_2407_; lean_object* v_tail_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2417_; 
v_head_2407_ = lean_ctor_get(v_a_2404_, 0);
v_tail_2408_ = lean_ctor_get(v_a_2404_, 1);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_a_2404_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2410_ = v_a_2404_;
v_isShared_2411_ = v_isSharedCheck_2417_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_tail_2408_);
lean_inc(v_head_2407_);
lean_dec(v_a_2404_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2417_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2412_ = l_Lean_mkLevelParam(v_head_2407_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 1, v_a_2405_);
lean_ctor_set(v___x_2410_, 0, v___x_2412_);
v___x_2414_ = v___x_2410_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v_a_2405_);
v___x_2414_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
v_a_2404_ = v_tail_2408_;
v_a_2405_ = v___x_2414_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object* v_constName_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v___x_2422_; 
lean_inc(v_constName_2418_);
v___x_2422_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2418_, v___y_2419_, v___y_2420_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2434_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2425_ = v___x_2422_;
v_isShared_2426_ = v_isSharedCheck_2434_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2422_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2434_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v_levelParams_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2432_; 
v_levelParams_2427_ = lean_ctor_get(v_a_2423_, 1);
lean_inc(v_levelParams_2427_);
lean_dec(v_a_2423_);
v___x_2428_ = lean_box(0);
v___x_2429_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_2427_, v___x_2428_);
v___x_2430_ = l_Lean_mkConst(v_constName_2418_, v___x_2429_);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v___x_2430_);
v___x_2432_ = v___x_2425_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_dec(v_constName_2418_);
v_a_2435_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2422_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2422_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object* v_constName_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_2443_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object* v_stx_2448_, lean_object* v_n_2449_, lean_object* v_expectedType_x3f_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_2449_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___x_2454_, 1);
v___x_2456_ = lean_box(0);
v___x_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
lean_ctor_set(v___x_2457_, 1, v_stx_2448_);
v___x_2458_ = l_Lean_LocalContext_empty;
v___x_2459_ = 0;
v___x_2460_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2460_, 0, v___x_2457_);
lean_ctor_set(v___x_2460_, 1, v___x_2458_);
lean_ctor_set(v___x_2460_, 2, v_expectedType_x3f_2450_);
lean_ctor_set(v___x_2460_, 3, v_a_2455_);
lean_ctor_set_uint8(v___x_2460_, sizeof(void*)*4, v___x_2459_);
lean_ctor_set_uint8(v___x_2460_, sizeof(void*)*4 + 1, v___x_2459_);
v___x_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
v___x_2462_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_2461_, v___y_2451_, v___y_2452_);
return v___x_2462_;
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec(v_expectedType_x3f_2450_);
lean_dec(v_stx_2448_);
v_a_2463_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2454_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2454_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object* v_stx_2471_, lean_object* v_n_2472_, lean_object* v_expectedType_x3f_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_2471_, v_n_2472_, v_expectedType_x3f_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object* v_id_2478_, lean_object* v_expectedType_x3f_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_){
_start:
{
lean_object* v___x_2483_; 
lean_inc(v_id_2478_);
v___x_2483_ = l_Lean_realizeGlobalConstNoOverload(v_id_2478_, v_a_2480_, v_a_2481_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2511_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2511_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2511_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2488_; lean_object* v_infoState_2489_; uint8_t v_enabled_2490_; 
v___x_2488_ = lean_st_ref_get(v_a_2481_);
v_infoState_2489_ = lean_ctor_get(v___x_2488_, 7);
lean_inc_ref(v_infoState_2489_);
lean_dec(v___x_2488_);
v_enabled_2490_ = lean_ctor_get_uint8(v_infoState_2489_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2489_);
if (v_enabled_2490_ == 0)
{
lean_object* v___x_2492_; 
lean_dec(v_expectedType_x3f_2479_);
lean_dec(v_id_2478_);
if (v_isShared_2487_ == 0)
{
v___x_2492_ = v___x_2486_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2484_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
else
{
lean_object* v___x_2494_; 
lean_del_object(v___x_2486_);
lean_inc(v_a_2484_);
v___x_2494_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2478_, v_a_2484_, v_expectedType_x3f_2479_, v_a_2480_, v_a_2481_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2501_ == 0)
{
lean_object* v_unused_2502_; 
v_unused_2502_ = lean_ctor_get(v___x_2494_, 0);
lean_dec(v_unused_2502_);
v___x_2496_ = v___x_2494_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_dec(v___x_2494_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 0, v_a_2484_);
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2484_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
lean_dec(v_a_2484_);
v_a_2503_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2494_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2494_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2479_);
lean_dec(v_id_2478_);
return v___x_2483_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object* v_id_2512_, lean_object* v_expectedType_x3f_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_2512_, v_expectedType_x3f_2513_, v_a_2514_, v_a_2515_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object* v_t_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2518_, v___y_2520_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_2523_, v___y_2524_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2528_, lean_object* v_constName_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2529_, v___y_2530_, v___y_2531_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2534_, lean_object* v_constName_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2534_, v_constName_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2540_, lean_object* v_ref_2541_, lean_object* v_constName_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2541_, v_constName_2542_, v___y_2543_, v___y_2544_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2547_, lean_object* v_ref_2548_, lean_object* v_constName_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_2547_, v_ref_2548_, v_constName_2549_, v___y_2550_, v___y_2551_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v_ref_2548_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2554_, lean_object* v_ref_2555_, lean_object* v_msg_2556_, lean_object* v_declHint_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2555_, v_msg_2556_, v_declHint_2557_, v___y_2558_, v___y_2559_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2562_, lean_object* v_ref_2563_, lean_object* v_msg_2564_, lean_object* v_declHint_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_2562_, v_ref_2563_, v_msg_2564_, v_declHint_2565_, v___y_2566_, v___y_2567_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v_ref_2563_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_2570_, lean_object* v_declHint_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v___x_2575_; 
v___x_2575_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2570_, v_declHint_2571_, v___y_2573_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2576_, lean_object* v_declHint_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2576_, v_declHint_2577_, v___y_2578_, v___y_2579_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_2582_, lean_object* v_ref_2583_, lean_object* v_msg_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v___x_2588_; 
v___x_2588_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2583_, v_msg_2584_, v___y_2585_, v___y_2586_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2589_, lean_object* v_ref_2590_, lean_object* v_msg_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_2589_, v_ref_2590_, v_msg_2591_, v___y_2592_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v_ref_2590_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_2596_, lean_object* v_msg_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v___x_2601_; 
v___x_2601_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2597_, v___y_2598_, v___y_2599_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_2602_, lean_object* v_msg_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_2602_, v_msg_2603_, v___y_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object* v_id_2608_, lean_object* v_expectedType_x3f_2609_, lean_object* v_as_x27_2610_, lean_object* v_b_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
if (lean_obj_tag(v_as_x27_2610_) == 0)
{
lean_object* v___x_2615_; 
lean_dec(v_expectedType_x3f_2609_);
lean_dec(v_id_2608_);
v___x_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2615_, 0, v_b_2611_);
return v___x_2615_;
}
else
{
lean_object* v_head_2616_; lean_object* v_tail_2617_; lean_object* v___x_2618_; 
v_head_2616_ = lean_ctor_get(v_as_x27_2610_, 0);
v_tail_2617_ = lean_ctor_get(v_as_x27_2610_, 1);
lean_inc(v_expectedType_x3f_2609_);
lean_inc(v_head_2616_);
lean_inc(v_id_2608_);
v___x_2618_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2608_, v_head_2616_, v_expectedType_x3f_2609_, v___y_2612_, v___y_2613_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v___x_2619_; 
lean_dec_ref_known(v___x_2618_, 1);
v___x_2619_ = lean_box(0);
v_as_x27_2610_ = v_tail_2617_;
v_b_2611_ = v___x_2619_;
goto _start;
}
else
{
lean_dec(v_expectedType_x3f_2609_);
lean_dec(v_id_2608_);
return v___x_2618_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object* v_id_2621_, lean_object* v_expectedType_x3f_2622_, lean_object* v_as_x27_2623_, lean_object* v_b_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2621_, v_expectedType_x3f_2622_, v_as_x27_2623_, v_b_2624_, v___y_2625_, v___y_2626_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v_as_x27_2623_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object* v_id_2629_, lean_object* v_expectedType_x3f_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_){
_start:
{
lean_object* v___x_2634_; 
lean_inc(v_id_2629_);
v___x_2634_ = l_Lean_realizeGlobalConst(v_id_2629_, v_a_2631_, v_a_2632_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2663_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2637_ = v___x_2634_;
v_isShared_2638_ = v_isSharedCheck_2663_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2634_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2663_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2639_; lean_object* v_infoState_2640_; uint8_t v_enabled_2641_; 
v___x_2639_ = lean_st_ref_get(v_a_2632_);
v_infoState_2640_ = lean_ctor_get(v___x_2639_, 7);
lean_inc_ref(v_infoState_2640_);
lean_dec(v___x_2639_);
v_enabled_2641_ = lean_ctor_get_uint8(v_infoState_2640_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2640_);
if (v_enabled_2641_ == 0)
{
lean_object* v___x_2643_; 
lean_dec(v_expectedType_x3f_2630_);
lean_dec(v_id_2629_);
if (v_isShared_2638_ == 0)
{
v___x_2643_ = v___x_2637_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2635_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
else
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
lean_del_object(v___x_2637_);
v___x_2645_ = lean_box(0);
v___x_2646_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2629_, v_expectedType_x3f_2630_, v_a_2635_, v___x_2645_, v_a_2631_, v_a_2632_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2653_ == 0)
{
lean_object* v_unused_2654_; 
v_unused_2654_ = lean_ctor_get(v___x_2646_, 0);
lean_dec(v_unused_2654_);
v___x_2648_ = v___x_2646_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_dec(v___x_2646_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v_a_2635_);
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2635_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
else
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
lean_dec(v_a_2635_);
v_a_2655_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2646_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2646_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2660_; 
if (v_isShared_2658_ == 0)
{
v___x_2660_ = v___x_2657_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2630_);
lean_dec(v_id_2629_);
return v___x_2634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object* v_id_2664_, lean_object* v_expectedType_x3f_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_2664_, v_expectedType_x3f_2665_, v_a_2666_, v_a_2667_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object* v_id_2670_, lean_object* v_expectedType_x3f_2671_, lean_object* v_as_2672_, lean_object* v_as_x27_2673_, lean_object* v_b_2674_, lean_object* v_a_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2670_, v_expectedType_x3f_2671_, v_as_x27_2673_, v_b_2674_, v___y_2676_, v___y_2677_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object* v_id_2680_, lean_object* v_expectedType_x3f_2681_, lean_object* v_as_2682_, lean_object* v_as_x27_2683_, lean_object* v_b_2684_, lean_object* v_a_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_2680_, v_expectedType_x3f_2681_, v_as_2682_, v_as_x27_2683_, v_b_2684_, v_a_2685_, v___y_2686_, v___y_2687_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v_as_x27_2683_);
lean_dec(v_as_2682_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object* v_ref_2690_, lean_object* v_as_x27_2691_, lean_object* v_b_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
if (lean_obj_tag(v_as_x27_2691_) == 0)
{
lean_object* v___x_2696_; 
lean_dec(v_ref_2690_);
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v_b_2692_);
return v___x_2696_;
}
else
{
lean_object* v_head_2697_; lean_object* v_tail_2698_; lean_object* v_fst_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v_head_2697_ = lean_ctor_get(v_as_x27_2691_, 0);
v_tail_2698_ = lean_ctor_get(v_as_x27_2691_, 1);
v_fst_2699_ = lean_ctor_get(v_head_2697_, 0);
v___x_2700_ = lean_box(0);
lean_inc(v_fst_2699_);
lean_inc(v_ref_2690_);
v___x_2701_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_2690_, v_fst_2699_, v___x_2700_, v___y_2693_, v___y_2694_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v___x_2702_; 
lean_dec_ref_known(v___x_2701_, 1);
v___x_2702_ = lean_box(0);
v_as_x27_2691_ = v_tail_2698_;
v_b_2692_ = v___x_2702_;
goto _start;
}
else
{
lean_dec(v_ref_2690_);
return v___x_2701_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object* v_ref_2704_, lean_object* v_as_x27_2705_, lean_object* v_b_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2704_, v_as_x27_2705_, v_b_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_as_x27_2705_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object* v_ref_2711_, lean_object* v_id_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Lean_realizeGlobalName(v_id_2712_, v_a_2713_, v_a_2714_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2745_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2719_ = v___x_2716_;
v_isShared_2720_ = v_isSharedCheck_2745_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2716_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2745_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2721_; lean_object* v_infoState_2722_; uint8_t v_enabled_2723_; 
v___x_2721_ = lean_st_ref_get(v_a_2714_);
v_infoState_2722_ = lean_ctor_get(v___x_2721_, 7);
lean_inc_ref(v_infoState_2722_);
lean_dec(v___x_2721_);
v_enabled_2723_ = lean_ctor_get_uint8(v_infoState_2722_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2722_);
if (v_enabled_2723_ == 0)
{
lean_object* v___x_2725_; 
lean_dec(v_ref_2711_);
if (v_isShared_2720_ == 0)
{
v___x_2725_ = v___x_2719_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2717_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
else
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
lean_del_object(v___x_2719_);
v___x_2727_ = lean_box(0);
v___x_2728_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2711_, v_a_2717_, v___x_2727_, v_a_2713_, v_a_2714_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2735_ == 0)
{
lean_object* v_unused_2736_; 
v_unused_2736_ = lean_ctor_get(v___x_2728_, 0);
lean_dec(v_unused_2736_);
v___x_2730_ = v___x_2728_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_dec(v___x_2728_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v_a_2717_);
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2717_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec(v_a_2717_);
v_a_2737_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2728_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2728_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
}
}
else
{
lean_dec(v_ref_2711_);
return v___x_2716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object* v_ref_2746_, lean_object* v_id_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_2746_, v_id_2747_, v_a_2748_, v_a_2749_);
lean_dec(v_a_2749_);
lean_dec_ref(v_a_2748_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object* v_ref_2752_, lean_object* v_as_2753_, lean_object* v_as_x27_2754_, lean_object* v_b_2755_, lean_object* v_a_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2752_, v_as_x27_2754_, v_b_2755_, v___y_2757_, v___y_2758_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object* v_ref_2761_, lean_object* v_as_2762_, lean_object* v_as_x27_2763_, lean_object* v_b_2764_, lean_object* v_a_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_2761_, v_as_2762_, v_as_x27_2763_, v_b_2764_, v_a_2765_, v___y_2766_, v___y_2767_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v_as_x27_2763_);
lean_dec(v_as_2762_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object* v_self_2770_){
_start:
{
lean_object* v_fst_2771_; 
v_fst_2771_ = lean_ctor_get(v_self_2770_, 0);
lean_inc(v_fst_2771_);
return v_fst_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object* v_self_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_2772_);
lean_dec_ref(v_self_2772_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object* v_info_2774_, lean_object* v_treesSaved_2775_, lean_object* v_s_2776_){
_start:
{
if (lean_obj_tag(v_info_2774_) == 0)
{
uint8_t v_enabled_2777_; lean_object* v_assignment_2778_; lean_object* v_lazyAssignment_2779_; lean_object* v_trees_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2790_; 
v_enabled_2777_ = lean_ctor_get_uint8(v_s_2776_, sizeof(void*)*3);
v_assignment_2778_ = lean_ctor_get(v_s_2776_, 0);
v_lazyAssignment_2779_ = lean_ctor_get(v_s_2776_, 1);
v_trees_2780_ = lean_ctor_get(v_s_2776_, 2);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_s_2776_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2782_ = v_s_2776_;
v_isShared_2783_ = v_isSharedCheck_2790_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_trees_2780_);
lean_inc(v_lazyAssignment_2779_);
lean_inc(v_assignment_2778_);
lean_dec(v_s_2776_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2790_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v_val_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
v_val_2784_ = lean_ctor_get(v_info_2774_, 0);
lean_inc(v_val_2784_);
lean_dec_ref_known(v_info_2774_, 1);
v___x_2785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2785_, 0, v_val_2784_);
lean_ctor_set(v___x_2785_, 1, v_trees_2780_);
v___x_2786_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2775_, v___x_2785_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 2, v___x_2786_);
v___x_2788_ = v___x_2782_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_assignment_2778_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_lazyAssignment_2779_);
lean_ctor_set(v_reuseFailAlloc_2789_, 2, v___x_2786_);
lean_ctor_set_uint8(v_reuseFailAlloc_2789_, sizeof(void*)*3, v_enabled_2777_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
else
{
uint8_t v_enabled_2791_; lean_object* v_assignment_2792_; lean_object* v_lazyAssignment_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2809_; 
v_enabled_2791_ = lean_ctor_get_uint8(v_s_2776_, sizeof(void*)*3);
v_assignment_2792_ = lean_ctor_get(v_s_2776_, 0);
v_lazyAssignment_2793_ = lean_ctor_get(v_s_2776_, 1);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_s_2776_);
if (v_isSharedCheck_2809_ == 0)
{
lean_object* v_unused_2810_; 
v_unused_2810_ = lean_ctor_get(v_s_2776_, 2);
lean_dec(v_unused_2810_);
v___x_2795_ = v_s_2776_;
v_isShared_2796_ = v_isSharedCheck_2809_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_lazyAssignment_2793_);
lean_inc(v_assignment_2792_);
lean_dec(v_s_2776_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2809_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v_val_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2808_; 
v_val_2797_ = lean_ctor_get(v_info_2774_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v_info_2774_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2799_ = v_info_2774_;
v_isShared_2800_ = v_isSharedCheck_2808_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_val_2797_);
lean_dec(v_info_2774_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2808_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2802_; 
if (v_isShared_2800_ == 0)
{
lean_ctor_set_tag(v___x_2799_, 2);
v___x_2802_ = v___x_2799_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_val_2797_);
v___x_2802_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2803_; lean_object* v___x_2805_; 
v___x_2803_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2775_, v___x_2802_);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 2, v___x_2803_);
v___x_2805_ = v___x_2795_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_assignment_2792_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_lazyAssignment_2793_);
lean_ctor_set(v_reuseFailAlloc_2806_, 2, v___x_2803_);
lean_ctor_set_uint8(v_reuseFailAlloc_2806_, sizeof(void*)*3, v_enabled_2791_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object* v_treesSaved_2811_, lean_object* v_modifyInfoState_2812_, lean_object* v_info_2813_){
_start:
{
lean_object* v___f_2814_; lean_object* v___x_2815_; 
v___f_2814_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2814_, 0, v_info_2813_);
lean_closure_set(v___f_2814_, 1, v_treesSaved_2811_);
v___x_2815_ = lean_apply_1(v_modifyInfoState_2812_, v___f_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object* v___f_2816_, lean_object* v_info_2817_){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = lean_apply_1(v___f_2816_, v_info_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object* v_toPure_2819_, lean_object* v_toBind_2820_, lean_object* v___f_2821_, lean_object* v_____do__lift_2822_){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2823_, 0, v_____do__lift_2822_);
v___x_2824_ = lean_apply_2(v_toPure_2819_, lean_box(0), v___x_2823_);
v___x_2825_ = lean_apply_4(v_toBind_2820_, lean_box(0), lean_box(0), v___x_2824_, v___f_2821_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object* v_toBind_2826_, lean_object* v_mkInfoOnError_2827_, lean_object* v___f_2828_, lean_object* v_mkInfo_2829_, lean_object* v___f_2830_, lean_object* v_a_x3f_2831_){
_start:
{
if (lean_obj_tag(v_a_x3f_2831_) == 0)
{
lean_object* v___x_2832_; 
lean_dec(v___f_2830_);
lean_dec(v_mkInfo_2829_);
v___x_2832_ = lean_apply_4(v_toBind_2826_, lean_box(0), lean_box(0), v_mkInfoOnError_2827_, v___f_2828_);
return v___x_2832_;
}
else
{
lean_object* v_val_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
lean_dec(v___f_2828_);
lean_dec(v_mkInfoOnError_2827_);
v_val_2833_ = lean_ctor_get(v_a_x3f_2831_, 0);
lean_inc(v_val_2833_);
lean_dec_ref_known(v_a_x3f_2831_, 1);
v___x_2834_ = lean_apply_1(v_mkInfo_2829_, v_val_2833_);
v___x_2835_ = lean_apply_4(v_toBind_2826_, lean_box(0), lean_box(0), v___x_2834_, v___f_2830_);
return v___x_2835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object* v_toFunctor_2836_, lean_object* v_modifyInfoState_2837_, lean_object* v_toPure_2838_, lean_object* v_toBind_2839_, lean_object* v_mkInfoOnError_2840_, lean_object* v_mkInfo_2841_, lean_object* v_inst_2842_, lean_object* v_x_2843_, lean_object* v___f_2844_, lean_object* v_treesSaved_2845_){
_start:
{
lean_object* v_map_2846_; lean_object* v___f_2847_; lean_object* v___f_2848_; lean_object* v___f_2849_; lean_object* v___f_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v_map_2846_ = lean_ctor_get(v_toFunctor_2836_, 0);
lean_inc(v_map_2846_);
lean_dec_ref(v_toFunctor_2836_);
v___f_2847_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2847_, 0, v_treesSaved_2845_);
lean_closure_set(v___f_2847_, 1, v_modifyInfoState_2837_);
v___f_2848_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2848_, 0, v___f_2847_);
lean_inc_ref(v___f_2848_);
lean_inc(v_toBind_2839_);
v___f_2849_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_2849_, 0, v_toPure_2838_);
lean_closure_set(v___f_2849_, 1, v_toBind_2839_);
lean_closure_set(v___f_2849_, 2, v___f_2848_);
v___f_2850_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__6), 6, 5);
lean_closure_set(v___f_2850_, 0, v_toBind_2839_);
lean_closure_set(v___f_2850_, 1, v_mkInfoOnError_2840_);
lean_closure_set(v___f_2850_, 2, v___f_2849_);
lean_closure_set(v___f_2850_, 3, v_mkInfo_2841_);
lean_closure_set(v___f_2850_, 4, v___f_2848_);
v___x_2851_ = lean_apply_4(v_inst_2842_, lean_box(0), lean_box(0), v_x_2843_, v___f_2850_);
v___x_2852_ = lean_apply_4(v_map_2846_, lean_box(0), lean_box(0), v___f_2844_, v___x_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object* v_x_2853_, lean_object* v_inst_2854_, lean_object* v_inst_2855_, lean_object* v_toBind_2856_, lean_object* v___f_2857_, lean_object* v_____do__lift_2858_){
_start:
{
uint8_t v_enabled_2859_; 
v_enabled_2859_ = lean_ctor_get_uint8(v_____do__lift_2858_, sizeof(void*)*3);
if (v_enabled_2859_ == 0)
{
lean_dec(v___f_2857_);
lean_dec(v_toBind_2856_);
lean_dec_ref(v_inst_2855_);
lean_dec_ref(v_inst_2854_);
lean_inc(v_x_2853_);
return v_x_2853_;
}
else
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2854_, v_inst_2855_);
v___x_2861_ = lean_apply_4(v_toBind_2856_, lean_box(0), lean_box(0), v___x_2860_, v___f_2857_);
return v___x_2861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object* v_x_2862_, lean_object* v_inst_2863_, lean_object* v_inst_2864_, lean_object* v_toBind_2865_, lean_object* v___f_2866_, lean_object* v_____do__lift_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__7(v_x_2862_, v_inst_2863_, v_inst_2864_, v_toBind_2865_, v___f_2866_, v_____do__lift_2867_);
lean_dec_ref(v_____do__lift_2867_);
lean_dec(v_x_2862_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object* v_inst_2870_, lean_object* v_inst_2871_, lean_object* v_inst_2872_, lean_object* v_x_2873_, lean_object* v_mkInfo_2874_, lean_object* v_mkInfoOnError_2875_){
_start:
{
lean_object* v_toApplicative_2876_; lean_object* v_toBind_2877_; lean_object* v_getInfoState_2878_; lean_object* v_modifyInfoState_2879_; lean_object* v_toFunctor_2880_; lean_object* v_toPure_2881_; lean_object* v___f_2882_; lean_object* v___f_2883_; lean_object* v___f_2884_; lean_object* v___x_2885_; 
v_toApplicative_2876_ = lean_ctor_get(v_inst_2870_, 0);
v_toBind_2877_ = lean_ctor_get(v_inst_2870_, 1);
lean_inc_n(v_toBind_2877_, 3);
v_getInfoState_2878_ = lean_ctor_get(v_inst_2871_, 0);
lean_inc(v_getInfoState_2878_);
v_modifyInfoState_2879_ = lean_ctor_get(v_inst_2871_, 1);
v_toFunctor_2880_ = lean_ctor_get(v_toApplicative_2876_, 0);
v_toPure_2881_ = lean_ctor_get(v_toApplicative_2876_, 1);
v___f_2882_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2873_);
lean_inc(v_toPure_2881_);
lean_inc(v_modifyInfoState_2879_);
lean_inc_ref(v_toFunctor_2880_);
v___f_2883_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__5), 10, 9);
lean_closure_set(v___f_2883_, 0, v_toFunctor_2880_);
lean_closure_set(v___f_2883_, 1, v_modifyInfoState_2879_);
lean_closure_set(v___f_2883_, 2, v_toPure_2881_);
lean_closure_set(v___f_2883_, 3, v_toBind_2877_);
lean_closure_set(v___f_2883_, 4, v_mkInfoOnError_2875_);
lean_closure_set(v___f_2883_, 5, v_mkInfo_2874_);
lean_closure_set(v___f_2883_, 6, v_inst_2872_);
lean_closure_set(v___f_2883_, 7, v_x_2873_);
lean_closure_set(v___f_2883_, 8, v___f_2882_);
v___f_2884_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2884_, 0, v_x_2873_);
lean_closure_set(v___f_2884_, 1, v_inst_2870_);
lean_closure_set(v___f_2884_, 2, v_inst_2871_);
lean_closure_set(v___f_2884_, 3, v_toBind_2877_);
lean_closure_set(v___f_2884_, 4, v___f_2883_);
v___x_2885_ = lean_apply_4(v_toBind_2877_, lean_box(0), lean_box(0), v_getInfoState_2878_, v___f_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* v_m_2886_, lean_object* v_inst_2887_, lean_object* v_inst_2888_, lean_object* v_00_u03b1_2889_, lean_object* v_inst_2890_, lean_object* v_x_2891_, lean_object* v_mkInfo_2892_, lean_object* v_mkInfoOnError_2893_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Lean_Elab_withInfoContext_x27___redArg(v_inst_2887_, v_inst_2888_, v_inst_2890_, v_x_2891_, v_mkInfo_2892_, v_mkInfoOnError_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object* v_treesSaved_2895_, lean_object* v_tree_2896_, lean_object* v_s_2897_){
_start:
{
uint8_t v_enabled_2898_; lean_object* v_assignment_2899_; lean_object* v_lazyAssignment_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2908_; 
v_enabled_2898_ = lean_ctor_get_uint8(v_s_2897_, sizeof(void*)*3);
v_assignment_2899_ = lean_ctor_get(v_s_2897_, 0);
v_lazyAssignment_2900_ = lean_ctor_get(v_s_2897_, 1);
v_isSharedCheck_2908_ = !lean_is_exclusive(v_s_2897_);
if (v_isSharedCheck_2908_ == 0)
{
lean_object* v_unused_2909_; 
v_unused_2909_ = lean_ctor_get(v_s_2897_, 2);
lean_dec(v_unused_2909_);
v___x_2902_ = v_s_2897_;
v_isShared_2903_ = v_isSharedCheck_2908_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_lazyAssignment_2900_);
lean_inc(v_assignment_2899_);
lean_dec(v_s_2897_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2908_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2904_; lean_object* v___x_2906_; 
v___x_2904_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2895_, v_tree_2896_);
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 2, v___x_2904_);
v___x_2906_ = v___x_2902_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_assignment_2899_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v_lazyAssignment_2900_);
lean_ctor_set(v_reuseFailAlloc_2907_, 2, v___x_2904_);
lean_ctor_set_uint8(v_reuseFailAlloc_2907_, sizeof(void*)*3, v_enabled_2898_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object* v_treesSaved_2910_, lean_object* v_modifyInfoState_2911_, lean_object* v_tree_2912_){
_start:
{
lean_object* v___f_2913_; lean_object* v___x_2914_; 
v___f_2913_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2913_, 0, v_treesSaved_2910_);
lean_closure_set(v___f_2913_, 1, v_tree_2912_);
v___x_2914_ = lean_apply_1(v_modifyInfoState_2911_, v___f_2913_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object* v_mkInfoTree_2915_, lean_object* v_toBind_2916_, lean_object* v___f_2917_, lean_object* v_st_2918_){
_start:
{
lean_object* v_trees_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v_trees_2919_ = lean_ctor_get(v_st_2918_, 2);
lean_inc_ref(v_trees_2919_);
lean_dec_ref(v_st_2918_);
v___x_2920_ = lean_apply_1(v_mkInfoTree_2915_, v_trees_2919_);
v___x_2921_ = lean_apply_4(v_toBind_2916_, lean_box(0), lean_box(0), v___x_2920_, v___f_2917_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object* v_toBind_2922_, lean_object* v_getInfoState_2923_, lean_object* v___f_2924_, lean_object* v_x_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = lean_apply_4(v_toBind_2922_, lean_box(0), lean_box(0), v_getInfoState_2923_, v___f_2924_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object* v_toBind_2927_, lean_object* v_getInfoState_2928_, lean_object* v___f_2929_, lean_object* v_x_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(v_toBind_2927_, v_getInfoState_2928_, v___f_2929_, v_x_2930_);
lean_dec(v_x_2930_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object* v_toFunctor_2932_, lean_object* v_modifyInfoState_2933_, lean_object* v_mkInfoTree_2934_, lean_object* v_toBind_2935_, lean_object* v_getInfoState_2936_, lean_object* v_inst_2937_, lean_object* v_x_2938_, lean_object* v___f_2939_, lean_object* v_treesSaved_2940_){
_start:
{
lean_object* v_map_2941_; lean_object* v___f_2942_; lean_object* v___f_2943_; lean_object* v___f_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v_map_2941_ = lean_ctor_get(v_toFunctor_2932_, 0);
lean_inc(v_map_2941_);
lean_dec_ref(v_toFunctor_2932_);
v___f_2942_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2942_, 0, v_treesSaved_2940_);
lean_closure_set(v___f_2942_, 1, v_modifyInfoState_2933_);
lean_inc(v_toBind_2935_);
v___f_2943_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2943_, 0, v_mkInfoTree_2934_);
lean_closure_set(v___f_2943_, 1, v_toBind_2935_);
lean_closure_set(v___f_2943_, 2, v___f_2942_);
v___f_2944_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_2944_, 0, v_toBind_2935_);
lean_closure_set(v___f_2944_, 1, v_getInfoState_2936_);
lean_closure_set(v___f_2944_, 2, v___f_2943_);
v___x_2945_ = lean_apply_4(v_inst_2937_, lean_box(0), lean_box(0), v_x_2938_, v___f_2944_);
v___x_2946_ = lean_apply_4(v_map_2941_, lean_box(0), lean_box(0), v___f_2939_, v___x_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object* v_inst_2947_, lean_object* v_inst_2948_, lean_object* v_inst_2949_, lean_object* v_x_2950_, lean_object* v_mkInfoTree_2951_){
_start:
{
lean_object* v_toApplicative_2952_; lean_object* v_toBind_2953_; lean_object* v_getInfoState_2954_; lean_object* v_modifyInfoState_2955_; lean_object* v_toFunctor_2956_; lean_object* v___f_2957_; lean_object* v___f_2958_; lean_object* v___f_2959_; lean_object* v___x_2960_; 
v_toApplicative_2952_ = lean_ctor_get(v_inst_2947_, 0);
v_toBind_2953_ = lean_ctor_get(v_inst_2947_, 1);
lean_inc_n(v_toBind_2953_, 3);
v_getInfoState_2954_ = lean_ctor_get(v_inst_2948_, 0);
lean_inc_n(v_getInfoState_2954_, 2);
v_modifyInfoState_2955_ = lean_ctor_get(v_inst_2948_, 1);
v_toFunctor_2956_ = lean_ctor_get(v_toApplicative_2952_, 0);
v___f_2957_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2950_);
lean_inc(v_modifyInfoState_2955_);
lean_inc_ref(v_toFunctor_2956_);
v___f_2958_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2958_, 0, v_toFunctor_2956_);
lean_closure_set(v___f_2958_, 1, v_modifyInfoState_2955_);
lean_closure_set(v___f_2958_, 2, v_mkInfoTree_2951_);
lean_closure_set(v___f_2958_, 3, v_toBind_2953_);
lean_closure_set(v___f_2958_, 4, v_getInfoState_2954_);
lean_closure_set(v___f_2958_, 5, v_inst_2949_);
lean_closure_set(v___f_2958_, 6, v_x_2950_);
lean_closure_set(v___f_2958_, 7, v___f_2957_);
v___f_2959_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2959_, 0, v_x_2950_);
lean_closure_set(v___f_2959_, 1, v_inst_2947_);
lean_closure_set(v___f_2959_, 2, v_inst_2948_);
lean_closure_set(v___f_2959_, 3, v_toBind_2953_);
lean_closure_set(v___f_2959_, 4, v___f_2958_);
v___x_2960_ = lean_apply_4(v_toBind_2953_, lean_box(0), lean_box(0), v_getInfoState_2954_, v___f_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object* v_m_2961_, lean_object* v_inst_2962_, lean_object* v_inst_2963_, lean_object* v_00_u03b1_2964_, lean_object* v_inst_2965_, lean_object* v_x_2966_, lean_object* v_mkInfoTree_2967_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_2962_, v_inst_2963_, v_inst_2965_, v_x_2966_, v_mkInfoTree_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object* v_trees_2969_, lean_object* v_toPure_2970_, lean_object* v_____do__lift_2971_){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2972_, 0, v_____do__lift_2971_);
lean_ctor_set(v___x_2972_, 1, v_trees_2969_);
v___x_2973_ = lean_apply_2(v_toPure_2970_, lean_box(0), v___x_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object* v_toPure_2974_, lean_object* v_toBind_2975_, lean_object* v_mkInfo_2976_, lean_object* v_trees_2977_){
_start:
{
lean_object* v___f_2978_; lean_object* v___x_2979_; 
v___f_2978_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2978_, 0, v_trees_2977_);
lean_closure_set(v___f_2978_, 1, v_toPure_2974_);
v___x_2979_ = lean_apply_4(v_toBind_2975_, lean_box(0), lean_box(0), v_mkInfo_2976_, v___f_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object* v_inst_2980_, lean_object* v_inst_2981_, lean_object* v_inst_2982_, lean_object* v_x_2983_, lean_object* v_mkInfo_2984_){
_start:
{
lean_object* v_toApplicative_2985_; lean_object* v_toBind_2986_; lean_object* v_toPure_2987_; lean_object* v___f_2988_; lean_object* v___x_2989_; 
v_toApplicative_2985_ = lean_ctor_get(v_inst_2980_, 0);
v_toBind_2986_ = lean_ctor_get(v_inst_2980_, 1);
v_toPure_2987_ = lean_ctor_get(v_toApplicative_2985_, 1);
lean_inc(v_toBind_2986_);
lean_inc(v_toPure_2987_);
v___f_2988_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2988_, 0, v_toPure_2987_);
lean_closure_set(v___f_2988_, 1, v_toBind_2986_);
lean_closure_set(v___f_2988_, 2, v_mkInfo_2984_);
v___x_2989_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_2980_, v_inst_2981_, v_inst_2982_, v_x_2983_, v___f_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object* v_m_2990_, lean_object* v_inst_2991_, lean_object* v_inst_2992_, lean_object* v_00_u03b1_2993_, lean_object* v_inst_2994_, lean_object* v_x_2995_, lean_object* v_mkInfo_2996_){
_start:
{
lean_object* v_toApplicative_2997_; lean_object* v_toBind_2998_; lean_object* v_toPure_2999_; lean_object* v___f_3000_; lean_object* v___x_3001_; 
v_toApplicative_2997_ = lean_ctor_get(v_inst_2991_, 0);
v_toBind_2998_ = lean_ctor_get(v_inst_2991_, 1);
v_toPure_2999_ = lean_ctor_get(v_toApplicative_2997_, 1);
lean_inc(v_toBind_2998_);
lean_inc(v_toPure_2999_);
v___f_3000_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3000_, 0, v_toPure_2999_);
lean_closure_set(v___f_3000_, 1, v_toBind_2998_);
lean_closure_set(v___f_3000_, 2, v_mkInfo_2996_);
v___x_3001_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_2991_, v_inst_2992_, v_inst_2994_, v_x_2995_, v___f_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object* v_treesSaved_3002_, lean_object* v_trees_3003_, lean_object* v_s_3004_){
_start:
{
uint8_t v_enabled_3005_; lean_object* v_assignment_3006_; lean_object* v_lazyAssignment_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3015_; 
v_enabled_3005_ = lean_ctor_get_uint8(v_s_3004_, sizeof(void*)*3);
v_assignment_3006_ = lean_ctor_get(v_s_3004_, 0);
v_lazyAssignment_3007_ = lean_ctor_get(v_s_3004_, 1);
v_isSharedCheck_3015_ = !lean_is_exclusive(v_s_3004_);
if (v_isSharedCheck_3015_ == 0)
{
lean_object* v_unused_3016_; 
v_unused_3016_ = lean_ctor_get(v_s_3004_, 2);
lean_dec(v_unused_3016_);
v___x_3009_ = v_s_3004_;
v_isShared_3010_ = v_isSharedCheck_3015_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_lazyAssignment_3007_);
lean_inc(v_assignment_3006_);
lean_dec(v_s_3004_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3015_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3011_; lean_object* v___x_3013_; 
v___x_3011_ = l_Lean_PersistentArray_append___redArg(v_treesSaved_3002_, v_trees_3003_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 2, v___x_3011_);
v___x_3013_ = v___x_3009_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_assignment_3006_);
lean_ctor_set(v_reuseFailAlloc_3014_, 1, v_lazyAssignment_3007_);
lean_ctor_set(v_reuseFailAlloc_3014_, 2, v___x_3011_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, sizeof(void*)*3, v_enabled_3005_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object* v_treesSaved_3017_, lean_object* v_trees_3018_, lean_object* v_s_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_3017_, v_trees_3018_, v_s_3019_);
lean_dec_ref(v_trees_3018_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object* v_treesSaved_3021_, lean_object* v_modifyInfoState_3022_, lean_object* v_trees_3023_){
_start:
{
lean_object* v___f_3024_; lean_object* v___x_3025_; 
v___f_3024_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3024_, 0, v_treesSaved_3021_);
lean_closure_set(v___f_3024_, 1, v_trees_3023_);
v___x_3025_ = lean_apply_1(v_modifyInfoState_3022_, v___f_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object* v_toPure_3026_, lean_object* v_tree_3027_, lean_object* v_____do__lift_3028_){
_start:
{
if (lean_obj_tag(v_____do__lift_3028_) == 0)
{
lean_object* v___x_3029_; 
v___x_3029_ = lean_apply_2(v_toPure_3026_, lean_box(0), v_tree_3027_);
return v___x_3029_;
}
else
{
lean_object* v_val_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v_val_3030_ = lean_ctor_get(v_____do__lift_3028_, 0);
lean_inc(v_val_3030_);
v___x_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3031_, 0, v_val_3030_);
lean_ctor_set(v___x_3031_, 1, v_tree_3027_);
v___x_3032_ = lean_apply_2(v_toPure_3026_, lean_box(0), v___x_3031_);
return v___x_3032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object* v_toPure_3033_, lean_object* v_tree_3034_, lean_object* v_____do__lift_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_3033_, v_tree_3034_, v_____do__lift_3035_);
lean_dec(v_____do__lift_3035_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object* v_assignment_3037_, lean_object* v_toPure_3038_, lean_object* v_toBind_3039_, lean_object* v_ctx_x3f_3040_, lean_object* v_tree_3041_){
_start:
{
lean_object* v_tree_3042_; lean_object* v___f_3043_; lean_object* v___x_3044_; 
v_tree_3042_ = l_Lean_Elab_InfoTree_substitute(v_tree_3041_, v_assignment_3037_);
v___f_3043_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3043_, 0, v_toPure_3038_);
lean_closure_set(v___f_3043_, 1, v_tree_3042_);
v___x_3044_ = lean_apply_4(v_toBind_3039_, lean_box(0), lean_box(0), v_ctx_x3f_3040_, v___f_3043_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object* v_assignment_3045_, lean_object* v_toPure_3046_, lean_object* v_toBind_3047_, lean_object* v_ctx_x3f_3048_, lean_object* v_tree_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(v_assignment_3045_, v_toPure_3046_, v_toBind_3047_, v_ctx_x3f_3048_, v_tree_3049_);
lean_dec_ref(v_assignment_3045_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object* v_toPure_3051_, lean_object* v_toBind_3052_, lean_object* v_ctx_x3f_3053_, lean_object* v_inst_3054_, lean_object* v___f_3055_, lean_object* v_st_3056_){
_start:
{
lean_object* v_assignment_3057_; lean_object* v_trees_3058_; lean_object* v___f_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v_assignment_3057_ = lean_ctor_get(v_st_3056_, 0);
lean_inc_ref(v_assignment_3057_);
v_trees_3058_ = lean_ctor_get(v_st_3056_, 2);
lean_inc_ref(v_trees_3058_);
lean_dec_ref(v_st_3056_);
lean_inc(v_toBind_3052_);
v___f_3059_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_3059_, 0, v_assignment_3057_);
lean_closure_set(v___f_3059_, 1, v_toPure_3051_);
lean_closure_set(v___f_3059_, 2, v_toBind_3052_);
lean_closure_set(v___f_3059_, 3, v_ctx_x3f_3053_);
v___x_3060_ = l_Lean_PersistentArray_mapM___redArg(v_inst_3054_, v___f_3059_, v_trees_3058_);
v___x_3061_ = lean_apply_4(v_toBind_3052_, lean_box(0), lean_box(0), v___x_3060_, v___f_3055_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object* v_toFunctor_3062_, lean_object* v_modifyInfoState_3063_, lean_object* v_toPure_3064_, lean_object* v_toBind_3065_, lean_object* v_ctx_x3f_3066_, lean_object* v_inst_3067_, lean_object* v_getInfoState_3068_, lean_object* v_inst_3069_, lean_object* v_x_3070_, lean_object* v___f_3071_, lean_object* v_treesSaved_3072_){
_start:
{
lean_object* v_map_3073_; lean_object* v___f_3074_; lean_object* v___f_3075_; lean_object* v___f_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v_map_3073_ = lean_ctor_get(v_toFunctor_3062_, 0);
lean_inc(v_map_3073_);
lean_dec_ref(v_toFunctor_3062_);
v___f_3074_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3074_, 0, v_treesSaved_3072_);
lean_closure_set(v___f_3074_, 1, v_modifyInfoState_3063_);
lean_inc(v_toBind_3065_);
v___f_3075_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4), 6, 5);
lean_closure_set(v___f_3075_, 0, v_toPure_3064_);
lean_closure_set(v___f_3075_, 1, v_toBind_3065_);
lean_closure_set(v___f_3075_, 2, v_ctx_x3f_3066_);
lean_closure_set(v___f_3075_, 3, v_inst_3067_);
lean_closure_set(v___f_3075_, 4, v___f_3074_);
v___f_3076_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3076_, 0, v_toBind_3065_);
lean_closure_set(v___f_3076_, 1, v_getInfoState_3068_);
lean_closure_set(v___f_3076_, 2, v___f_3075_);
v___x_3077_ = lean_apply_4(v_inst_3069_, lean_box(0), lean_box(0), v_x_3070_, v___f_3076_);
v___x_3078_ = lean_apply_4(v_map_3073_, lean_box(0), lean_box(0), v___f_3071_, v___x_3077_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object* v_inst_3079_, lean_object* v_inst_3080_, lean_object* v_inst_3081_, lean_object* v_x_3082_, lean_object* v_ctx_x3f_3083_){
_start:
{
lean_object* v_toApplicative_3084_; lean_object* v_toBind_3085_; lean_object* v_getInfoState_3086_; lean_object* v_modifyInfoState_3087_; lean_object* v_toFunctor_3088_; lean_object* v_toPure_3089_; lean_object* v___f_3090_; lean_object* v___f_3091_; lean_object* v___f_3092_; lean_object* v___x_3093_; 
v_toApplicative_3084_ = lean_ctor_get(v_inst_3079_, 0);
v_toBind_3085_ = lean_ctor_get(v_inst_3079_, 1);
lean_inc_n(v_toBind_3085_, 3);
v_getInfoState_3086_ = lean_ctor_get(v_inst_3080_, 0);
lean_inc_n(v_getInfoState_3086_, 2);
v_modifyInfoState_3087_ = lean_ctor_get(v_inst_3080_, 1);
v_toFunctor_3088_ = lean_ctor_get(v_toApplicative_3084_, 0);
v_toPure_3089_ = lean_ctor_get(v_toApplicative_3084_, 1);
v___f_3090_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3082_);
lean_inc_ref(v_inst_3079_);
lean_inc(v_toPure_3089_);
lean_inc(v_modifyInfoState_3087_);
lean_inc_ref(v_toFunctor_3088_);
v___f_3091_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6), 11, 10);
lean_closure_set(v___f_3091_, 0, v_toFunctor_3088_);
lean_closure_set(v___f_3091_, 1, v_modifyInfoState_3087_);
lean_closure_set(v___f_3091_, 2, v_toPure_3089_);
lean_closure_set(v___f_3091_, 3, v_toBind_3085_);
lean_closure_set(v___f_3091_, 4, v_ctx_x3f_3083_);
lean_closure_set(v___f_3091_, 5, v_inst_3079_);
lean_closure_set(v___f_3091_, 6, v_getInfoState_3086_);
lean_closure_set(v___f_3091_, 7, v_inst_3081_);
lean_closure_set(v___f_3091_, 8, v_x_3082_);
lean_closure_set(v___f_3091_, 9, v___f_3090_);
v___f_3092_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3092_, 0, v_x_3082_);
lean_closure_set(v___f_3092_, 1, v_inst_3079_);
lean_closure_set(v___f_3092_, 2, v_inst_3080_);
lean_closure_set(v___f_3092_, 3, v_toBind_3085_);
lean_closure_set(v___f_3092_, 4, v___f_3091_);
v___x_3093_ = lean_apply_4(v_toBind_3085_, lean_box(0), lean_box(0), v_getInfoState_3086_, v___f_3092_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object* v_m_3094_, lean_object* v_inst_3095_, lean_object* v_inst_3096_, lean_object* v_00_u03b1_3097_, lean_object* v_inst_3098_, lean_object* v_x_3099_, lean_object* v_ctx_x3f_3100_){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3095_, v_inst_3096_, v_inst_3098_, v_x_3099_, v_ctx_x3f_3100_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object* v_toPure_3102_, lean_object* v_____do__lift_3103_){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3104_, 0, v_____do__lift_3103_);
v___x_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
v___x_3106_ = lean_apply_2(v_toPure_3102_, lean_box(0), v___x_3105_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object* v_inst_3107_, lean_object* v_inst_3108_, lean_object* v_inst_3109_, lean_object* v_inst_3110_, lean_object* v_inst_3111_, lean_object* v_inst_3112_, lean_object* v_inst_3113_, lean_object* v_inst_3114_, lean_object* v_inst_3115_, lean_object* v_x_3116_){
_start:
{
lean_object* v_toApplicative_3117_; lean_object* v_toBind_3118_; lean_object* v_toPure_3119_; lean_object* v___x_3120_; lean_object* v___f_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v_toApplicative_3117_ = lean_ctor_get(v_inst_3107_, 0);
v_toBind_3118_ = lean_ctor_get(v_inst_3107_, 1);
v_toPure_3119_ = lean_ctor_get(v_toApplicative_3117_, 1);
lean_inc_ref(v_inst_3107_);
v___x_3120_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_3107_, v_inst_3111_, v_inst_3113_, v_inst_3112_, v_inst_3114_, v_inst_3109_, v_inst_3115_);
lean_inc(v_toPure_3119_);
v___f_3121_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3121_, 0, v_toPure_3119_);
lean_inc(v_toBind_3118_);
v___x_3122_ = lean_apply_4(v_toBind_3118_, lean_box(0), lean_box(0), v___x_3120_, v___f_3121_);
v___x_3123_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3107_, v_inst_3108_, v_inst_3110_, v_x_3116_, v___x_3122_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object* v_m_3124_, lean_object* v_inst_3125_, lean_object* v_inst_3126_, lean_object* v_00_u03b1_3127_, lean_object* v_inst_3128_, lean_object* v_inst_3129_, lean_object* v_inst_3130_, lean_object* v_inst_3131_, lean_object* v_inst_3132_, lean_object* v_inst_3133_, lean_object* v_inst_3134_, lean_object* v_x_3135_){
_start:
{
lean_object* v___x_3136_; 
v___x_3136_ = l_Lean_Elab_withSaveInfoContext___redArg(v_inst_3125_, v_inst_3126_, v_inst_3128_, v_inst_3129_, v_inst_3130_, v_inst_3131_, v_inst_3132_, v_inst_3133_, v_inst_3134_, v_x_3135_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object* v_toPure_3137_, lean_object* v_____x_3138_){
_start:
{
if (lean_obj_tag(v_____x_3138_) == 1)
{
lean_object* v_val_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3148_; 
v_val_3139_ = lean_ctor_get(v_____x_3138_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_____x_3138_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3141_ = v_____x_3138_;
v_isShared_3142_ = v_isSharedCheck_3148_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_val_3139_);
lean_dec(v_____x_3138_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3148_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3143_; lean_object* v___x_3145_; 
v___x_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3143_, 0, v_val_3139_);
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 0, v___x_3143_);
v___x_3145_ = v___x_3141_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
lean_object* v___x_3146_; 
v___x_3146_ = lean_apply_2(v_toPure_3137_, lean_box(0), v___x_3145_);
return v___x_3146_;
}
}
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_dec(v_____x_3138_);
v___x_3149_ = lean_box(0);
v___x_3150_ = lean_apply_2(v_toPure_3137_, lean_box(0), v___x_3149_);
return v___x_3150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object* v_inst_3151_, lean_object* v_inst_3152_, lean_object* v_inst_3153_, lean_object* v_inst_3154_, lean_object* v_x_3155_){
_start:
{
lean_object* v_toApplicative_3156_; lean_object* v_toBind_3157_; lean_object* v_toPure_3158_; lean_object* v___f_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v_toApplicative_3156_ = lean_ctor_get(v_inst_3151_, 0);
v_toBind_3157_ = lean_ctor_get(v_inst_3151_, 1);
v_toPure_3158_ = lean_ctor_get(v_toApplicative_3156_, 1);
lean_inc(v_toPure_3158_);
v___f_3159_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3159_, 0, v_toPure_3158_);
lean_inc(v_toBind_3157_);
v___x_3160_ = lean_apply_4(v_toBind_3157_, lean_box(0), lean_box(0), v_inst_3154_, v___f_3159_);
v___x_3161_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3151_, v_inst_3152_, v_inst_3153_, v_x_3155_, v___x_3160_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object* v_m_3162_, lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_00_u03b1_3165_, lean_object* v_inst_3166_, lean_object* v_inst_3167_, lean_object* v_x_3168_){
_start:
{
lean_object* v___x_3169_; 
v___x_3169_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(v_inst_3163_, v_inst_3164_, v_inst_3166_, v_inst_3167_, v_x_3168_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object* v_toPure_3170_, lean_object* v_autoImplicits_3171_){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3172_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3172_, 0, v_autoImplicits_3171_);
v___x_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
v___x_3174_ = lean_apply_2(v_toPure_3170_, lean_box(0), v___x_3173_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object* v_inst_3175_, lean_object* v_inst_3176_, lean_object* v_inst_3177_, lean_object* v_inst_3178_, lean_object* v_x_3179_){
_start:
{
lean_object* v_toApplicative_3180_; lean_object* v_toBind_3181_; lean_object* v_toPure_3182_; lean_object* v___f_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v_toApplicative_3180_ = lean_ctor_get(v_inst_3175_, 0);
v_toBind_3181_ = lean_ctor_get(v_inst_3175_, 1);
v_toPure_3182_ = lean_ctor_get(v_toApplicative_3180_, 1);
lean_inc(v_toPure_3182_);
v___f_3183_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3183_, 0, v_toPure_3182_);
lean_inc(v_toBind_3181_);
v___x_3184_ = lean_apply_4(v_toBind_3181_, lean_box(0), lean_box(0), v_inst_3178_, v___f_3183_);
v___x_3185_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3175_, v_inst_3176_, v_inst_3177_, v_x_3179_, v___x_3184_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object* v_m_3186_, lean_object* v_inst_3187_, lean_object* v_inst_3188_, lean_object* v_00_u03b1_3189_, lean_object* v_inst_3190_, lean_object* v_inst_3191_, lean_object* v_x_3192_){
_start:
{
lean_object* v___x_3193_; 
v___x_3193_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(v_inst_3187_, v_inst_3188_, v_inst_3190_, v_inst_3191_, v_x_3192_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object* v___x_3194_, lean_object* v___x_3195_, lean_object* v_mvarId_3196_, lean_object* v_toPure_3197_, lean_object* v_____do__lift_3198_){
_start:
{
lean_object* v_assignment_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v_assignment_3199_ = lean_ctor_get(v_____do__lift_3198_, 0);
v___x_3200_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_3194_, v___x_3195_, v_assignment_3199_, v_mvarId_3196_);
v___x_3201_ = lean_apply_2(v_toPure_3197_, lean_box(0), v___x_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object* v___x_3202_, lean_object* v___x_3203_, lean_object* v_mvarId_3204_, lean_object* v_toPure_3205_, lean_object* v_____do__lift_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(v___x_3202_, v___x_3203_, v_mvarId_3204_, v_toPure_3205_, v_____do__lift_3206_);
lean_dec_ref(v_____do__lift_3206_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object* v_inst_3210_, lean_object* v_inst_3211_, lean_object* v_mvarId_3212_){
_start:
{
lean_object* v_toApplicative_3213_; lean_object* v_toBind_3214_; lean_object* v_getInfoState_3215_; lean_object* v_toPure_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___f_3219_; lean_object* v___x_3220_; 
v_toApplicative_3213_ = lean_ctor_get(v_inst_3210_, 0);
lean_inc_ref(v_toApplicative_3213_);
v_toBind_3214_ = lean_ctor_get(v_inst_3210_, 1);
lean_inc(v_toBind_3214_);
lean_dec_ref(v_inst_3210_);
v_getInfoState_3215_ = lean_ctor_get(v_inst_3211_, 0);
lean_inc(v_getInfoState_3215_);
lean_dec_ref(v_inst_3211_);
v_toPure_3216_ = lean_ctor_get(v_toApplicative_3213_, 1);
lean_inc(v_toPure_3216_);
lean_dec_ref(v_toApplicative_3213_);
v___x_3217_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3218_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___f_3219_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3219_, 0, v___x_3217_);
lean_closure_set(v___f_3219_, 1, v___x_3218_);
lean_closure_set(v___f_3219_, 2, v_mvarId_3212_);
lean_closure_set(v___f_3219_, 3, v_toPure_3216_);
v___x_3220_ = lean_apply_4(v_toBind_3214_, lean_box(0), lean_box(0), v_getInfoState_3215_, v___f_3219_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* v_m_3221_, lean_object* v_inst_3222_, lean_object* v_inst_3223_, lean_object* v_mvarId_3224_){
_start:
{
lean_object* v___x_3225_; 
v___x_3225_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3222_, v_inst_3223_, v_mvarId_3224_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object* v___x_3226_, lean_object* v___x_3227_, lean_object* v_mvarId_3228_, lean_object* v_infoTree_3229_, lean_object* v_s_3230_){
_start:
{
uint8_t v_enabled_3231_; lean_object* v_assignment_3232_; lean_object* v_lazyAssignment_3233_; lean_object* v_trees_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3242_; 
v_enabled_3231_ = lean_ctor_get_uint8(v_s_3230_, sizeof(void*)*3);
v_assignment_3232_ = lean_ctor_get(v_s_3230_, 0);
v_lazyAssignment_3233_ = lean_ctor_get(v_s_3230_, 1);
v_trees_3234_ = lean_ctor_get(v_s_3230_, 2);
v_isSharedCheck_3242_ = !lean_is_exclusive(v_s_3230_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3236_ = v_s_3230_;
v_isShared_3237_ = v_isSharedCheck_3242_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_trees_3234_);
lean_inc(v_lazyAssignment_3233_);
lean_inc(v_assignment_3232_);
lean_dec(v_s_3230_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3242_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3238_; lean_object* v___x_3240_; 
v___x_3238_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3226_, v___x_3227_, v_assignment_3232_, v_mvarId_3228_, v_infoTree_3229_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v___x_3238_);
v___x_3240_ = v___x_3236_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3238_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v_lazyAssignment_3233_);
lean_ctor_set(v_reuseFailAlloc_3241_, 2, v_trees_3234_);
lean_ctor_set_uint8(v_reuseFailAlloc_3241_, sizeof(void*)*3, v_enabled_3231_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3246_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2));
v___x_3247_ = lean_unsigned_to_nat(2u);
v___x_3248_ = lean_unsigned_to_nat(380u);
v___x_3249_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1));
v___x_3250_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0));
v___x_3251_ = l_mkPanicMessageWithDecl(v___x_3250_, v___x_3249_, v___x_3248_, v___x_3247_, v___x_3246_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object* v_inst_3252_, lean_object* v___f_3253_, lean_object* v___x_3254_, lean_object* v_____do__lift_3255_){
_start:
{
if (lean_obj_tag(v_____do__lift_3255_) == 0)
{
lean_object* v_modifyInfoState_3256_; lean_object* v___x_3257_; 
v_modifyInfoState_3256_ = lean_ctor_get(v_inst_3252_, 1);
lean_inc(v_modifyInfoState_3256_);
lean_dec_ref(v_inst_3252_);
v___x_3257_ = lean_apply_1(v_modifyInfoState_3256_, v___f_3253_);
return v___x_3257_;
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
lean_dec_ref(v___f_3253_);
lean_dec_ref(v_inst_3252_);
v___x_3258_ = lean_obj_once(&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3, &l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3_once, _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3);
v___x_3259_ = l_panic___redArg(v___x_3254_, v___x_3258_);
return v___x_3259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object* v_inst_3260_, lean_object* v___f_3261_, lean_object* v___x_3262_, lean_object* v_____do__lift_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(v_inst_3260_, v___f_3261_, v___x_3262_, v_____do__lift_3263_);
lean_dec(v_____do__lift_3263_);
lean_dec(v___x_3262_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object* v_inst_3265_, lean_object* v_inst_3266_, lean_object* v_mvarId_3267_, lean_object* v_infoTree_3268_){
_start:
{
lean_object* v_toBind_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___f_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___f_3276_; lean_object* v___x_3277_; 
v_toBind_3269_ = lean_ctor_get(v_inst_3265_, 1);
lean_inc(v_toBind_3269_);
v___x_3270_ = lean_box(0);
v___x_3271_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3272_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
lean_inc(v_mvarId_3267_);
v___f_3273_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__0), 5, 4);
lean_closure_set(v___f_3273_, 0, v___x_3271_);
lean_closure_set(v___f_3273_, 1, v___x_3272_);
lean_closure_set(v___f_3273_, 2, v_mvarId_3267_);
lean_closure_set(v___f_3273_, 3, v_infoTree_3268_);
lean_inc_ref(v_inst_3266_);
lean_inc_ref(v_inst_3265_);
v___x_3274_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3265_, v_inst_3266_, v_mvarId_3267_);
v___x_3275_ = l_instInhabitedOfMonad___redArg(v_inst_3265_, v___x_3270_);
v___f_3276_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3276_, 0, v_inst_3266_);
lean_closure_set(v___f_3276_, 1, v___f_3273_);
lean_closure_set(v___f_3276_, 2, v___x_3275_);
v___x_3277_ = lean_apply_4(v_toBind_3269_, lean_box(0), lean_box(0), v___x_3274_, v___f_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* v_m_3278_, lean_object* v_inst_3279_, lean_object* v_inst_3280_, lean_object* v_mvarId_3281_, lean_object* v_infoTree_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Lean_Elab_assignInfoHoleId___redArg(v_inst_3279_, v_inst_3280_, v_mvarId_3281_, v_infoTree_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object* v_stx_3284_, lean_object* v_output_3285_, lean_object* v_toPure_3286_, lean_object* v_____do__lift_3287_){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3288_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3288_, 0, v_____do__lift_3287_);
lean_ctor_set(v___x_3288_, 1, v_stx_3284_);
lean_ctor_set(v___x_3288_, 2, v_output_3285_);
v___x_3289_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
v___x_3290_ = lean_apply_2(v_toPure_3286_, lean_box(0), v___x_3289_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object* v_inst_3291_, lean_object* v_inst_3292_, lean_object* v_inst_3293_, lean_object* v_inst_3294_, lean_object* v_stx_3295_, lean_object* v_output_3296_, lean_object* v_x_3297_){
_start:
{
lean_object* v_toApplicative_3298_; lean_object* v_toBind_3299_; lean_object* v_toPure_3300_; lean_object* v___f_3301_; lean_object* v_mkInfo_3302_; lean_object* v___f_3303_; lean_object* v___x_3304_; 
v_toApplicative_3298_ = lean_ctor_get(v_inst_3292_, 0);
v_toBind_3299_ = lean_ctor_get(v_inst_3292_, 1);
v_toPure_3300_ = lean_ctor_get(v_toApplicative_3298_, 1);
lean_inc_n(v_toPure_3300_, 2);
v___f_3301_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3301_, 0, v_stx_3295_);
lean_closure_set(v___f_3301_, 1, v_output_3296_);
lean_closure_set(v___f_3301_, 2, v_toPure_3300_);
lean_inc_n(v_toBind_3299_, 2);
v_mkInfo_3302_ = lean_apply_4(v_toBind_3299_, lean_box(0), lean_box(0), v_inst_3294_, v___f_3301_);
v___f_3303_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3303_, 0, v_toPure_3300_);
lean_closure_set(v___f_3303_, 1, v_toBind_3299_);
lean_closure_set(v___f_3303_, 2, v_mkInfo_3302_);
v___x_3304_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3292_, v_inst_3293_, v_inst_3291_, v_x_3297_, v___f_3303_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* v_m_3305_, lean_object* v_00_u03b1_3306_, lean_object* v_inst_3307_, lean_object* v_inst_3308_, lean_object* v_inst_3309_, lean_object* v_inst_3310_, lean_object* v_stx_3311_, lean_object* v_output_3312_, lean_object* v_x_3313_){
_start:
{
lean_object* v___x_3314_; 
v___x_3314_ = l_Lean_Elab_withMacroExpansionInfo___redArg(v_inst_3307_, v_inst_3308_, v_inst_3309_, v_inst_3310_, v_stx_3311_, v_output_3312_, v_x_3313_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object* v_treesSaved_3315_, lean_object* v___x_3316_, lean_object* v___x_3317_, lean_object* v___x_3318_, lean_object* v_mvarId_3319_, lean_object* v_s_3320_){
_start:
{
lean_object* v_trees_3321_; uint8_t v_enabled_3322_; lean_object* v_assignment_3323_; lean_object* v_lazyAssignment_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3341_; 
v_trees_3321_ = lean_ctor_get(v_s_3320_, 2);
v_enabled_3322_ = lean_ctor_get_uint8(v_s_3320_, sizeof(void*)*3);
v_assignment_3323_ = lean_ctor_get(v_s_3320_, 0);
v_lazyAssignment_3324_ = lean_ctor_get(v_s_3320_, 1);
v_isSharedCheck_3341_ = !lean_is_exclusive(v_s_3320_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3326_ = v_s_3320_;
v_isShared_3327_ = v_isSharedCheck_3341_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_trees_3321_);
lean_inc(v_lazyAssignment_3324_);
lean_inc(v_assignment_3323_);
lean_dec(v_s_3320_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3341_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v_size_3328_; lean_object* v___x_3329_; uint8_t v___x_3330_; 
v_size_3328_ = lean_ctor_get(v_trees_3321_, 2);
v___x_3329_ = lean_unsigned_to_nat(0u);
v___x_3330_ = lean_nat_dec_lt(v___x_3329_, v_size_3328_);
if (v___x_3330_ == 0)
{
lean_object* v___x_3332_; 
lean_dec_ref(v_trees_3321_);
lean_dec(v_mvarId_3319_);
lean_dec_ref(v___x_3318_);
lean_dec_ref(v___x_3317_);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 2, v_treesSaved_3315_);
v___x_3332_ = v___x_3326_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_assignment_3323_);
lean_ctor_set(v_reuseFailAlloc_3333_, 1, v_lazyAssignment_3324_);
lean_ctor_set(v_reuseFailAlloc_3333_, 2, v_treesSaved_3315_);
lean_ctor_set_uint8(v_reuseFailAlloc_3333_, sizeof(void*)*3, v_enabled_3322_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
else
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3339_; 
v___x_3334_ = lean_unsigned_to_nat(1u);
v___x_3335_ = lean_nat_sub(v_size_3328_, v___x_3334_);
v___x_3336_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3316_, v_trees_3321_, v___x_3335_);
lean_dec(v___x_3335_);
lean_dec_ref(v_trees_3321_);
v___x_3337_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3317_, v___x_3318_, v_assignment_3323_, v_mvarId_3319_, v___x_3336_);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 2, v_treesSaved_3315_);
lean_ctor_set(v___x_3326_, 0, v___x_3337_);
v___x_3339_ = v___x_3326_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_lazyAssignment_3324_);
lean_ctor_set(v_reuseFailAlloc_3340_, 2, v_treesSaved_3315_);
lean_ctor_set_uint8(v_reuseFailAlloc_3340_, sizeof(void*)*3, v_enabled_3322_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1___boxed(lean_object* v_treesSaved_3342_, lean_object* v___x_3343_, lean_object* v___x_3344_, lean_object* v___x_3345_, lean_object* v_mvarId_3346_, lean_object* v_s_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Lean_Elab_withInfoHole___redArg___lam__1(v_treesSaved_3342_, v___x_3343_, v___x_3344_, v___x_3345_, v_mvarId_3346_, v_s_3347_);
lean_dec_ref(v___x_3343_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object* v_modifyInfoState_3349_, lean_object* v___f_3350_, lean_object* v_x_3351_){
_start:
{
lean_object* v___x_3352_; 
v___x_3352_ = lean_apply_1(v_modifyInfoState_3349_, v___f_3350_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object* v_modifyInfoState_3353_, lean_object* v___f_3354_, lean_object* v_x_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_3353_, v___f_3354_, v_x_3355_);
lean_dec(v_x_3355_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object* v_toFunctor_3357_, lean_object* v___x_3358_, lean_object* v___x_3359_, lean_object* v___x_3360_, lean_object* v_mvarId_3361_, lean_object* v_modifyInfoState_3362_, lean_object* v_inst_3363_, lean_object* v_x_3364_, lean_object* v___f_3365_, lean_object* v_treesSaved_3366_){
_start:
{
lean_object* v_map_3367_; lean_object* v___f_3368_; lean_object* v___f_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v_map_3367_ = lean_ctor_get(v_toFunctor_3357_, 0);
lean_inc(v_map_3367_);
lean_dec_ref(v_toFunctor_3357_);
v___f_3368_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_3368_, 0, v_treesSaved_3366_);
lean_closure_set(v___f_3368_, 1, v___x_3358_);
lean_closure_set(v___f_3368_, 2, v___x_3359_);
lean_closure_set(v___f_3368_, 3, v___x_3360_);
lean_closure_set(v___f_3368_, 4, v_mvarId_3361_);
v___f_3369_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3369_, 0, v_modifyInfoState_3362_);
lean_closure_set(v___f_3369_, 1, v___f_3368_);
v___x_3370_ = lean_apply_4(v_inst_3363_, lean_box(0), lean_box(0), v_x_3364_, v___f_3369_);
v___x_3371_ = lean_apply_4(v_map_3367_, lean_box(0), lean_box(0), v___f_3365_, v___x_3370_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object* v_inst_3372_, lean_object* v_inst_3373_, lean_object* v_inst_3374_, lean_object* v_mvarId_3375_, lean_object* v_x_3376_){
_start:
{
lean_object* v_toApplicative_3377_; lean_object* v_toBind_3378_; lean_object* v_getInfoState_3379_; lean_object* v_modifyInfoState_3380_; lean_object* v_toFunctor_3381_; lean_object* v___f_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___f_3386_; lean_object* v___f_3387_; lean_object* v___x_3388_; 
v_toApplicative_3377_ = lean_ctor_get(v_inst_3373_, 0);
v_toBind_3378_ = lean_ctor_get(v_inst_3373_, 1);
lean_inc_n(v_toBind_3378_, 2);
v_getInfoState_3379_ = lean_ctor_get(v_inst_3374_, 0);
lean_inc(v_getInfoState_3379_);
v_modifyInfoState_3380_ = lean_ctor_get(v_inst_3374_, 1);
v_toFunctor_3381_ = lean_ctor_get(v_toApplicative_3377_, 0);
v___f_3382_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
v___x_3383_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3384_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3385_ = l_Lean_Elab_instInhabitedInfoTree_default;
lean_inc(v_x_3376_);
lean_inc(v_modifyInfoState_3380_);
lean_inc_ref(v_toFunctor_3381_);
v___f_3386_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3386_, 0, v_toFunctor_3381_);
lean_closure_set(v___f_3386_, 1, v___x_3385_);
lean_closure_set(v___f_3386_, 2, v___x_3383_);
lean_closure_set(v___f_3386_, 3, v___x_3384_);
lean_closure_set(v___f_3386_, 4, v_mvarId_3375_);
lean_closure_set(v___f_3386_, 5, v_modifyInfoState_3380_);
lean_closure_set(v___f_3386_, 6, v_inst_3372_);
lean_closure_set(v___f_3386_, 7, v_x_3376_);
lean_closure_set(v___f_3386_, 8, v___f_3382_);
v___f_3387_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3387_, 0, v_x_3376_);
lean_closure_set(v___f_3387_, 1, v_inst_3373_);
lean_closure_set(v___f_3387_, 2, v_inst_3374_);
lean_closure_set(v___f_3387_, 3, v_toBind_3378_);
lean_closure_set(v___f_3387_, 4, v___f_3386_);
v___x_3388_ = lean_apply_4(v_toBind_3378_, lean_box(0), lean_box(0), v_getInfoState_3379_, v___f_3387_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object* v_m_3389_, lean_object* v_00_u03b1_3390_, lean_object* v_inst_3391_, lean_object* v_inst_3392_, lean_object* v_inst_3393_, lean_object* v_mvarId_3394_, lean_object* v_x_3395_){
_start:
{
lean_object* v_toApplicative_3396_; lean_object* v_toBind_3397_; lean_object* v_getInfoState_3398_; lean_object* v_modifyInfoState_3399_; lean_object* v_toFunctor_3400_; lean_object* v___f_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___f_3405_; lean_object* v___f_3406_; lean_object* v___x_3407_; 
v_toApplicative_3396_ = lean_ctor_get(v_inst_3392_, 0);
v_toBind_3397_ = lean_ctor_get(v_inst_3392_, 1);
lean_inc_n(v_toBind_3397_, 2);
v_getInfoState_3398_ = lean_ctor_get(v_inst_3393_, 0);
lean_inc(v_getInfoState_3398_);
v_modifyInfoState_3399_ = lean_ctor_get(v_inst_3393_, 1);
v_toFunctor_3400_ = lean_ctor_get(v_toApplicative_3396_, 0);
v___f_3401_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
v___x_3402_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3403_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3404_ = l_Lean_Elab_instInhabitedInfoTree_default;
lean_inc(v_x_3395_);
lean_inc(v_modifyInfoState_3399_);
lean_inc_ref(v_toFunctor_3400_);
v___f_3405_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3405_, 0, v_toFunctor_3400_);
lean_closure_set(v___f_3405_, 1, v___x_3404_);
lean_closure_set(v___f_3405_, 2, v___x_3402_);
lean_closure_set(v___f_3405_, 3, v___x_3403_);
lean_closure_set(v___f_3405_, 4, v_mvarId_3394_);
lean_closure_set(v___f_3405_, 5, v_modifyInfoState_3399_);
lean_closure_set(v___f_3405_, 6, v_inst_3391_);
lean_closure_set(v___f_3405_, 7, v_x_3395_);
lean_closure_set(v___f_3405_, 8, v___f_3401_);
v___f_3406_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3406_, 0, v_x_3395_);
lean_closure_set(v___f_3406_, 1, v_inst_3392_);
lean_closure_set(v___f_3406_, 2, v_inst_3393_);
lean_closure_set(v___f_3406_, 3, v_toBind_3397_);
lean_closure_set(v___f_3406_, 4, v___f_3405_);
v___x_3407_ = lean_apply_4(v_toBind_3397_, lean_box(0), lean_box(0), v_getInfoState_3398_, v___f_3406_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t v_flag_3408_, lean_object* v_s_3409_){
_start:
{
lean_object* v_assignment_3410_; lean_object* v_lazyAssignment_3411_; lean_object* v_trees_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
v_assignment_3410_ = lean_ctor_get(v_s_3409_, 0);
v_lazyAssignment_3411_ = lean_ctor_get(v_s_3409_, 1);
v_trees_3412_ = lean_ctor_get(v_s_3409_, 2);
v_isSharedCheck_3419_ = !lean_is_exclusive(v_s_3409_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v_s_3409_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_trees_3412_);
lean_inc(v_lazyAssignment_3411_);
lean_inc(v_assignment_3410_);
lean_dec(v_s_3409_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_assignment_3410_);
lean_ctor_set(v_reuseFailAlloc_3418_, 1, v_lazyAssignment_3411_);
lean_ctor_set(v_reuseFailAlloc_3418_, 2, v_trees_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_ctor_set_uint8(v___x_3417_, sizeof(void*)*3, v_flag_3408_);
return v___x_3417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object* v_flag_3420_, lean_object* v_s_3421_){
_start:
{
uint8_t v_flag_boxed_3422_; lean_object* v_res_3423_; 
v_flag_boxed_3422_ = lean_unbox(v_flag_3420_);
v_res_3423_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_3422_, v_s_3421_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object* v_inst_3424_, uint8_t v_flag_3425_){
_start:
{
lean_object* v_modifyInfoState_3426_; lean_object* v___x_3427_; lean_object* v___f_3428_; lean_object* v___x_3429_; 
v_modifyInfoState_3426_ = lean_ctor_get(v_inst_3424_, 1);
lean_inc(v_modifyInfoState_3426_);
lean_dec_ref(v_inst_3424_);
v___x_3427_ = lean_box(v_flag_3425_);
v___f_3428_ = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3428_, 0, v___x_3427_);
v___x_3429_ = lean_apply_1(v_modifyInfoState_3426_, v___f_3428_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object* v_inst_3430_, lean_object* v_flag_3431_){
_start:
{
uint8_t v_flag_boxed_3432_; lean_object* v_res_3433_; 
v_flag_boxed_3432_ = lean_unbox(v_flag_3431_);
v_res_3433_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3430_, v_flag_boxed_3432_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object* v_m_3434_, lean_object* v_inst_3435_, uint8_t v_flag_3436_){
_start:
{
lean_object* v___x_3437_; 
v___x_3437_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3435_, v_flag_3436_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object* v_m_3438_, lean_object* v_inst_3439_, lean_object* v_flag_3440_){
_start:
{
uint8_t v_flag_boxed_3441_; lean_object* v_res_3442_; 
v_flag_boxed_3441_ = lean_unbox(v_flag_3440_);
v_res_3442_ = l_Lean_Elab_enableInfoTree(v_m_3438_, v_inst_3439_, v_flag_boxed_3441_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object* v_x_3443_){
_start:
{
lean_object* v_fst_3444_; 
v_fst_3444_ = lean_ctor_get(v_x_3443_, 0);
lean_inc(v_fst_3444_);
return v_fst_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object* v_x_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_3445_);
lean_dec_ref(v_x_3445_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object* v_x_3447_, lean_object* v_____r_3448_){
_start:
{
lean_inc(v_x_3447_);
return v_x_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object* v_x_3449_, lean_object* v_____r_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_3449_, v_____r_3450_);
lean_dec(v_x_3449_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object* v___x_3452_, lean_object* v_x_3453_){
_start:
{
lean_inc(v___x_3452_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object* v___x_3454_, lean_object* v_x_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_3454_, v_x_3455_);
lean_dec(v_x_3455_);
lean_dec(v___x_3454_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object* v_toFunctor_3457_, lean_object* v_inst_3458_, uint8_t v_flag_3459_, lean_object* v_toBind_3460_, lean_object* v___f_3461_, lean_object* v_inst_3462_, lean_object* v___f_3463_, lean_object* v_____do__lift_3464_){
_start:
{
uint8_t v_enabled_3465_; lean_object* v_map_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___f_3470_; lean_object* v_y_3471_; lean_object* v___x_3472_; 
v_enabled_3465_ = lean_ctor_get_uint8(v_____do__lift_3464_, sizeof(void*)*3);
v_map_3466_ = lean_ctor_get(v_toFunctor_3457_, 0);
lean_inc(v_map_3466_);
lean_dec_ref(v_toFunctor_3457_);
lean_inc_ref(v_inst_3458_);
v___x_3467_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3458_, v_flag_3459_);
v___x_3468_ = lean_apply_4(v_toBind_3460_, lean_box(0), lean_box(0), v___x_3467_, v___f_3461_);
v___x_3469_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3458_, v_enabled_3465_);
v___f_3470_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_3470_, 0, v___x_3469_);
v_y_3471_ = lean_apply_4(v_inst_3462_, lean_box(0), lean_box(0), v___x_3468_, v___f_3470_);
v___x_3472_ = lean_apply_4(v_map_3466_, lean_box(0), lean_box(0), v___f_3463_, v_y_3471_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object* v_toFunctor_3473_, lean_object* v_inst_3474_, lean_object* v_flag_3475_, lean_object* v_toBind_3476_, lean_object* v___f_3477_, lean_object* v_inst_3478_, lean_object* v___f_3479_, lean_object* v_____do__lift_3480_){
_start:
{
uint8_t v_flag_boxed_3481_; lean_object* v_res_3482_; 
v_flag_boxed_3481_ = lean_unbox(v_flag_3475_);
v_res_3482_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_3473_, v_inst_3474_, v_flag_boxed_3481_, v_toBind_3476_, v___f_3477_, v_inst_3478_, v___f_3479_, v_____do__lift_3480_);
lean_dec_ref(v_____do__lift_3480_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object* v_inst_3484_, lean_object* v_inst_3485_, lean_object* v_inst_3486_, uint8_t v_flag_3487_, lean_object* v_x_3488_){
_start:
{
lean_object* v_toApplicative_3489_; lean_object* v_toBind_3490_; lean_object* v_getInfoState_3491_; lean_object* v_toFunctor_3492_; lean_object* v___f_3493_; lean_object* v___f_3494_; lean_object* v___x_3495_; lean_object* v___f_3496_; lean_object* v___x_3497_; 
v_toApplicative_3489_ = lean_ctor_get(v_inst_3484_, 0);
lean_inc_ref(v_toApplicative_3489_);
v_toBind_3490_ = lean_ctor_get(v_inst_3484_, 1);
lean_inc_n(v_toBind_3490_, 2);
lean_dec_ref(v_inst_3484_);
v_getInfoState_3491_ = lean_ctor_get(v_inst_3485_, 0);
lean_inc(v_getInfoState_3491_);
v_toFunctor_3492_ = lean_ctor_get(v_toApplicative_3489_, 0);
lean_inc_ref(v_toFunctor_3492_);
lean_dec_ref(v_toApplicative_3489_);
v___f_3493_ = ((lean_object*)(l_Lean_Elab_withEnableInfoTree___redArg___closed__0));
v___f_3494_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3494_, 0, v_x_3488_);
v___x_3495_ = lean_box(v_flag_3487_);
v___f_3496_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_3496_, 0, v_toFunctor_3492_);
lean_closure_set(v___f_3496_, 1, v_inst_3485_);
lean_closure_set(v___f_3496_, 2, v___x_3495_);
lean_closure_set(v___f_3496_, 3, v_toBind_3490_);
lean_closure_set(v___f_3496_, 4, v___f_3494_);
lean_closure_set(v___f_3496_, 5, v_inst_3486_);
lean_closure_set(v___f_3496_, 6, v___f_3493_);
v___x_3497_ = lean_apply_4(v_toBind_3490_, lean_box(0), lean_box(0), v_getInfoState_3491_, v___f_3496_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object* v_inst_3498_, lean_object* v_inst_3499_, lean_object* v_inst_3500_, lean_object* v_flag_3501_, lean_object* v_x_3502_){
_start:
{
uint8_t v_flag_boxed_3503_; lean_object* v_res_3504_; 
v_flag_boxed_3503_ = lean_unbox(v_flag_3501_);
v_res_3504_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3498_, v_inst_3499_, v_inst_3500_, v_flag_boxed_3503_, v_x_3502_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object* v_m_3505_, lean_object* v_00_u03b1_3506_, lean_object* v_inst_3507_, lean_object* v_inst_3508_, lean_object* v_inst_3509_, uint8_t v_flag_3510_, lean_object* v_x_3511_){
_start:
{
lean_object* v___x_3512_; 
v___x_3512_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3507_, v_inst_3508_, v_inst_3509_, v_flag_3510_, v_x_3511_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object* v_m_3513_, lean_object* v_00_u03b1_3514_, lean_object* v_inst_3515_, lean_object* v_inst_3516_, lean_object* v_inst_3517_, lean_object* v_flag_3518_, lean_object* v_x_3519_){
_start:
{
uint8_t v_flag_boxed_3520_; lean_object* v_res_3521_; 
v_flag_boxed_3520_ = lean_unbox(v_flag_3518_);
v_res_3521_ = l_Lean_Elab_withEnableInfoTree(v_m_3513_, v_00_u03b1_3514_, v_inst_3515_, v_inst_3516_, v_inst_3517_, v_flag_boxed_3520_, v_x_3519_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object* v_toPure_3522_, lean_object* v_____do__lift_3523_){
_start:
{
lean_object* v_trees_3524_; lean_object* v___x_3525_; 
v_trees_3524_ = lean_ctor_get(v_____do__lift_3523_, 2);
lean_inc_ref(v_trees_3524_);
lean_dec_ref(v_____do__lift_3523_);
v___x_3525_ = lean_apply_2(v_toPure_3522_, lean_box(0), v_trees_3524_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object* v_inst_3526_, lean_object* v_inst_3527_){
_start:
{
lean_object* v_toApplicative_3528_; lean_object* v_toBind_3529_; lean_object* v_getInfoState_3530_; lean_object* v_toPure_3531_; lean_object* v___f_3532_; lean_object* v___x_3533_; 
v_toApplicative_3528_ = lean_ctor_get(v_inst_3527_, 0);
lean_inc_ref(v_toApplicative_3528_);
v_toBind_3529_ = lean_ctor_get(v_inst_3527_, 1);
lean_inc(v_toBind_3529_);
lean_dec_ref(v_inst_3527_);
v_getInfoState_3530_ = lean_ctor_get(v_inst_3526_, 0);
lean_inc(v_getInfoState_3530_);
lean_dec_ref(v_inst_3526_);
v_toPure_3531_ = lean_ctor_get(v_toApplicative_3528_, 1);
lean_inc(v_toPure_3531_);
lean_dec_ref(v_toApplicative_3528_);
v___f_3532_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3532_, 0, v_toPure_3531_);
v___x_3533_ = lean_apply_4(v_toBind_3529_, lean_box(0), lean_box(0), v_getInfoState_3530_, v___f_3532_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object* v_m_3534_, lean_object* v_inst_3535_, lean_object* v_inst_3536_){
_start:
{
lean_object* v___x_3537_; 
v___x_3537_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_3535_, v_inst_3536_);
return v___x_3537_;
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
