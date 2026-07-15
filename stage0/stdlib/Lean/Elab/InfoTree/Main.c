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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Elab_instInhabitedInfoTree_default;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqMVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableMVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
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
lean_object* v_a_229_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_toCommandContextInfo_236_; lean_object* v_env_237_; lean_object* v_options_238_; lean_object* v_currNamespace_239_; lean_object* v_openDecls_240_; lean_object* v_ngen_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; lean_object* v_env_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___y_255_; lean_object* v___y_256_; lean_object* v_fileName_257_; lean_object* v_fileMap_258_; lean_object* v_currRecDepth_259_; lean_object* v_ref_260_; lean_object* v_currNamespace_261_; lean_object* v_openDecls_262_; lean_object* v_initHeartbeats_263_; lean_object* v_maxHeartbeats_264_; lean_object* v_quotContext_265_; lean_object* v_currMacroScope_266_; lean_object* v_cancelTk_x3f_267_; uint8_t v_suppressElabErrors_268_; lean_object* v_inheritedTraceOptions_269_; lean_object* v___y_270_; uint8_t v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; uint8_t v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; uint8_t v___y_328_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_env_359_; lean_object* v___x_360_; uint8_t v___x_361_; lean_object* v___y_363_; lean_object* v___y_364_; uint8_t v___y_394_; uint8_t v___x_414_; 
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
v___x_348_ = l_Lean_inheritedTraceOptions;
v___x_349_ = lean_st_ref_get(v___x_348_);
v___x_350_ = lean_st_ref_get(v___x_253_);
v___x_351_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14));
v___x_352_ = l_Lean_instInhabitedFileMap_default;
v___x_353_ = l_Lean_Options_empty;
v___x_354_ = lean_unsigned_to_nat(1000u);
v___x_355_ = lean_box(0);
v___x_356_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15);
v___x_357_ = lean_box(0);
v___x_358_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_358_, 0, v___x_351_);
lean_ctor_set(v___x_358_, 1, v___x_352_);
lean_ctor_set(v___x_358_, 2, v___x_353_);
lean_ctor_set(v___x_358_, 3, v___x_232_);
lean_ctor_set(v___x_358_, 4, v___x_354_);
lean_ctor_set(v___x_358_, 5, v___x_355_);
lean_ctor_set(v___x_358_, 6, v_currNamespace_239_);
lean_ctor_set(v___x_358_, 7, v_openDecls_240_);
lean_ctor_set(v___x_358_, 8, v___x_235_);
lean_ctor_set(v___x_358_, 9, v___x_356_);
lean_ctor_set(v___x_358_, 10, v___x_246_);
lean_ctor_set(v___x_358_, 11, v___x_242_);
lean_ctor_set(v___x_358_, 12, v___x_357_);
lean_ctor_set(v___x_358_, 13, v___x_349_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*14, v___x_244_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*14 + 1, v___x_244_);
v_env_359_ = lean_ctor_get(v___x_350_, 0);
lean_inc_ref(v_env_359_);
lean_dec(v___x_350_);
v___x_360_ = l_Lean_diagnostics;
v___x_361_ = lean_uint8_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16);
v___x_414_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_359_);
lean_dec_ref(v_env_359_);
if (v___x_414_ == 0)
{
if (v___x_361_ == 0)
{
lean_inc(v___x_253_);
v___y_363_ = v___x_358_;
v___y_364_ = v___x_253_;
goto v___jp_362_;
}
else
{
v___y_394_ = v___x_414_;
goto v___jp_393_;
}
}
else
{
v___y_394_ = v___x_361_;
goto v___jp_393_;
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
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v_options_238_, v___y_256_);
v___x_272_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_272_, 0, v_fileName_257_);
lean_ctor_set(v___x_272_, 1, v_fileMap_258_);
lean_ctor_set(v___x_272_, 2, v_options_238_);
lean_ctor_set(v___x_272_, 3, v_currRecDepth_259_);
lean_ctor_set(v___x_272_, 4, v___x_271_);
lean_ctor_set(v___x_272_, 5, v_ref_260_);
lean_ctor_set(v___x_272_, 6, v_currNamespace_261_);
lean_ctor_set(v___x_272_, 7, v_openDecls_262_);
lean_ctor_set(v___x_272_, 8, v_initHeartbeats_263_);
lean_ctor_set(v___x_272_, 9, v_maxHeartbeats_264_);
lean_ctor_set(v___x_272_, 10, v_quotContext_265_);
lean_ctor_set(v___x_272_, 11, v_currMacroScope_266_);
lean_ctor_set(v___x_272_, 12, v_cancelTk_x3f_267_);
lean_ctor_set(v___x_272_, 13, v_inheritedTraceOptions_269_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*14, v___y_255_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*14 + 1, v_suppressElabErrors_268_);
v___x_273_ = lean_apply_3(v_x_226_, v___x_272_, v___y_270_, lean_box(0));
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_282_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_282_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_278_ = lean_st_ref_get(v___x_253_);
lean_dec(v___x_253_);
lean_dec(v___x_278_);
if (v_isShared_277_ == 0)
{
v___x_280_ = v___x_276_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_274_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_304_; 
lean_dec(v___x_253_);
v_a_283_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_304_ == 0)
{
v___x_285_ = v___x_273_;
v_isShared_286_ = v_isSharedCheck_304_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_273_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_304_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
if (lean_obj_tag(v_a_283_) == 0)
{
lean_object* v_msg_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v_msg_287_ = lean_ctor_get(v_a_283_, 1);
lean_inc_ref(v_msg_287_);
lean_dec_ref_known(v_a_283_, 2);
v___x_288_ = l_Lean_MessageData_toString(v_msg_287_);
v___x_289_ = lean_mk_io_user_error(v___x_288_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_289_);
v___x_291_ = v___x_285_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
else
{
lean_object* v_id_293_; lean_object* v___x_294_; 
lean_del_object(v___x_285_);
v_id_293_ = lean_ctor_get(v_a_283_, 0);
lean_inc(v_id_293_);
lean_dec_ref_known(v_a_283_, 2);
v___x_294_ = l_Lean_InternalExceptionId_getName(v_id_293_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec(v_id_293_);
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref_known(v___x_294_, 1);
v___x_296_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11));
v___x_297_ = l_Lean_Name_toString(v_a_295_, v___x_249_);
v___x_298_ = lean_string_append(v___x_296_, v___x_297_);
lean_dec_ref(v___x_297_);
v_a_229_ = v___x_298_;
goto v___jp_228_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec_ref_known(v___x_294_, 1);
v___x_299_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12));
v___x_300_ = l_Nat_reprFast(v_id_293_);
v___x_301_ = lean_string_append(v___x_299_, v___x_300_);
lean_dec_ref(v___x_300_);
v___x_302_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13));
v___x_303_ = lean_string_append(v___x_301_, v___x_302_);
v_a_229_ = v___x_303_;
goto v___jp_228_;
}
}
}
}
}
v___jp_305_:
{
lean_object* v_fileName_310_; lean_object* v_fileMap_311_; lean_object* v_currRecDepth_312_; lean_object* v_ref_313_; lean_object* v_currNamespace_314_; lean_object* v_openDecls_315_; lean_object* v_initHeartbeats_316_; lean_object* v_maxHeartbeats_317_; lean_object* v_quotContext_318_; lean_object* v_currMacroScope_319_; lean_object* v_cancelTk_x3f_320_; uint8_t v_suppressElabErrors_321_; lean_object* v_inheritedTraceOptions_322_; 
v_fileName_310_ = lean_ctor_get(v___y_308_, 0);
lean_inc_ref(v_fileName_310_);
v_fileMap_311_ = lean_ctor_get(v___y_308_, 1);
lean_inc_ref(v_fileMap_311_);
v_currRecDepth_312_ = lean_ctor_get(v___y_308_, 3);
lean_inc(v_currRecDepth_312_);
v_ref_313_ = lean_ctor_get(v___y_308_, 5);
lean_inc(v_ref_313_);
v_currNamespace_314_ = lean_ctor_get(v___y_308_, 6);
lean_inc(v_currNamespace_314_);
v_openDecls_315_ = lean_ctor_get(v___y_308_, 7);
lean_inc(v_openDecls_315_);
v_initHeartbeats_316_ = lean_ctor_get(v___y_308_, 8);
lean_inc(v_initHeartbeats_316_);
v_maxHeartbeats_317_ = lean_ctor_get(v___y_308_, 9);
lean_inc(v_maxHeartbeats_317_);
v_quotContext_318_ = lean_ctor_get(v___y_308_, 10);
lean_inc(v_quotContext_318_);
v_currMacroScope_319_ = lean_ctor_get(v___y_308_, 11);
lean_inc(v_currMacroScope_319_);
v_cancelTk_x3f_320_ = lean_ctor_get(v___y_308_, 12);
lean_inc(v_cancelTk_x3f_320_);
v_suppressElabErrors_321_ = lean_ctor_get_uint8(v___y_308_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_322_ = lean_ctor_get(v___y_308_, 13);
lean_inc_ref(v_inheritedTraceOptions_322_);
lean_dec_ref(v___y_308_);
v___y_255_ = v___y_306_;
v___y_256_ = v___y_307_;
v_fileName_257_ = v_fileName_310_;
v_fileMap_258_ = v_fileMap_311_;
v_currRecDepth_259_ = v_currRecDepth_312_;
v_ref_260_ = v_ref_313_;
v_currNamespace_261_ = v_currNamespace_314_;
v_openDecls_262_ = v_openDecls_315_;
v_initHeartbeats_263_ = v_initHeartbeats_316_;
v_maxHeartbeats_264_ = v_maxHeartbeats_317_;
v_quotContext_265_ = v_quotContext_318_;
v_currMacroScope_266_ = v_currMacroScope_319_;
v_cancelTk_x3f_267_ = v_cancelTk_x3f_320_;
v_suppressElabErrors_268_ = v_suppressElabErrors_321_;
v_inheritedTraceOptions_269_ = v_inheritedTraceOptions_322_;
v___y_270_ = v___y_309_;
goto v___jp_254_;
}
v___jp_323_:
{
if (v___y_328_ == 0)
{
lean_object* v___x_329_; lean_object* v_env_330_; lean_object* v_nextMacroScope_331_; lean_object* v_ngen_332_; lean_object* v_auxDeclNGen_333_; lean_object* v_traceState_334_; lean_object* v_messages_335_; lean_object* v_infoState_336_; lean_object* v_snapshotTasks_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_346_; 
v___x_329_ = lean_st_ref_take(v___y_325_);
v_env_330_ = lean_ctor_get(v___x_329_, 0);
v_nextMacroScope_331_ = lean_ctor_get(v___x_329_, 1);
v_ngen_332_ = lean_ctor_get(v___x_329_, 2);
v_auxDeclNGen_333_ = lean_ctor_get(v___x_329_, 3);
v_traceState_334_ = lean_ctor_get(v___x_329_, 4);
v_messages_335_ = lean_ctor_get(v___x_329_, 6);
v_infoState_336_ = lean_ctor_get(v___x_329_, 7);
v_snapshotTasks_337_ = lean_ctor_get(v___x_329_, 8);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_346_ == 0)
{
lean_object* v_unused_347_; 
v_unused_347_ = lean_ctor_get(v___x_329_, 5);
lean_dec(v_unused_347_);
v___x_339_ = v___x_329_;
v_isShared_340_ = v_isSharedCheck_346_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_snapshotTasks_337_);
lean_inc(v_infoState_336_);
lean_inc(v_messages_335_);
lean_inc(v_traceState_334_);
lean_inc(v_auxDeclNGen_333_);
lean_inc(v_ngen_332_);
lean_inc(v_nextMacroScope_331_);
lean_inc(v_env_330_);
lean_dec(v___x_329_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_346_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_341_ = l_Lean_Kernel_enableDiag(v_env_330_, v___y_324_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 5, v___x_233_);
lean_ctor_set(v___x_339_, 0, v___x_341_);
v___x_343_ = v___x_339_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_nextMacroScope_331_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v_ngen_332_);
lean_ctor_set(v_reuseFailAlloc_345_, 3, v_auxDeclNGen_333_);
lean_ctor_set(v_reuseFailAlloc_345_, 4, v_traceState_334_);
lean_ctor_set(v_reuseFailAlloc_345_, 5, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_345_, 6, v_messages_335_);
lean_ctor_set(v_reuseFailAlloc_345_, 7, v_infoState_336_);
lean_ctor_set(v_reuseFailAlloc_345_, 8, v_snapshotTasks_337_);
v___x_343_ = v_reuseFailAlloc_345_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; 
v___x_344_ = lean_st_ref_set(v___y_325_, v___x_343_);
v___y_306_ = v___y_324_;
v___y_307_ = v___y_326_;
v___y_308_ = v___y_327_;
v___y_309_ = v___y_325_;
goto v___jp_305_;
}
}
}
else
{
v___y_306_ = v___y_324_;
v___y_307_ = v___y_326_;
v___y_308_ = v___y_327_;
v___y_309_ = v___y_325_;
goto v___jp_305_;
}
}
v___jp_362_:
{
lean_object* v___x_365_; lean_object* v_fileName_366_; lean_object* v_fileMap_367_; lean_object* v_currRecDepth_368_; lean_object* v_ref_369_; lean_object* v_currNamespace_370_; lean_object* v_openDecls_371_; lean_object* v_initHeartbeats_372_; lean_object* v_maxHeartbeats_373_; lean_object* v_quotContext_374_; lean_object* v_currMacroScope_375_; lean_object* v_cancelTk_x3f_376_; uint8_t v_suppressElabErrors_377_; lean_object* v_inheritedTraceOptions_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_390_; 
v___x_365_ = lean_st_ref_get(v___y_364_);
v_fileName_366_ = lean_ctor_get(v___y_363_, 0);
v_fileMap_367_ = lean_ctor_get(v___y_363_, 1);
v_currRecDepth_368_ = lean_ctor_get(v___y_363_, 3);
v_ref_369_ = lean_ctor_get(v___y_363_, 5);
v_currNamespace_370_ = lean_ctor_get(v___y_363_, 6);
v_openDecls_371_ = lean_ctor_get(v___y_363_, 7);
v_initHeartbeats_372_ = lean_ctor_get(v___y_363_, 8);
v_maxHeartbeats_373_ = lean_ctor_get(v___y_363_, 9);
v_quotContext_374_ = lean_ctor_get(v___y_363_, 10);
v_currMacroScope_375_ = lean_ctor_get(v___y_363_, 11);
v_cancelTk_x3f_376_ = lean_ctor_get(v___y_363_, 12);
v_suppressElabErrors_377_ = lean_ctor_get_uint8(v___y_363_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_378_ = lean_ctor_get(v___y_363_, 13);
v_isSharedCheck_390_ = !lean_is_exclusive(v___y_363_);
if (v_isSharedCheck_390_ == 0)
{
lean_object* v_unused_391_; lean_object* v_unused_392_; 
v_unused_391_ = lean_ctor_get(v___y_363_, 4);
lean_dec(v_unused_391_);
v_unused_392_ = lean_ctor_get(v___y_363_, 2);
lean_dec(v_unused_392_);
v___x_380_ = v___y_363_;
v_isShared_381_ = v_isSharedCheck_390_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_inheritedTraceOptions_378_);
lean_inc(v_cancelTk_x3f_376_);
lean_inc(v_currMacroScope_375_);
lean_inc(v_quotContext_374_);
lean_inc(v_maxHeartbeats_373_);
lean_inc(v_initHeartbeats_372_);
lean_inc(v_openDecls_371_);
lean_inc(v_currNamespace_370_);
lean_inc(v_ref_369_);
lean_inc(v_currRecDepth_368_);
lean_inc(v_fileMap_367_);
lean_inc(v_fileName_366_);
lean_dec(v___y_363_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_390_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v_env_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v_env_382_ = lean_ctor_get(v___x_365_, 0);
lean_inc_ref(v_env_382_);
lean_dec(v___x_365_);
v___x_383_ = l_Lean_maxRecDepth;
v___x_384_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17);
lean_inc_ref(v_inheritedTraceOptions_378_);
lean_inc(v_cancelTk_x3f_376_);
lean_inc(v_currMacroScope_375_);
lean_inc(v_quotContext_374_);
lean_inc(v_maxHeartbeats_373_);
lean_inc(v_initHeartbeats_372_);
lean_inc(v_openDecls_371_);
lean_inc(v_currNamespace_370_);
lean_inc(v_ref_369_);
lean_inc(v_currRecDepth_368_);
lean_inc_ref(v_fileMap_367_);
lean_inc_ref(v_fileName_366_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 4, v___x_384_);
lean_ctor_set(v___x_380_, 2, v___x_353_);
v___x_386_ = v___x_380_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_fileName_366_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_fileMap_367_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_389_, 3, v_currRecDepth_368_);
lean_ctor_set(v_reuseFailAlloc_389_, 4, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_389_, 5, v_ref_369_);
lean_ctor_set(v_reuseFailAlloc_389_, 6, v_currNamespace_370_);
lean_ctor_set(v_reuseFailAlloc_389_, 7, v_openDecls_371_);
lean_ctor_set(v_reuseFailAlloc_389_, 8, v_initHeartbeats_372_);
lean_ctor_set(v_reuseFailAlloc_389_, 9, v_maxHeartbeats_373_);
lean_ctor_set(v_reuseFailAlloc_389_, 10, v_quotContext_374_);
lean_ctor_set(v_reuseFailAlloc_389_, 11, v_currMacroScope_375_);
lean_ctor_set(v_reuseFailAlloc_389_, 12, v_cancelTk_x3f_376_);
lean_ctor_set(v_reuseFailAlloc_389_, 13, v_inheritedTraceOptions_378_);
lean_ctor_set_uint8(v_reuseFailAlloc_389_, sizeof(void*)*14 + 1, v_suppressElabErrors_377_);
v___x_386_ = v_reuseFailAlloc_389_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
uint8_t v___x_387_; uint8_t v___x_388_; 
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*14, v___x_361_);
v___x_387_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v_options_238_, v___x_360_);
v___x_388_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_382_);
lean_dec_ref(v_env_382_);
if (v___x_388_ == 0)
{
if (v___x_387_ == 0)
{
lean_dec_ref(v___x_386_);
v___y_255_ = v___x_387_;
v___y_256_ = v___x_383_;
v_fileName_257_ = v_fileName_366_;
v_fileMap_258_ = v_fileMap_367_;
v_currRecDepth_259_ = v_currRecDepth_368_;
v_ref_260_ = v_ref_369_;
v_currNamespace_261_ = v_currNamespace_370_;
v_openDecls_262_ = v_openDecls_371_;
v_initHeartbeats_263_ = v_initHeartbeats_372_;
v_maxHeartbeats_264_ = v_maxHeartbeats_373_;
v_quotContext_265_ = v_quotContext_374_;
v_currMacroScope_266_ = v_currMacroScope_375_;
v_cancelTk_x3f_267_ = v_cancelTk_x3f_376_;
v_suppressElabErrors_268_ = v_suppressElabErrors_377_;
v_inheritedTraceOptions_269_ = v_inheritedTraceOptions_378_;
v___y_270_ = v___y_364_;
goto v___jp_254_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_378_);
lean_dec(v_cancelTk_x3f_376_);
lean_dec(v_currMacroScope_375_);
lean_dec(v_quotContext_374_);
lean_dec(v_maxHeartbeats_373_);
lean_dec(v_initHeartbeats_372_);
lean_dec(v_openDecls_371_);
lean_dec(v_currNamespace_370_);
lean_dec(v_ref_369_);
lean_dec(v_currRecDepth_368_);
lean_dec_ref(v_fileMap_367_);
lean_dec_ref(v_fileName_366_);
v___y_324_ = v___x_387_;
v___y_325_ = v___y_364_;
v___y_326_ = v___x_383_;
v___y_327_ = v___x_386_;
v___y_328_ = v___x_388_;
goto v___jp_323_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_378_);
lean_dec(v_cancelTk_x3f_376_);
lean_dec(v_currMacroScope_375_);
lean_dec(v_quotContext_374_);
lean_dec(v_maxHeartbeats_373_);
lean_dec(v_initHeartbeats_372_);
lean_dec(v_openDecls_371_);
lean_dec(v_currNamespace_370_);
lean_dec(v_ref_369_);
lean_dec(v_currRecDepth_368_);
lean_dec_ref(v_fileMap_367_);
lean_dec_ref(v_fileName_366_);
v___y_324_ = v___x_387_;
v___y_325_ = v___y_364_;
v___y_326_ = v___x_383_;
v___y_327_ = v___x_386_;
v___y_328_ = v___x_387_;
goto v___jp_323_;
}
}
}
}
v___jp_393_:
{
if (v___y_394_ == 0)
{
lean_object* v___x_395_; lean_object* v_env_396_; lean_object* v_nextMacroScope_397_; lean_object* v_ngen_398_; lean_object* v_auxDeclNGen_399_; lean_object* v_traceState_400_; lean_object* v_messages_401_; lean_object* v_infoState_402_; lean_object* v_snapshotTasks_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_412_; 
v___x_395_ = lean_st_ref_take(v___x_253_);
v_env_396_ = lean_ctor_get(v___x_395_, 0);
v_nextMacroScope_397_ = lean_ctor_get(v___x_395_, 1);
v_ngen_398_ = lean_ctor_get(v___x_395_, 2);
v_auxDeclNGen_399_ = lean_ctor_get(v___x_395_, 3);
v_traceState_400_ = lean_ctor_get(v___x_395_, 4);
v_messages_401_ = lean_ctor_get(v___x_395_, 6);
v_infoState_402_ = lean_ctor_get(v___x_395_, 7);
v_snapshotTasks_403_ = lean_ctor_get(v___x_395_, 8);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v___x_395_, 5);
lean_dec(v_unused_413_);
v___x_405_ = v___x_395_;
v_isShared_406_ = v_isSharedCheck_412_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_snapshotTasks_403_);
lean_inc(v_infoState_402_);
lean_inc(v_messages_401_);
lean_inc(v_traceState_400_);
lean_inc(v_auxDeclNGen_399_);
lean_inc(v_ngen_398_);
lean_inc(v_nextMacroScope_397_);
lean_inc(v_env_396_);
lean_dec(v___x_395_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_412_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_407_ = l_Lean_Kernel_enableDiag(v_env_396_, v___x_361_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 5, v___x_233_);
lean_ctor_set(v___x_405_, 0, v___x_407_);
v___x_409_ = v___x_405_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_nextMacroScope_397_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_ngen_398_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_auxDeclNGen_399_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v_traceState_400_);
lean_ctor_set(v_reuseFailAlloc_411_, 5, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_411_, 6, v_messages_401_);
lean_ctor_set(v_reuseFailAlloc_411_, 7, v_infoState_402_);
lean_ctor_set(v_reuseFailAlloc_411_, 8, v_snapshotTasks_403_);
v___x_409_ = v_reuseFailAlloc_411_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_410_; 
v___x_410_ = lean_st_ref_set(v___x_253_, v___x_409_);
lean_inc(v___x_253_);
v___y_363_ = v___x_358_;
v___y_364_ = v___x_253_;
goto v___jp_362_;
}
}
}
else
{
lean_inc(v___x_253_);
v___y_363_ = v___x_358_;
v___y_364_ = v___x_253_;
goto v___jp_362_;
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
lean_object* v___x_475_; 
v___x_475_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_475_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_479_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
lean_ctor_set(v___x_479_, 2, v___x_478_);
lean_ctor_set(v___x_479_, 3, v___x_478_);
lean_ctor_set(v___x_479_, 4, v___x_478_);
lean_ctor_set(v___x_479_, 5, v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = lean_unsigned_to_nat(32u);
v___x_481_ = lean_mk_empty_array_with_capacity(v___x_480_);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8(void){
_start:
{
size_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_483_ = ((size_t)5ULL);
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = lean_unsigned_to_nat(32u);
v___x_486_ = lean_mk_empty_array_with_capacity(v___x_485_);
v___x_487_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7);
v___x_488_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___x_486_);
lean_ctor_set(v___x_488_, 2, v___x_484_);
lean_ctor_set(v___x_488_, 3, v___x_484_);
lean_ctor_set_usize(v___x_488_, 4, v___x_483_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
lean_ctor_set(v___x_490_, 2, v___x_489_);
lean_ctor_set(v___x_490_, 3, v___x_489_);
lean_ctor_set(v___x_490_, 4, v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object* v_info_491_, lean_object* v_lctx_492_, lean_object* v_x_493_){
_start:
{
lean_object* v___x_495_; uint8_t v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_toCommandContextInfo_503_; lean_object* v_mctx_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___f_509_; lean_object* v___x_510_; 
v___x_495_ = lean_box(1);
v___x_496_ = 0;
v___x_497_ = 1;
v___x_498_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2);
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3));
v___x_501_ = lean_box(0);
v___x_502_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_502_, 0, v___x_498_);
lean_ctor_set(v___x_502_, 1, v___x_495_);
lean_ctor_set(v___x_502_, 2, v_lctx_492_);
lean_ctor_set(v___x_502_, 3, v___x_500_);
lean_ctor_set(v___x_502_, 4, v___x_501_);
lean_ctor_set(v___x_502_, 5, v___x_499_);
lean_ctor_set(v___x_502_, 6, v___x_501_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*7, v___x_496_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*7 + 1, v___x_496_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*7 + 2, v___x_496_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*7 + 3, v___x_497_);
v_toCommandContextInfo_503_ = lean_ctor_get(v_info_491_, 0);
v_mctx_504_ = lean_ctor_get(v_toCommandContextInfo_503_, 3);
v___x_505_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6);
v___x_506_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8);
v___x_507_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9);
lean_inc_ref(v_mctx_504_);
v___x_508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_508_, 0, v_mctx_504_);
lean_ctor_set(v___x_508_, 1, v___x_505_);
lean_ctor_set(v___x_508_, 2, v___x_495_);
lean_ctor_set(v___x_508_, 3, v___x_506_);
lean_ctor_set(v___x_508_, 4, v___x_507_);
v___f_509_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_509_, 0, v___x_508_);
lean_closure_set(v___f_509_, 1, v_x_493_);
lean_closure_set(v___f_509_, 2, v___x_502_);
v___x_510_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_491_, v___f_509_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_519_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_519_ == 0)
{
v___x_513_ = v___x_510_;
v_isShared_514_ = v_isSharedCheck_519_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_519_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v_fst_515_; lean_object* v___x_517_; 
v_fst_515_ = lean_ctor_get(v_a_511_, 0);
lean_inc(v_fst_515_);
lean_dec(v_a_511_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v_fst_515_);
v___x_517_ = v___x_513_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_fst_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
v_a_520_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_510_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_510_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object* v_info_528_, lean_object* v_lctx_529_, lean_object* v_x_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_528_, v_lctx_529_, v_x_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object* v_00_u03b1_533_, lean_object* v_info_534_, lean_object* v_lctx_535_, lean_object* v_x_536_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_534_, v_lctx_535_, v_x_536_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object* v_00_u03b1_539_, lean_object* v_info_540_, lean_object* v_lctx_541_, lean_object* v_x_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Elab_ContextInfo_runMetaM(v_00_u03b1_539_, v_info_540_, v_lctx_541_, v_x_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object* v_info_545_, lean_object* v_lctx_546_){
_start:
{
lean_object* v_toCommandContextInfo_547_; lean_object* v_env_548_; lean_object* v_mctx_549_; lean_object* v_options_550_; lean_object* v_currNamespace_551_; lean_object* v_openDecls_552_; lean_object* v___x_553_; 
v_toCommandContextInfo_547_ = lean_ctor_get(v_info_545_, 0);
v_env_548_ = lean_ctor_get(v_toCommandContextInfo_547_, 0);
v_mctx_549_ = lean_ctor_get(v_toCommandContextInfo_547_, 3);
v_options_550_ = lean_ctor_get(v_toCommandContextInfo_547_, 4);
v_currNamespace_551_ = lean_ctor_get(v_toCommandContextInfo_547_, 5);
v_openDecls_552_ = lean_ctor_get(v_toCommandContextInfo_547_, 6);
lean_inc(v_openDecls_552_);
lean_inc(v_currNamespace_551_);
lean_inc_ref(v_options_550_);
lean_inc_ref(v_mctx_549_);
lean_inc_ref(v_env_548_);
v___x_553_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_553_, 0, v_env_548_);
lean_ctor_set(v___x_553_, 1, v_mctx_549_);
lean_ctor_set(v___x_553_, 2, v_lctx_546_);
lean_ctor_set(v___x_553_, 3, v_options_550_);
lean_ctor_set(v___x_553_, 4, v_currNamespace_551_);
lean_ctor_set(v___x_553_, 5, v_openDecls_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object* v_info_554_, lean_object* v_lctx_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_554_, v_lctx_555_);
lean_dec_ref(v_info_554_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object* v_info_557_, lean_object* v_lctx_558_, lean_object* v_stx_559_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_557_, v_lctx_558_);
v___x_562_ = l_Lean_ppTerm(v___x_561_, v_stx_559_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object* v_info_564_, lean_object* v_lctx_565_, lean_object* v_stx_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_Elab_ContextInfo_ppSyntax(v_info_564_, v_lctx_565_, v_stx_566_);
lean_dec_ref(v_info_564_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(lean_object* v_ctx_584_, lean_object* v_pos_585_, lean_object* v_info_586_){
_start:
{
lean_object* v_toCommandContextInfo_587_; lean_object* v_fileMap_588_; lean_object* v___x_589_; lean_object* v_line_590_; lean_object* v_column_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_614_; 
v_toCommandContextInfo_587_ = lean_ctor_get(v_ctx_584_, 0);
lean_inc_ref(v_toCommandContextInfo_587_);
lean_dec_ref(v_ctx_584_);
v_fileMap_588_ = lean_ctor_get(v_toCommandContextInfo_587_, 2);
lean_inc_ref(v_fileMap_588_);
lean_dec_ref(v_toCommandContextInfo_587_);
v___x_589_ = l_Lean_FileMap_toPosition(v_fileMap_588_, v_pos_585_);
v_line_590_ = lean_ctor_get(v___x_589_, 0);
v_column_591_ = lean_ctor_get(v___x_589_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_614_ == 0)
{
v___x_593_ = v___x_589_;
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_column_591_);
lean_inc(v_line_590_);
lean_dec(v___x_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_595_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_596_ = l_Nat_reprFast(v_line_590_);
v___x_597_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
if (v_isShared_594_ == 0)
{
lean_ctor_set_tag(v___x_593_, 5);
lean_ctor_set(v___x_593_, 1, v___x_597_);
lean_ctor_set(v___x_593_, 0, v___x_595_);
v___x_599_ = v___x_593_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___x_597_);
v___x_599_ = v_reuseFailAlloc_613_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v_pos_606_; 
v___x_600_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
v___x_601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l_Nat_reprFast(v_column_591_);
v___x_603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
v___x_604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_601_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v_pos_606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_pos_606_, 0, v___x_604_);
lean_ctor_set(v_pos_606_, 1, v___x_605_);
switch(lean_obj_tag(v_info_586_))
{
case 0:
{
return v_pos_606_;
}
case 1:
{
uint8_t v_canonical_610_; 
v_canonical_610_ = lean_ctor_get_uint8(v_info_586_, sizeof(void*)*2);
if (v_canonical_610_ == 1)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9));
v___x_612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_612_, 0, v_pos_606_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
return v___x_612_;
}
else
{
goto v___jp_607_;
}
}
default: 
{
goto v___jp_607_;
}
}
v___jp_607_:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7));
v___x_609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_609_, 0, v_pos_606_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
return v___x_609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(lean_object* v_ctx_615_, lean_object* v_pos_616_, lean_object* v_info_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_615_, v_pos_616_, v_info_617_);
lean_dec(v_info_617_);
lean_dec(v_pos_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(lean_object* v_ctx_622_, lean_object* v_stx_623_){
_start:
{
lean_object* v___y_625_; lean_object* v___y_626_; uint8_t v___x_634_; lean_object* v___y_636_; lean_object* v___x_639_; 
v___x_634_ = 0;
v___x_639_ = l_Lean_Syntax_getPos_x3f(v_stx_623_, v___x_634_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v___x_640_; 
v___x_640_ = lean_unsigned_to_nat(0u);
v___y_636_ = v___x_640_;
goto v___jp_635_;
}
else
{
lean_object* v_val_641_; 
v_val_641_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_val_641_);
lean_dec_ref_known(v___x_639_, 1);
v___y_636_ = v_val_641_;
goto v___jp_635_;
}
v___jp_624_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_627_ = l_Lean_Syntax_getHeadInfo(v_stx_623_);
lean_inc_ref(v_ctx_622_);
v___x_628_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_622_, v___y_625_, v___x_627_);
lean_dec(v___x_627_);
lean_dec(v___y_625_);
v___x_629_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = l_Lean_Syntax_getTailInfo(v_stx_623_);
v___x_632_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_622_, v___y_626_, v___x_631_);
lean_dec(v___x_631_);
lean_dec(v___y_626_);
v___x_633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_630_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
return v___x_633_;
}
v___jp_635_:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_Syntax_getTailPos_x3f(v_stx_623_, v___x_634_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_inc(v___y_636_);
v___y_625_ = v___y_636_;
v___y_626_ = v___y_636_;
goto v___jp_624_;
}
else
{
lean_object* v_val_638_; 
v_val_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_val_638_);
lean_dec_ref_known(v___x_637_, 1);
v___y_625_ = v___y_636_;
v___y_626_ = v_val_638_;
goto v___jp_624_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(lean_object* v_ctx_642_, lean_object* v_stx_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_642_, v_stx_643_);
lean_dec(v_stx_643_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(lean_object* v_ctx_648_, lean_object* v_info_649_){
_start:
{
lean_object* v_elaborator_650_; lean_object* v_stx_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_666_; 
v_elaborator_650_ = lean_ctor_get(v_info_649_, 0);
v_stx_651_ = lean_ctor_get(v_info_649_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_info_649_);
if (v_isSharedCheck_666_ == 0)
{
v___x_653_ = v_info_649_;
v_isShared_654_ = v_isSharedCheck_666_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_stx_651_);
lean_inc(v_elaborator_650_);
lean_dec(v_info_649_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_666_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
uint8_t v___x_655_; 
v___x_655_ = l_Lean_Name_isAnonymous(v_elaborator_650_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_656_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_648_, v_stx_651_);
lean_dec(v_stx_651_);
v___x_657_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 5);
lean_ctor_set(v___x_653_, 1, v___x_657_);
lean_ctor_set(v___x_653_, 0, v___x_656_);
v___x_659_ = v___x_653_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_657_);
v___x_659_ = v_reuseFailAlloc_664_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
uint8_t v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_660_ = 1;
v___x_661_ = l_Lean_Name_toString(v_elaborator_650_, v___x_660_);
v___x_662_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
v___x_663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_659_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
return v___x_663_;
}
}
else
{
lean_object* v___x_665_; 
lean_del_object(v___x_653_);
lean_dec(v_elaborator_650_);
v___x_665_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_648_, v_stx_651_);
lean_dec(v_stx_651_);
return v___x_665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object* v_info_667_, lean_object* v_ctx_668_, lean_object* v_x_669_){
_start:
{
lean_object* v_lctx_671_; lean_object* v___x_672_; 
v_lctx_671_ = lean_ctor_get(v_info_667_, 1);
lean_inc_ref(v_lctx_671_);
lean_dec_ref(v_info_667_);
v___x_672_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_668_, v_lctx_671_, v_x_669_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(lean_object* v_info_673_, lean_object* v_ctx_674_, lean_object* v_x_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_673_, v_ctx_674_, v_x_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM(lean_object* v_00_u03b1_678_, lean_object* v_info_679_, lean_object* v_ctx_680_, lean_object* v_x_681_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_679_, v_ctx_680_, v_x_681_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___boxed(lean_object* v_00_u03b1_684_, lean_object* v_info_685_, lean_object* v_ctx_686_, lean_object* v_x_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Elab_TermInfo_runMetaM(v_00_u03b1_684_, v_info_685_, v_ctx_686_, v_x_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0(lean_object* v_ctx_704_, lean_object* v_toElabInfo_705_, lean_object* v_expr_706_, uint8_t v_isBinder_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v_a_728_; lean_object* v___y_738_; uint8_t v___y_739_; lean_object* v___y_742_; lean_object* v_a_743_; lean_object* v___x_746_; 
lean_inc(v___y_711_);
lean_inc_ref(v___y_710_);
lean_inc(v___y_709_);
lean_inc_ref(v___y_708_);
lean_inc_ref(v_expr_706_);
v___x_746_ = lean_infer_type(v_expr_706_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_748_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_748_ = l_Lean_Meta_ppExpr(v_a_747_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
v_a_728_ = v_a_749_;
goto v___jp_727_;
}
else
{
lean_object* v_a_750_; 
v_a_750_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_750_);
v___y_742_ = v___x_748_;
v_a_743_ = v_a_750_;
goto v___jp_741_;
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
v_a_751_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_746_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_746_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
lean_inc(v_a_751_);
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
v___y_742_ = v___x_756_;
v_a_743_ = v_a_751_;
goto v___jp_741_;
}
}
}
v___jp_713_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
lean_inc_ref(v___y_716_);
v___x_717_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_717_, 0, v___y_716_);
v___x_718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_718_, 0, v___y_714_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v___y_715_);
v___x_722_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_704_, v_toElabInfo_705_);
v___x_725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
v___jp_727_:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Meta_ppExpr(v_expr_706_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
v___x_731_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__3));
v___x_732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v_a_730_);
v___x_733_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
v___x_734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
if (v_isBinder_707_ == 0)
{
lean_object* v___x_735_; 
v___x_735_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__6));
v___y_714_ = v___x_734_;
v___y_715_ = v_a_728_;
v___y_716_ = v___x_735_;
goto v___jp_713_;
}
else
{
lean_object* v___x_736_; 
v___x_736_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__7));
v___y_714_ = v___x_734_;
v___y_715_ = v_a_728_;
v___y_716_ = v___x_736_;
goto v___jp_713_;
}
}
else
{
lean_dec(v_a_728_);
lean_dec_ref(v_toElabInfo_705_);
lean_dec_ref(v_ctx_704_);
return v___x_729_;
}
}
v___jp_737_:
{
if (v___y_739_ == 0)
{
lean_object* v___x_740_; 
lean_dec_ref(v___y_738_);
v___x_740_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__9));
v_a_728_ = v___x_740_;
goto v___jp_727_;
}
else
{
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec_ref(v_expr_706_);
lean_dec_ref(v_toElabInfo_705_);
lean_dec_ref(v_ctx_704_);
return v___y_738_;
}
}
v___jp_741_:
{
uint8_t v___x_744_; 
v___x_744_ = l_Lean_Exception_isInterrupt(v_a_743_);
if (v___x_744_ == 0)
{
uint8_t v___x_745_; 
v___x_745_ = l_Lean_Exception_isRuntime(v_a_743_);
v___y_738_ = v___y_742_;
v___y_739_ = v___x_745_;
goto v___jp_737_;
}
else
{
lean_dec_ref(v_a_743_);
v___y_738_ = v___y_742_;
v___y_739_ = v___x_744_;
goto v___jp_737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0___boxed(lean_object* v_ctx_759_, lean_object* v_toElabInfo_760_, lean_object* v_expr_761_, lean_object* v_isBinder_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
uint8_t v_isBinder_boxed_768_; lean_object* v_res_769_; 
v_isBinder_boxed_768_ = lean_unbox(v_isBinder_762_);
v_res_769_ = l_Lean_Elab_TermInfo_format___lam__0(v_ctx_759_, v_toElabInfo_760_, v_expr_761_, v_isBinder_boxed_768_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format(lean_object* v_ctx_770_, lean_object* v_info_771_){
_start:
{
lean_object* v_toElabInfo_773_; lean_object* v_expr_774_; uint8_t v_isBinder_775_; lean_object* v___x_776_; lean_object* v___f_777_; lean_object* v___x_778_; 
v_toElabInfo_773_ = lean_ctor_get(v_info_771_, 0);
v_expr_774_ = lean_ctor_get(v_info_771_, 3);
v_isBinder_775_ = lean_ctor_get_uint8(v_info_771_, sizeof(void*)*4);
v___x_776_ = lean_box(v_isBinder_775_);
lean_inc_ref(v_expr_774_);
lean_inc_ref(v_toElabInfo_773_);
lean_inc_ref(v_ctx_770_);
v___f_777_ = lean_alloc_closure((void*)(l_Lean_Elab_TermInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_777_, 0, v_ctx_770_);
lean_closure_set(v___f_777_, 1, v_toElabInfo_773_);
lean_closure_set(v___f_777_, 2, v_expr_774_);
lean_closure_set(v___f_777_, 3, v___x_776_);
v___x_778_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_771_, v_ctx_770_, v___f_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___boxed(lean_object* v_ctx_779_, lean_object* v_info_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Elab_TermInfo_format(v_ctx_779_, v_info_780_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialTermInfo_format(lean_object* v_ctx_786_, lean_object* v_info_787_){
_start:
{
lean_object* v_toElabInfo_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_toElabInfo_788_ = lean_ctor_get(v_info_787_, 0);
lean_inc_ref(v_toElabInfo_788_);
lean_dec_ref(v_info_787_);
v___x_789_ = ((lean_object*)(l_Lean_Elab_PartialTermInfo_format___closed__1));
v___x_790_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_786_, v_toElabInfo_788_);
v___x_791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_789_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(lean_object* v_x_798_){
_start:
{
if (lean_obj_tag(v_x_798_) == 0)
{
lean_object* v___x_799_; 
v___x_799_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_799_;
}
else
{
lean_object* v_val_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_810_; 
v_val_800_ = lean_ctor_get(v_x_798_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v_x_798_);
if (v_isSharedCheck_810_ == 0)
{
v___x_802_ = v_x_798_;
v_isShared_803_ = v_isSharedCheck_810_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_val_800_);
lean_dec(v_x_798_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_810_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_804_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_805_ = lean_expr_dbg_to_string(v_val_800_);
lean_dec(v_val_800_);
if (v_isShared_803_ == 0)
{
lean_ctor_set_tag(v___x_802_, 3);
lean_ctor_set(v___x_802_, 0, v___x_805_);
v___x_807_ = v___x_802_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_809_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; 
v___x_808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_804_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
return v___x_808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0(lean_object* v_ctx_817_, lean_object* v_lctx_818_, lean_object* v_stx_819_, lean_object* v_expectedType_x3f_820_, lean_object* v_info_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_846_; 
v___x_827_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_817_, v_lctx_818_, v_stx_819_);
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_846_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_846_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_846_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_832_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__1));
v___x_833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v_a_828_);
v___x_834_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_820_);
v___x_837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = l_Lean_Elab_CompletionInfo_stx(v_info_821_);
v___x_841_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_817_, v___x_840_);
lean_dec(v___x_840_);
v___x_842_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_839_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_842_);
v___x_844_ = v___x_830_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___boxed(lean_object* v_ctx_847_, lean_object* v_lctx_848_, lean_object* v_stx_849_, lean_object* v_expectedType_x3f_850_, lean_object* v_info_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Elab_CompletionInfo_format___lam__0(v_ctx_847_, v_lctx_848_, v_stx_849_, v_expectedType_x3f_850_, v_info_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec_ref(v_info_851_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format(lean_object* v_ctx_864_, lean_object* v_info_865_){
_start:
{
switch(lean_obj_tag(v_info_865_))
{
case 0:
{
lean_object* v_termInfo_867_; lean_object* v_expectedType_x3f_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_889_; 
v_termInfo_867_ = lean_ctor_get(v_info_865_, 0);
v_expectedType_x3f_868_ = lean_ctor_get(v_info_865_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v_info_865_);
if (v_isSharedCheck_889_ == 0)
{
v___x_870_ = v_info_865_;
v_isShared_871_ = v_isSharedCheck_889_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_expectedType_x3f_868_);
lean_inc(v_termInfo_867_);
lean_dec(v_info_865_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_889_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_Elab_TermInfo_format(v_ctx_864_, v_termInfo_867_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_888_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_888_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_888_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_888_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_877_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__1));
if (v_isShared_871_ == 0)
{
lean_ctor_set_tag(v___x_870_, 5);
lean_ctor_set(v___x_870_, 1, v_a_873_);
lean_ctor_set(v___x_870_, 0, v___x_877_);
v___x_879_ = v___x_870_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_a_873_);
v___x_879_ = v_reuseFailAlloc_887_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_880_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_868_);
v___x_883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_883_);
v___x_885_ = v___x_875_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
lean_del_object(v___x_870_);
lean_dec(v_expectedType_x3f_868_);
return v___x_872_;
}
}
}
case 1:
{
lean_object* v_stx_890_; lean_object* v_lctx_891_; lean_object* v_expectedType_x3f_892_; lean_object* v___f_893_; lean_object* v___x_894_; 
v_stx_890_ = lean_ctor_get(v_info_865_, 0);
lean_inc(v_stx_890_);
v_lctx_891_ = lean_ctor_get(v_info_865_, 2);
lean_inc_ref_n(v_lctx_891_, 2);
v_expectedType_x3f_892_ = lean_ctor_get(v_info_865_, 3);
lean_inc(v_expectedType_x3f_892_);
lean_inc_ref(v_ctx_864_);
v___f_893_ = lean_alloc_closure((void*)(l_Lean_Elab_CompletionInfo_format___lam__0___boxed), 10, 5);
lean_closure_set(v___f_893_, 0, v_ctx_864_);
lean_closure_set(v___f_893_, 1, v_lctx_891_);
lean_closure_set(v___f_893_, 2, v_stx_890_);
lean_closure_set(v___f_893_, 3, v_expectedType_x3f_892_);
lean_closure_set(v___f_893_, 4, v_info_865_);
v___x_894_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_864_, v_lctx_891_, v___f_893_);
return v___x_894_;
}
default: 
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_895_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__3));
v___x_896_ = l_Lean_Elab_CompletionInfo_stx(v_info_865_);
lean_dec_ref(v_info_865_);
v___x_897_ = lean_box(0);
v___x_898_ = 0;
lean_inc(v___x_896_);
v___x_899_ = l_Lean_Syntax_formatStx(v___x_896_, v___x_897_, v___x_898_);
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_895_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_864_, v___x_896_);
lean_dec(v___x_896_);
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___boxed(lean_object* v_ctx_906_, lean_object* v_info_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_Elab_CompletionInfo_format(v_ctx_906_, v_info_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format(lean_object* v_ctx_913_, lean_object* v_info_914_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_916_ = ((lean_object*)(l_Lean_Elab_CommandInfo_format___closed__1));
v___x_917_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_913_, v_info_914_);
v___x_918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format___boxed(lean_object* v_ctx_920_, lean_object* v_info_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Elab_CommandInfo_format(v_ctx_920_, v_info_921_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format(lean_object* v_ctx_927_, lean_object* v_info_928_){
_start:
{
lean_object* v_stx_930_; lean_object* v_optionName_931_; lean_object* v___x_932_; uint8_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_stx_930_ = lean_ctor_get(v_info_928_, 0);
lean_inc(v_stx_930_);
v_optionName_931_ = lean_ctor_get(v_info_928_, 1);
lean_inc(v_optionName_931_);
lean_dec_ref(v_info_928_);
v___x_932_ = ((lean_object*)(l_Lean_Elab_OptionInfo_format___closed__1));
v___x_933_ = 1;
v___x_934_ = l_Lean_Name_toString(v_optionName_931_, v___x_933_);
v___x_935_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
v___x_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_932_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_927_, v_stx_930_);
lean_dec(v_stx_930_);
v___x_940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format___boxed(lean_object* v_ctx_942_, lean_object* v_info_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Elab_OptionInfo_format(v_ctx_942_, v_info_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format(lean_object* v_ctx_949_, lean_object* v_info_950_){
_start:
{
lean_object* v_stx_952_; lean_object* v_errorName_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_969_; 
v_stx_952_ = lean_ctor_get(v_info_950_, 0);
v_errorName_953_ = lean_ctor_get(v_info_950_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_info_950_);
if (v_isSharedCheck_969_ == 0)
{
v___x_955_ = v_info_950_;
v_isShared_956_ = v_isSharedCheck_969_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_errorName_953_);
lean_inc(v_stx_952_);
lean_dec(v_info_950_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_969_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; uint8_t v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_957_ = ((lean_object*)(l_Lean_Elab_ErrorNameInfo_format___closed__1));
v___x_958_ = 1;
v___x_959_ = l_Lean_Name_toString(v_errorName_953_, v___x_958_);
v___x_960_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
if (v_isShared_956_ == 0)
{
lean_ctor_set_tag(v___x_955_, 5);
lean_ctor_set(v___x_955_, 1, v___x_960_);
lean_ctor_set(v___x_955_, 0, v___x_957_);
v___x_962_ = v___x_955_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v___x_960_);
v___x_962_ = v_reuseFailAlloc_968_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_963_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_949_, v_stx_952_);
lean_dec(v_stx_952_);
v___x_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
return v___x_967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format___boxed(lean_object* v_ctx_970_, lean_object* v_info_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_970_, v_info_971_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0(lean_object* v_val_980_, lean_object* v_fieldName_981_, lean_object* v_ctx_982_, lean_object* v_stx_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; 
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc_ref(v_val_980_);
v___x_989_ = lean_infer_type(v_val_980_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_991_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
v___x_991_ = l_Lean_Meta_ppExpr(v_a_990_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1022_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1022_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1022_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_Meta_ppExpr(v_val_980_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1021_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1021_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1021_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; uint8_t v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1001_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__1));
v___x_1002_ = 1;
v___x_1003_ = l_Lean_Name_toString(v_fieldName_981_, v___x_1002_);
if (v_isShared_995_ == 0)
{
lean_ctor_set_tag(v___x_994_, 3);
lean_ctor_set(v___x_994_, 0, v___x_1003_);
v___x_1005_ = v___x_994_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1001_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v_a_992_);
v___x_1010_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__3));
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v_a_997_);
v___x_1013_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_982_, v_stx_983_);
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1016_);
v___x_1018_ = v___x_999_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
else
{
lean_del_object(v___x_994_);
lean_dec(v_a_992_);
lean_dec_ref(v_ctx_982_);
lean_dec(v_fieldName_981_);
return v___x_996_;
}
}
}
else
{
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec_ref(v_ctx_982_);
lean_dec(v_fieldName_981_);
lean_dec_ref(v_val_980_);
return v___x_991_;
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec_ref(v_ctx_982_);
lean_dec(v_fieldName_981_);
lean_dec_ref(v_val_980_);
v_a_1023_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_989_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_989_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0___boxed(lean_object* v_val_1031_, lean_object* v_fieldName_1032_, lean_object* v_ctx_1033_, lean_object* v_stx_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_Elab_FieldInfo_format___lam__0(v_val_1031_, v_fieldName_1032_, v_ctx_1033_, v_stx_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v_stx_1034_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format(lean_object* v_ctx_1041_, lean_object* v_info_1042_){
_start:
{
lean_object* v_fieldName_1044_; lean_object* v_lctx_1045_; lean_object* v_val_1046_; lean_object* v_stx_1047_; lean_object* v___f_1048_; lean_object* v___x_1049_; 
v_fieldName_1044_ = lean_ctor_get(v_info_1042_, 1);
lean_inc(v_fieldName_1044_);
v_lctx_1045_ = lean_ctor_get(v_info_1042_, 2);
lean_inc_ref(v_lctx_1045_);
v_val_1046_ = lean_ctor_get(v_info_1042_, 3);
lean_inc_ref(v_val_1046_);
v_stx_1047_ = lean_ctor_get(v_info_1042_, 4);
lean_inc(v_stx_1047_);
lean_dec_ref(v_info_1042_);
lean_inc_ref(v_ctx_1041_);
v___f_1048_ = lean_alloc_closure((void*)(l_Lean_Elab_FieldInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1048_, 0, v_val_1046_);
lean_closure_set(v___f_1048_, 1, v_fieldName_1044_);
lean_closure_set(v___f_1048_, 2, v_ctx_1041_);
lean_closure_set(v___f_1048_, 3, v_stx_1047_);
v___x_1049_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1041_, v_lctx_1045_, v___f_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___boxed(lean_object* v_ctx_1050_, lean_object* v_info_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Elab_FieldInfo_format(v_ctx_1050_, v_info_1051_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(lean_object* v_pre_1054_, lean_object* v_x_1055_, lean_object* v_x_1056_){
_start:
{
if (lean_obj_tag(v_x_1056_) == 0)
{
lean_dec(v_pre_1054_);
return v_x_1055_;
}
else
{
lean_object* v_head_1057_; lean_object* v_tail_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1067_; 
v_head_1057_ = lean_ctor_get(v_x_1056_, 0);
v_tail_1058_ = lean_ctor_get(v_x_1056_, 1);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_x_1056_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1060_ = v_x_1056_;
v_isShared_1061_ = v_isSharedCheck_1067_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_tail_1058_);
lean_inc(v_head_1057_);
lean_dec(v_x_1056_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1067_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
lean_inc(v_pre_1054_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set_tag(v___x_1060_, 5);
lean_ctor_set(v___x_1060_, 1, v_pre_1054_);
lean_ctor_set(v___x_1060_, 0, v_x_1055_);
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_x_1055_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_pre_1054_);
v___x_1063_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v_head_1057_);
v_x_1055_ = v___x_1064_;
v_x_1056_ = v_tail_1058_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(lean_object* v_pre_1068_, lean_object* v_x_1069_){
_start:
{
if (lean_obj_tag(v_x_1069_) == 0)
{
lean_object* v___x_1070_; 
lean_dec(v_pre_1068_);
v___x_1070_ = lean_box(0);
return v___x_1070_;
}
else
{
lean_object* v_head_1071_; lean_object* v_tail_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1080_; 
v_head_1071_ = lean_ctor_get(v_x_1069_, 0);
v_tail_1072_ = lean_ctor_get(v_x_1069_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_x_1069_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1074_ = v_x_1069_;
v_isShared_1075_ = v_isSharedCheck_1080_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_tail_1072_);
lean_inc(v_head_1071_);
lean_dec(v_x_1069_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1080_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
lean_inc(v_pre_1068_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set_tag(v___x_1074_, 5);
lean_ctor_set(v___x_1074_, 1, v_head_1071_);
lean_ctor_set(v___x_1074_, 0, v_pre_1068_);
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_pre_1068_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_head_1071_);
v___x_1077_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(v_pre_1068_, v___x_1077_, v_tail_1072_);
return v___x_1078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
if (lean_obj_tag(v_x_1081_) == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = l_List_reverse___redArg(v_x_1082_);
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
return v___x_1089_;
}
else
{
lean_object* v_head_1090_; lean_object* v_tail_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1109_; 
v_head_1090_ = lean_ctor_get(v_x_1081_, 0);
v_tail_1091_ = lean_ctor_get(v_x_1081_, 1);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_x_1081_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1093_ = v_x_1081_;
v_isShared_1094_ = v_isSharedCheck_1109_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_tail_1091_);
lean_inc(v_head_1090_);
lean_dec(v_x_1081_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1109_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_Meta_ppGoal(v_head_1090_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v_head_1090_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1098_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v_x_1082_);
lean_ctor_set(v___x_1093_, 0, v_a_1096_);
v___x_1098_ = v___x_1093_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1096_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_x_1082_);
v___x_1098_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
v_x_1081_ = v_tail_1091_;
v_x_1082_ = v___x_1098_;
goto _start;
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_del_object(v___x_1093_);
lean_dec(v_tail_1091_);
lean_dec(v_x_1082_);
v_a_1101_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1095_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1095_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(lean_object* v_x_1110_, lean_object* v_x_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_x_1110_, v_x_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0(lean_object* v_goals_1121_, lean_object* v___x_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_goals_1121_, v___x_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1138_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1131_ = v___x_1128_;
v_isShared_1132_ = v_isSharedCheck_1138_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1128_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1138_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1133_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1134_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1133_, v_a_1129_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1134_);
v___x_1136_ = v___x_1131_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
v_a_1139_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1128_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1128_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(lean_object* v_goals_1147_, lean_object* v___x_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0(v_goals_1147_, v___x_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
return v_res_1154_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0(void){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1155_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__0, &l_Lean_Elab_ContextInfo_ppGoals___closed__0_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = lean_unsigned_to_nat(32u);
v___x_1159_ = lean_mk_empty_array_with_capacity(v___x_1158_);
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
return v___x_1160_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3(void){
_start:
{
size_t v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1161_ = ((size_t)5ULL);
v___x_1162_ = lean_unsigned_to_nat(0u);
v___x_1163_ = lean_unsigned_to_nat(32u);
v___x_1164_ = lean_mk_empty_array_with_capacity(v___x_1163_);
v___x_1165_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_1166_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v___x_1164_);
lean_ctor_set(v___x_1166_, 2, v___x_1162_);
lean_ctor_set(v___x_1166_, 3, v___x_1162_);
lean_ctor_set_usize(v___x_1166_, 4, v___x_1161_);
return v___x_1166_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1167_ = lean_box(1);
v___x_1168_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_1169_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__1, &l_Lean_Elab_ContextInfo_ppGoals___closed__1_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1);
v___x_1170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set(v___x_1170_, 1, v___x_1168_);
lean_ctor_set(v___x_1170_, 2, v___x_1167_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object* v_ctx_1174_, lean_object* v_goals_1175_){
_start:
{
uint8_t v___x_1177_; 
v___x_1177_ = l_List_isEmpty___redArg(v_goals_1175_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___f_1180_; lean_object* v___x_1181_; 
v___x_1178_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__4, &l_Lean_Elab_ContextInfo_ppGoals___closed__4_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4);
v___x_1179_ = lean_box(0);
v___f_1180_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1180_, 0, v_goals_1175_);
lean_closure_set(v___f_1180_, 1, v___x_1179_);
v___x_1181_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1174_, v___x_1178_, v___f_1180_);
return v___x_1181_;
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec(v_goals_1175_);
lean_dec_ref(v_ctx_1174_);
v___x_1182_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___closed__6));
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object* v_ctx_1184_, lean_object* v_goals_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctx_1184_, v_goals_1185_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format(lean_object* v_ctx_1197_, lean_object* v_info_1198_){
_start:
{
lean_object* v_toCommandContextInfo_1200_; lean_object* v_parentDecl_x3f_1201_; lean_object* v_autoImplicits_1202_; lean_object* v_env_1203_; lean_object* v_cmdEnv_x3f_1204_; lean_object* v_fileMap_1205_; lean_object* v_options_1206_; lean_object* v_currNamespace_1207_; lean_object* v_openDecls_1208_; lean_object* v_ngen_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1251_; 
v_toCommandContextInfo_1200_ = lean_ctor_get(v_ctx_1197_, 0);
lean_inc_ref(v_toCommandContextInfo_1200_);
v_parentDecl_x3f_1201_ = lean_ctor_get(v_ctx_1197_, 1);
v_autoImplicits_1202_ = lean_ctor_get(v_ctx_1197_, 2);
v_env_1203_ = lean_ctor_get(v_toCommandContextInfo_1200_, 0);
v_cmdEnv_x3f_1204_ = lean_ctor_get(v_toCommandContextInfo_1200_, 1);
v_fileMap_1205_ = lean_ctor_get(v_toCommandContextInfo_1200_, 2);
v_options_1206_ = lean_ctor_get(v_toCommandContextInfo_1200_, 4);
v_currNamespace_1207_ = lean_ctor_get(v_toCommandContextInfo_1200_, 5);
v_openDecls_1208_ = lean_ctor_get(v_toCommandContextInfo_1200_, 6);
v_ngen_1209_ = lean_ctor_get(v_toCommandContextInfo_1200_, 7);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_toCommandContextInfo_1200_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; 
v_unused_1252_ = lean_ctor_get(v_toCommandContextInfo_1200_, 3);
lean_dec(v_unused_1252_);
v___x_1211_ = v_toCommandContextInfo_1200_;
v_isShared_1212_ = v_isSharedCheck_1251_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_ngen_1209_);
lean_inc(v_openDecls_1208_);
lean_inc(v_currNamespace_1207_);
lean_inc(v_options_1206_);
lean_inc(v_fileMap_1205_);
lean_inc(v_cmdEnv_x3f_1204_);
lean_inc(v_env_1203_);
lean_dec(v_toCommandContextInfo_1200_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1251_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v_toElabInfo_1213_; lean_object* v_mctxBefore_1214_; lean_object* v_goalsBefore_1215_; lean_object* v_mctxAfter_1216_; lean_object* v_goalsAfter_1217_; lean_object* v___x_1219_; 
v_toElabInfo_1213_ = lean_ctor_get(v_info_1198_, 0);
lean_inc_ref(v_toElabInfo_1213_);
v_mctxBefore_1214_ = lean_ctor_get(v_info_1198_, 1);
lean_inc_ref(v_mctxBefore_1214_);
v_goalsBefore_1215_ = lean_ctor_get(v_info_1198_, 2);
lean_inc(v_goalsBefore_1215_);
v_mctxAfter_1216_ = lean_ctor_get(v_info_1198_, 3);
lean_inc_ref(v_mctxAfter_1216_);
v_goalsAfter_1217_ = lean_ctor_get(v_info_1198_, 4);
lean_inc(v_goalsAfter_1217_);
lean_dec_ref(v_info_1198_);
lean_inc_ref(v_ngen_1209_);
lean_inc(v_openDecls_1208_);
lean_inc(v_currNamespace_1207_);
lean_inc_ref(v_options_1206_);
lean_inc_ref(v_fileMap_1205_);
lean_inc(v_cmdEnv_x3f_1204_);
lean_inc_ref(v_env_1203_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 3, v_mctxBefore_1214_);
v___x_1219_ = v___x_1211_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_env_1203_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_cmdEnv_x3f_1204_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_fileMap_1205_);
lean_ctor_set(v_reuseFailAlloc_1250_, 3, v_mctxBefore_1214_);
lean_ctor_set(v_reuseFailAlloc_1250_, 4, v_options_1206_);
lean_ctor_set(v_reuseFailAlloc_1250_, 5, v_currNamespace_1207_);
lean_ctor_set(v_reuseFailAlloc_1250_, 6, v_openDecls_1208_);
lean_ctor_set(v_reuseFailAlloc_1250_, 7, v_ngen_1209_);
v___x_1219_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v_ctxB_1220_; lean_object* v___x_1221_; 
lean_inc_ref(v_autoImplicits_1202_);
lean_inc(v_parentDecl_x3f_1201_);
v_ctxB_1220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxB_1220_, 0, v___x_1219_);
lean_ctor_set(v_ctxB_1220_, 1, v_parentDecl_x3f_1201_);
lean_ctor_set(v_ctxB_1220_, 2, v_autoImplicits_1202_);
v___x_1221_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxB_1220_, v_goalsBefore_1215_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1223_; lean_object* v_ctxA_1224_; lean_object* v___x_1225_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___x_1221_, 1);
v___x_1223_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1223_, 0, v_env_1203_);
lean_ctor_set(v___x_1223_, 1, v_cmdEnv_x3f_1204_);
lean_ctor_set(v___x_1223_, 2, v_fileMap_1205_);
lean_ctor_set(v___x_1223_, 3, v_mctxAfter_1216_);
lean_ctor_set(v___x_1223_, 4, v_options_1206_);
lean_ctor_set(v___x_1223_, 5, v_currNamespace_1207_);
lean_ctor_set(v___x_1223_, 6, v_openDecls_1208_);
lean_ctor_set(v___x_1223_, 7, v_ngen_1209_);
lean_inc_ref(v_autoImplicits_1202_);
lean_inc(v_parentDecl_x3f_1201_);
v_ctxA_1224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxA_1224_, 0, v___x_1223_);
lean_ctor_set(v_ctxA_1224_, 1, v_parentDecl_x3f_1201_);
lean_ctor_set(v_ctxA_1224_, 2, v_autoImplicits_1202_);
v___x_1225_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxA_1224_, v_goalsAfter_1217_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1249_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1249_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1249_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v_stx_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1247_; 
v_stx_1230_ = lean_ctor_get(v_toElabInfo_1213_, 1);
lean_inc(v_stx_1230_);
v___x_1231_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__1));
v___x_1232_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1197_, v_toElabInfo_1213_);
v___x_1233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = lean_box(0);
v___x_1237_ = 0;
v___x_1238_ = l_Lean_Syntax_formatStx(v_stx_1230_, v___x_1236_, v___x_1237_);
v___x_1239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1235_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__3));
v___x_1241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v_a_1222_);
v___x_1243_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__5));
v___x_1244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1242_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
lean_ctor_set(v___x_1245_, 1, v_a_1226_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1245_);
v___x_1247_ = v___x_1228_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
else
{
lean_dec(v_a_1222_);
lean_dec_ref(v_toElabInfo_1213_);
lean_dec_ref(v_ctx_1197_);
return v___x_1225_;
}
}
else
{
lean_dec(v_goalsAfter_1217_);
lean_dec_ref(v_mctxAfter_1216_);
lean_dec_ref(v_toElabInfo_1213_);
lean_dec_ref(v_ngen_1209_);
lean_dec(v_openDecls_1208_);
lean_dec(v_currNamespace_1207_);
lean_dec_ref(v_options_1206_);
lean_dec_ref(v_fileMap_1205_);
lean_dec(v_cmdEnv_x3f_1204_);
lean_dec_ref(v_env_1203_);
lean_dec_ref(v_ctx_1197_);
return v___x_1221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format___boxed(lean_object* v_ctx_1253_, lean_object* v_info_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_Elab_TacticInfo_format(v_ctx_1253_, v_info_1254_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object* v_ctx_1263_, lean_object* v_info_1264_){
_start:
{
lean_object* v_lctx_1266_; lean_object* v_stx_1267_; lean_object* v_output_1268_; lean_object* v___x_1269_; lean_object* v_a_1270_; lean_object* v___x_1271_; lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1284_; 
v_lctx_1266_ = lean_ctor_get(v_info_1264_, 0);
lean_inc_ref_n(v_lctx_1266_, 2);
v_stx_1267_ = lean_ctor_get(v_info_1264_, 1);
lean_inc(v_stx_1267_);
v_output_1268_ = lean_ctor_get(v_info_1264_, 2);
lean_inc(v_output_1268_);
lean_dec_ref(v_info_1264_);
v___x_1269_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1263_, v_lctx_1266_, v_stx_1267_);
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref(v___x_1269_);
v___x_1271_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1263_, v_lctx_1266_, v_output_1268_);
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1284_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1284_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1276_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__1));
v___x_1277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v_a_1270_);
v___x_1278_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__3));
v___x_1279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
lean_ctor_set(v___x_1280_, 1, v_a_1272_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1280_);
v___x_1282_ = v___x_1274_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object* v_ctx_1285_, lean_object* v_info_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1285_, v_info_1286_);
lean_dec_ref(v_ctx_1285_);
return v_res_1288_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__0(void){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1289_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__1(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__0, &l_Lean_Elab_UserWidgetInfo_format___closed__0_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__0);
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
return v___x_1291_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__2(void){
_start:
{
uint8_t v___x_1292_; size_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1292_ = 1;
v___x_1293_ = ((size_t)0ULL);
v___x_1294_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__1, &l_Lean_Elab_UserWidgetInfo_format___closed__1_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__1);
v___x_1295_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
lean_ctor_set_usize(v___x_1295_, 2, v___x_1293_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*3, v___x_1292_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_UserWidgetInfo_format(lean_object* v_info_1299_){
_start:
{
lean_object* v_toWidgetInstance_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1329_; 
v_toWidgetInstance_1300_ = lean_ctor_get(v_info_1299_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_info_1299_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v_info_1299_, 1);
lean_dec(v_unused_1330_);
v___x_1302_ = v_info_1299_;
v_isShared_1303_ = v_isSharedCheck_1329_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_toWidgetInstance_1300_);
lean_dec(v_info_1299_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1329_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v_id_1304_; lean_object* v_props_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v_fst_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1327_; 
v_id_1304_ = lean_ctor_get(v_toWidgetInstance_1300_, 0);
lean_inc(v_id_1304_);
v_props_1305_ = lean_ctor_get(v_toWidgetInstance_1300_, 1);
lean_inc_ref(v_props_1305_);
lean_dec_ref(v_toWidgetInstance_1300_);
v___x_1306_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__2, &l_Lean_Elab_UserWidgetInfo_format___closed__2_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__2);
v___x_1307_ = lean_apply_1(v_props_1305_, v___x_1306_);
v_fst_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; 
v_unused_1328_ = lean_ctor_get(v___x_1307_, 1);
lean_dec(v_unused_1328_);
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1327_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_fst_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1327_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1312_ = ((lean_object*)(l_Lean_Elab_UserWidgetInfo_format___closed__4));
v___x_1313_ = 1;
v___x_1314_ = l_Lean_Name_toString(v_id_1304_, v___x_1313_);
v___x_1315_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set_tag(v___x_1310_, 5);
lean_ctor_set(v___x_1310_, 1, v___x_1315_);
lean_ctor_set(v___x_1310_, 0, v___x_1312_);
v___x_1317_ = v___x_1310_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1318_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
if (v_isShared_1303_ == 0)
{
lean_ctor_set_tag(v___x_1302_, 5);
lean_ctor_set(v___x_1302_, 1, v___x_1318_);
lean_ctor_set(v___x_1302_, 0, v___x_1317_);
v___x_1320_ = v___x_1302_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1321_ = lean_unsigned_to_nat(80u);
v___x_1322_ = l_Lean_Json_pretty(v_fst_1308_, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
v___x_1324_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1320_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
return v___x_1324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FVarAliasInfo_format(lean_object* v_info_1337_){
_start:
{
lean_object* v_userName_1338_; lean_object* v_id_1339_; lean_object* v_baseId_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_userName_1338_ = lean_ctor_get(v_info_1337_, 0);
lean_inc(v_userName_1338_);
v_id_1339_ = lean_ctor_get(v_info_1337_, 1);
lean_inc(v_id_1339_);
v_baseId_1340_ = lean_ctor_get(v_info_1337_, 2);
lean_inc(v_baseId_1340_);
lean_dec_ref(v_info_1337_);
v___x_1341_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__1));
v___x_1342_ = l_Lean_Name_eraseMacroScopes(v_userName_1338_);
lean_dec(v_userName_1338_);
v___x_1343_ = 1;
v___x_1344_ = l_Lean_Name_toString(v___x_1342_, v___x_1343_);
v___x_1345_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
v___x_1346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1341_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_1348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = l_Lean_Name_toString(v_id_1339_, v___x_1343_);
v___x_1350_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
v___x_1351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1348_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__3));
v___x_1353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = l_Lean_Name_toString(v_baseId_1340_, v___x_1343_);
v___x_1355_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
v___x_1356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1353_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format(lean_object* v_ctx_1360_, lean_object* v_info_1361_){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = ((lean_object*)(l_Lean_Elab_FieldRedeclInfo_format___closed__1));
v___x_1363_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1360_, v_info_1361_);
v___x_1364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1362_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format___boxed(lean_object* v_ctx_1365_, lean_object* v_info_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1365_, v_info_1366_);
lean_dec(v_info_1366_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f(lean_object* v_ppCtx_1370_, lean_object* v_info_1371_){
_start:
{
lean_object* v_mkDocString_x3f_1373_; 
v_mkDocString_x3f_1373_ = lean_ctor_get(v_info_1371_, 2);
lean_inc(v_mkDocString_x3f_1373_);
lean_dec_ref(v_info_1371_);
if (lean_obj_tag(v_mkDocString_x3f_1373_) == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_dec_ref(v_ppCtx_1370_);
v___x_1374_ = lean_box(0);
v___x_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
return v___x_1375_;
}
else
{
lean_object* v_val_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1408_; 
v_val_1376_ = lean_ctor_get(v_mkDocString_x3f_1373_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_mkDocString_x3f_1373_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1378_ = v_mkDocString_x3f_1373_;
v_isShared_1379_ = v_isSharedCheck_1408_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_val_1376_);
lean_dec(v_mkDocString_x3f_1373_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1408_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_apply_2(v_val_1376_, v_ppCtx_1370_, lean_box(0));
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1391_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1391_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1391_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v_a_1381_);
v___x_1386_ = v___x_1378_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1388_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1386_);
v___x_1388_ = v___x_1383_;
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
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1407_; 
v_a_1392_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1394_ = v___x_1380_;
v_isShared_1395_ = v_isSharedCheck_1407_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1380_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1407_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1396_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0));
v___x_1397_ = lean_io_error_to_string(v_a_1392_);
v___x_1398_ = lean_string_append(v___x_1396_, v___x_1397_);
lean_dec_ref(v___x_1397_);
v___x_1399_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1400_ = lean_string_append(v___x_1398_, v___x_1399_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1400_);
v___x_1402_ = v___x_1378_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1404_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set_tag(v___x_1394_, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1402_);
v___x_1404_ = v___x_1394_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___boxed(lean_object* v_ppCtx_1409_, lean_object* v_info_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_ppCtx_1409_, v_info_1410_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(lean_object* v_x_1413_, lean_object* v_x_1414_){
_start:
{
if (lean_obj_tag(v_x_1413_) == 0)
{
lean_object* v___x_1415_; 
v___x_1415_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_1415_;
}
else
{
lean_object* v_val_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1427_; 
v_val_1416_ = lean_ctor_get(v_x_1413_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_x_1413_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1418_ = v_x_1413_;
v_isShared_1419_ = v_isSharedCheck_1427_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_val_1416_);
lean_dec(v_x_1413_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1427_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1420_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_1421_ = l_String_quote(v_val_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set_tag(v___x_1418_, 3);
lean_ctor_set(v___x_1418_, 0, v___x_1421_);
v___x_1423_ = v___x_1418_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1420_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v___x_1425_ = l_Repr_addAppParen(v___x_1424_, v_x_1414_);
return v___x_1425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(lean_object* v_x_1428_, lean_object* v_x_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_x_1428_, v_x_1429_);
lean_dec(v_x_1429_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object* v_ctx_1445_, lean_object* v_info_1446_){
_start:
{
lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v_toTermInfo_1454_; lean_object* v_location_x3f_1455_; uint8_t v_explicit_1456_; lean_object* v___y_1458_; 
v_toTermInfo_1454_ = lean_ctor_get(v_info_1446_, 0);
lean_inc_ref(v_toTermInfo_1454_);
v_location_x3f_1455_ = lean_ctor_get(v_info_1446_, 1);
lean_inc(v_location_x3f_1455_);
v_explicit_1456_ = lean_ctor_get_uint8(v_info_1446_, sizeof(void*)*3);
if (lean_obj_tag(v_location_x3f_1455_) == 1)
{
lean_object* v_val_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1540_; 
v_val_1479_ = lean_ctor_get(v_location_x3f_1455_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v_location_x3f_1455_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1481_ = v_location_x3f_1455_;
v_isShared_1482_ = v_isSharedCheck_1540_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_val_1479_);
lean_dec(v_location_x3f_1455_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1540_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v_range_1483_; lean_object* v_pos_1484_; lean_object* v_endPos_1485_; lean_object* v_module_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1538_; 
v_range_1483_ = lean_ctor_get(v_val_1479_, 1);
v_pos_1484_ = lean_ctor_get(v_range_1483_, 0);
lean_inc_ref(v_pos_1484_);
v_endPos_1485_ = lean_ctor_get(v_range_1483_, 2);
lean_inc_ref(v_endPos_1485_);
v_module_1486_ = lean_ctor_get(v_val_1479_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_val_1479_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; 
v_unused_1539_ = lean_ctor_get(v_val_1479_, 1);
lean_dec(v_unused_1539_);
v___x_1488_ = v_val_1479_;
v_isShared_1489_ = v_isSharedCheck_1538_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_module_1486_);
lean_dec(v_val_1479_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1538_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v_line_1490_; lean_object* v_column_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1537_; 
v_line_1490_ = lean_ctor_get(v_pos_1484_, 0);
v_column_1491_ = lean_ctor_get(v_pos_1484_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_pos_1484_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1493_ = v_pos_1484_;
v_isShared_1494_ = v_isSharedCheck_1537_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_column_1491_);
lean_inc(v_line_1490_);
lean_dec(v_pos_1484_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1537_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v_line_1495_; lean_object* v_column_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1536_; 
v_line_1495_ = lean_ctor_get(v_endPos_1485_, 0);
v_column_1496_ = lean_ctor_get(v_endPos_1485_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_endPos_1485_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1498_ = v_endPos_1485_;
v_isShared_1499_ = v_isSharedCheck_1536_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_column_1496_);
lean_inc(v_line_1495_);
lean_dec(v_endPos_1485_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1536_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
uint8_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1500_ = 1;
v___x_1501_ = l_Lean_Name_toString(v_module_1486_, v___x_1500_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set_tag(v___x_1481_, 3);
lean_ctor_set(v___x_1481_, 0, v___x_1501_);
v___x_1503_ = v___x_1481_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1504_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
if (v_isShared_1499_ == 0)
{
lean_ctor_set_tag(v___x_1498_, 5);
lean_ctor_set(v___x_1498_, 1, v___x_1504_);
lean_ctor_set(v___x_1498_, 0, v___x_1503_);
v___x_1506_ = v___x_1498_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1507_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_1508_ = l_Nat_reprFast(v_line_1490_);
v___x_1509_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set_tag(v___x_1493_, 5);
lean_ctor_set(v___x_1493_, 1, v___x_1509_);
lean_ctor_set(v___x_1493_, 0, v___x_1507_);
v___x_1511_ = v___x_1493_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1512_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
if (v_isShared_1489_ == 0)
{
lean_ctor_set_tag(v___x_1488_, 5);
lean_ctor_set(v___x_1488_, 1, v___x_1512_);
lean_ctor_set(v___x_1488_, 0, v___x_1511_);
v___x_1514_ = v___x_1488_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1515_ = l_Nat_reprFast(v_column_1491_);
v___x_1516_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
v___x_1517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1514_);
lean_ctor_set(v___x_1517_, 1, v___x_1516_);
v___x_1518_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v___x_1519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1506_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_1522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1520_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
v___x_1523_ = l_Nat_reprFast(v_line_1495_);
v___x_1524_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
v___x_1525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1507_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v___x_1512_);
v___x_1527_ = l_Nat_reprFast(v_column_1496_);
v___x_1528_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
v___x_1529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1526_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
lean_ctor_set(v___x_1530_, 1, v___x_1518_);
v___x_1531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1522_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___y_1458_ = v___x_1531_;
goto v___jp_1457_;
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
lean_object* v___x_1541_; 
lean_dec(v_location_x3f_1455_);
v___x_1541_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
v___y_1458_ = v___x_1541_;
goto v___jp_1457_;
}
v___jp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_inc_ref(v___y_1450_);
v___x_1451_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___y_1450_);
v___x_1452_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___y_1449_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
return v___x_1453_;
}
v___jp_1457_:
{
lean_object* v_lctx_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v_a_1462_; lean_object* v___x_1463_; 
v_lctx_1459_ = lean_ctor_get(v_toTermInfo_1454_, 1);
lean_inc_ref(v_lctx_1459_);
v___x_1460_ = l_Lean_Elab_ContextInfo_toPPContext(v_ctx_1445_, v_lctx_1459_);
v___x_1461_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v___x_1460_, v_info_1446_);
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref(v___x_1461_);
v___x_1463_ = l_Lean_Elab_TermInfo_format(v_ctx_1445_, v_toTermInfo_1454_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
v___x_1465_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__1));
v___x_1466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
lean_ctor_set(v___x_1466_, 1, v_a_1464_);
v___x_1467_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__3));
v___x_1468_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
lean_ctor_set(v___x_1469_, 1, v___y_1458_);
v___x_1470_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__5));
v___x_1471_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1469_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = lean_unsigned_to_nat(0u);
v___x_1473_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_a_1462_, v___x_1472_);
v___x_1474_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1471_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__7));
v___x_1476_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
if (v_explicit_1456_ == 0)
{
lean_object* v___x_1477_; 
v___x_1477_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__8));
v___y_1449_ = v___x_1476_;
v___y_1450_ = v___x_1477_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1478_; 
v___x_1478_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__9));
v___y_1449_ = v___x_1476_;
v___y_1450_ = v___x_1478_;
goto v___jp_1448_;
}
}
else
{
lean_dec(v_a_1462_);
lean_dec(v___y_1458_);
return v___x_1463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object* v_ctx_1542_, lean_object* v_info_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1542_, v_info_1543_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object* v_ctx_1549_, lean_object* v_info_1550_){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1551_ = ((lean_object*)(l_Lean_Elab_ChoiceInfo_format___closed__1));
v___x_1552_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1549_, v_info_1550_);
v___x_1553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object* v_ctx_1557_, lean_object* v_info_1558_){
_start:
{
lean_object* v_stx_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_stx_1559_ = lean_ctor_get(v_info_1558_, 1);
v___x_1560_ = ((lean_object*)(l_Lean_Elab_DocInfo_format___closed__1));
lean_inc(v_stx_1559_);
v___x_1561_ = l_Lean_Syntax_getKind(v_stx_1559_);
v___x_1562_ = 1;
v___x_1563_ = l_Lean_Name_toString(v___x_1561_, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
v___x_1565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1560_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1557_, v_info_1558_);
v___x_1569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1567_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object* v_ctx_1579_, lean_object* v_info_1580_){
_start:
{
lean_object* v_toElabInfo_1581_; lean_object* v_name_1582_; uint8_t v_kind_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v_toElabInfo_1581_ = lean_ctor_get(v_info_1580_, 0);
lean_inc_ref(v_toElabInfo_1581_);
v_name_1582_ = lean_ctor_get(v_info_1580_, 1);
lean_inc(v_name_1582_);
v_kind_1583_ = lean_ctor_get_uint8(v_info_1580_, sizeof(void*)*2);
lean_dec_ref(v_info_1580_);
v___x_1584_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__1));
v___x_1585_ = 1;
v___x_1586_ = l_Lean_Name_toString(v_name_1582_, v___x_1585_);
v___x_1587_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
v___x_1588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1584_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__3));
v___x_1590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = lean_unsigned_to_nat(0u);
v___x_1592_ = l_Lean_Elab_instReprDocElabKind_repr(v_kind_1583_, v___x_1591_);
v___x_1593_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1590_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__5));
v___x_1595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1579_, v_toElabInfo_1581_);
v___x_1597_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object* v_ctx_1598_, lean_object* v_x_1599_){
_start:
{
switch(lean_obj_tag(v_x_1599_))
{
case 0:
{
lean_object* v_i_1601_; lean_object* v___x_1602_; 
v_i_1601_ = lean_ctor_get(v_x_1599_, 0);
lean_inc_ref(v_i_1601_);
lean_dec_ref_known(v_x_1599_, 1);
v___x_1602_ = l_Lean_Elab_TacticInfo_format(v_ctx_1598_, v_i_1601_);
return v___x_1602_;
}
case 1:
{
lean_object* v_i_1603_; lean_object* v___x_1604_; 
v_i_1603_ = lean_ctor_get(v_x_1599_, 0);
lean_inc_ref(v_i_1603_);
lean_dec_ref_known(v_x_1599_, 1);
v___x_1604_ = l_Lean_Elab_TermInfo_format(v_ctx_1598_, v_i_1603_);
return v___x_1604_;
}
case 2:
{
lean_object* v_i_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1613_; 
v_i_1605_ = lean_ctor_get(v_x_1599_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_x_1599_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1607_ = v_x_1599_;
v_isShared_1608_ = v_isSharedCheck_1613_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_i_1605_);
lean_dec(v_x_1599_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1613_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1609_ = l_Lean_Elab_PartialTermInfo_format(v_ctx_1598_, v_i_1605_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1609_);
v___x_1611_ = v___x_1607_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
case 3:
{
lean_object* v_i_1614_; lean_object* v___x_1615_; 
v_i_1614_ = lean_ctor_get(v_x_1599_, 0);
lean_inc_ref(v_i_1614_);
lean_dec_ref_known(v_x_1599_, 1);
v___x_1615_ = l_Lean_Elab_CommandInfo_format(v_ctx_1598_, v_i_1614_);
return v___x_1615_;
}
case 4:
{
lean_object* v_i_1616_; lean_object* v___x_1617_; 
v_i_1616_ = lean_ctor_get(v_x_1599_, 0);
lean_inc_ref(v_i_1616_);
lean_dec_ref_known(v_x_1599_, 1);
v___x_1617_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1598_, v_i_1616_);
lean_dec_ref(v_ctx_1598_);
return v___x_1617_;
}
case 5:
{
lean_object* v_i_1618_; lean_object* v___x_1619_; 
v_i_1618_ = lean_ctor_get(v_x_1599_, 0);
lean_inc_ref(v_i_1618_);
lean_dec_ref_known(v_x_1599_, 1);
v___x_1619_ = l_Lean_Elab_OptionInfo_format(v_ctx_1598_, v_i_1618_);
return v___x_1619_;
}
case 6:
{
lean_object* v_i_1620_; lean_object* v___x_1621_; 
v_i_1620_ = lean_ctor_get(v_x_1599_, 0);
lean_inc_ref(v_i_1620_);
lean_dec_ref_known(v_x_1599_, 1);
v___x_1621_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_1598_, v_i_1620_);
return v___x_1621_;
}
case 7:
{
lean_object* v_i_1622_; lean_object* v___x_1623_; 
v_i_1622_ = lean_ctor_get(v_x_1599_, 0);
lean_inc_ref(v_i_1622_);
lean_dec_ref_known(v_x_1599_, 1);
v___x_1623_ = l_Lean_Elab_FieldInfo_format(v_ctx_1598_, v_i_1622_);
return v___x_1623_;
}
case 8:
{
lean_object* v_i_1624_; lean_object* v___x_1625_; 
v_i_1624_ = lean_ctor_get(v_x_1599_, 0);
lean_inc_ref(v_i_1624_);
lean_dec_ref_known(v_x_1599_, 1);
v___x_1625_ = l_Lean_Elab_CompletionInfo_format(v_ctx_1598_, v_i_1624_);
return v___x_1625_;
}
case 9:
{
lean_object* v_i_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1634_; 
lean_dec_ref(v_ctx_1598_);
v_i_1626_ = lean_ctor_get(v_x_1599_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_x_1599_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1628_ = v_x_1599_;
v_isShared_1629_ = v_isSharedCheck_1634_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_i_1626_);
lean_dec(v_x_1599_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1634_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1632_; 
v___x_1630_ = l_Lean_Elab_UserWidgetInfo_format(v_i_1626_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set_tag(v___x_1628_, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1630_);
v___x_1632_ = v___x_1628_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
case 10:
{
lean_object* v_i_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1643_; 
lean_dec_ref(v_ctx_1598_);
v_i_1635_ = lean_ctor_get(v_x_1599_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v_x_1599_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1637_ = v_x_1599_;
v_isShared_1638_ = v_isSharedCheck_1643_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_i_1635_);
lean_dec(v_x_1599_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1643_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1639_ = l_Lean_Elab_CustomInfo_format(v_i_1635_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set_tag(v___x_1637_, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1639_);
v___x_1641_ = v___x_1637_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
case 11:
{
lean_object* v_i_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1652_; 
lean_dec_ref(v_ctx_1598_);
v_i_1644_ = lean_ctor_get(v_x_1599_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_x_1599_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1646_ = v_x_1599_;
v_isShared_1647_ = v_isSharedCheck_1652_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_i_1644_);
lean_dec(v_x_1599_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1652_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1648_ = l_Lean_Elab_FVarAliasInfo_format(v_i_1644_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set_tag(v___x_1646_, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1648_);
v___x_1650_ = v___x_1646_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
case 12:
{
lean_object* v_i_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1661_; 
v_i_1653_ = lean_ctor_get(v_x_1599_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_x_1599_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1655_ = v_x_1599_;
v_isShared_1656_ = v_isSharedCheck_1661_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_i_1653_);
lean_dec(v_x_1599_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1661_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1657_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1598_, v_i_1653_);
lean_dec(v_i_1653_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set_tag(v___x_1655_, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1657_);
v___x_1659_ = v___x_1655_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
case 13:
{
lean_object* v_i_1662_; lean_object* v___x_1663_; 
v_i_1662_ = lean_ctor_get(v_x_1599_, 0);
lean_inc_ref(v_i_1662_);
lean_dec_ref_known(v_x_1599_, 1);
v___x_1663_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1598_, v_i_1662_);
return v___x_1663_;
}
case 14:
{
lean_object* v_i_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1672_; 
v_i_1664_ = lean_ctor_get(v_x_1599_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_x_1599_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1666_ = v_x_1599_;
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_i_1664_);
lean_dec(v_x_1599_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1668_ = l_Lean_Elab_ChoiceInfo_format(v_ctx_1598_, v_i_1664_);
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
case 15:
{
lean_object* v_i_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1681_; 
v_i_1673_ = lean_ctor_get(v_x_1599_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_x_1599_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1675_ = v_x_1599_;
v_isShared_1676_ = v_isSharedCheck_1681_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_i_1673_);
lean_dec(v_x_1599_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1681_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = l_Lean_Elab_DocInfo_format(v_ctx_1598_, v_i_1673_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set_tag(v___x_1675_, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1677_);
v___x_1679_ = v___x_1675_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
default: 
{
lean_object* v_i_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1690_; 
v_i_1682_ = lean_ctor_get(v_x_1599_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_x_1599_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1684_ = v_x_1599_;
v_isShared_1685_ = v_isSharedCheck_1690_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_i_1682_);
lean_dec(v_x_1599_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1690_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1686_ = l_Lean_Elab_DocElabInfo_format(v_ctx_1598_, v_i_1682_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set_tag(v___x_1684_, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1686_);
v___x_1688_ = v___x_1684_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object* v_ctx_1691_, lean_object* v_x_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_Elab_Info_format(v_ctx_1691_, v_x_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object* v_x_1695_, lean_object* v_x_1696_){
_start:
{
if (lean_obj_tag(v_x_1696_) == 0)
{
return v_x_1695_;
}
else
{
lean_object* v_head_1697_; lean_object* v_tail_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v_head_1697_ = lean_ctor_get(v_x_1696_, 0);
v_tail_1698_ = lean_ctor_get(v_x_1696_, 1);
v___x_1699_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2));
v___x_1700_ = lean_string_append(v_x_1695_, v___x_1699_);
v___x_1701_ = lean_expr_dbg_to_string(v_head_1697_);
v___x_1702_ = lean_string_append(v___x_1700_, v___x_1701_);
lean_dec_ref(v___x_1701_);
v_x_1695_ = v___x_1702_;
v_x_1696_ = v_tail_1698_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object* v_x_1704_, lean_object* v_x_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v_x_1704_, v_x_1705_);
lean_dec(v_x_1705_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object* v_x_1709_){
_start:
{
if (lean_obj_tag(v_x_1709_) == 0)
{
lean_object* v___x_1710_; 
v___x_1710_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0));
return v___x_1710_;
}
else
{
lean_object* v_tail_1711_; 
v_tail_1711_ = lean_ctor_get(v_x_1709_, 1);
if (lean_obj_tag(v_tail_1711_) == 0)
{
lean_object* v_head_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v_head_1712_ = lean_ctor_get(v_x_1709_, 0);
v___x_1713_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1714_ = lean_expr_dbg_to_string(v_head_1712_);
v___x_1715_ = lean_string_append(v___x_1713_, v___x_1714_);
lean_dec_ref(v___x_1714_);
v___x_1716_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1717_ = lean_string_append(v___x_1715_, v___x_1716_);
return v___x_1717_;
}
else
{
lean_object* v_head_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; uint32_t v___x_1723_; lean_object* v___x_1724_; 
v_head_1718_ = lean_ctor_get(v_x_1709_, 0);
v___x_1719_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1720_ = lean_expr_dbg_to_string(v_head_1718_);
v___x_1721_ = lean_string_append(v___x_1719_, v___x_1720_);
lean_dec_ref(v___x_1720_);
v___x_1722_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v___x_1721_, v_tail_1711_);
v___x_1723_ = 93;
v___x_1724_ = lean_string_push(v___x_1722_, v___x_1723_);
return v___x_1724_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object* v_x_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v_x_1725_);
lean_dec(v_x_1725_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object* v_ctx_1733_){
_start:
{
switch(lean_obj_tag(v_ctx_1733_))
{
case 0:
{
lean_object* v___x_1734_; 
lean_dec_ref_known(v_ctx_1733_, 1);
v___x_1734_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__1));
return v___x_1734_;
}
case 1:
{
lean_object* v_parentDecl_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1748_; 
v_parentDecl_1735_ = lean_ctor_get(v_ctx_1733_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_ctx_1733_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1737_ = v_ctx_1733_;
v_isShared_1738_ = v_isSharedCheck_1748_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_parentDecl_1735_);
lean_dec(v_ctx_1733_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1748_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; uint8_t v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1746_; 
v___x_1739_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__2));
v___x_1740_ = 1;
v___x_1741_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_parentDecl_1735_, v___x_1740_);
v___x_1742_ = lean_string_append(v___x_1739_, v___x_1741_);
lean_dec_ref(v___x_1741_);
v___x_1743_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1744_ = lean_string_append(v___x_1742_, v___x_1743_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set_tag(v___x_1737_, 3);
lean_ctor_set(v___x_1737_, 0, v___x_1744_);
v___x_1746_ = v___x_1737_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(3, 1, 0);
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
lean_object* v_autoImplicits_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1764_; 
v_autoImplicits_1749_ = lean_ctor_get(v_ctx_1733_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v_ctx_1733_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1751_ = v_ctx_1733_;
v_isShared_1752_ = v_isSharedCheck_1764_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_autoImplicits_1749_);
lean_dec(v_ctx_1733_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1764_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1753_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__3));
v___x_1754_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__4));
v___x_1755_ = lean_array_to_list(v_autoImplicits_1749_);
v___x_1756_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v___x_1755_);
lean_dec(v___x_1755_);
v___x_1757_ = lean_string_append(v___x_1754_, v___x_1756_);
lean_dec_ref(v___x_1756_);
v___x_1758_ = lean_string_append(v___x_1753_, v___x_1757_);
lean_dec_ref(v___x_1757_);
v___x_1759_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1760_ = lean_string_append(v___x_1758_, v___x_1759_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set_tag(v___x_1751_, 3);
lean_ctor_set(v___x_1751_, 0, v___x_1760_);
v___x_1762_ = v___x_1751_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format(lean_object* v_tree_1774_, lean_object* v_ctx_x3f_1775_){
_start:
{
switch(lean_obj_tag(v_tree_1774_))
{
case 0:
{
lean_object* v_i_1777_; lean_object* v_t_1778_; lean_object* v___x_1779_; 
v_i_1777_ = lean_ctor_get(v_tree_1774_, 0);
lean_inc_ref(v_i_1777_);
v_t_1778_ = lean_ctor_get(v_tree_1774_, 1);
lean_inc_ref(v_t_1778_);
lean_dec_ref_known(v_tree_1774_, 2);
v___x_1779_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1777_, v_ctx_x3f_1775_);
v_tree_1774_ = v_t_1778_;
v_ctx_x3f_1775_ = v___x_1779_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_ctx_x3f_1775_) == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_dec_ref_known(v_tree_1774_, 2);
v___x_1781_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__1));
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
return v___x_1782_;
}
else
{
lean_object* v_i_1783_; lean_object* v_children_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1834_; 
v_i_1783_ = lean_ctor_get(v_tree_1774_, 0);
v_children_1784_ = lean_ctor_get(v_tree_1774_, 1);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_tree_1774_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1786_ = v_tree_1774_;
v_isShared_1787_ = v_isSharedCheck_1834_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_children_1784_);
lean_inc(v_i_1783_);
lean_dec(v_tree_1774_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1834_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v_val_1788_; lean_object* v___x_1789_; 
v_val_1788_ = lean_ctor_get(v_ctx_x3f_1775_, 0);
lean_inc_ref(v_i_1783_);
lean_inc(v_val_1788_);
v___x_1789_ = l_Lean_Elab_Info_format(v_val_1788_, v_i_1783_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1833_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1833_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1833_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v_size_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v_size_1794_ = lean_ctor_get(v_children_1784_, 2);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = lean_nat_dec_eq(v_size_1794_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
lean_del_object(v___x_1792_);
v___x_1797_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_1775_, v_i_1783_);
lean_dec_ref(v_i_1783_);
v___x_1798_ = l_Lean_PersistentArray_toList___redArg(v_children_1784_);
lean_dec_ref(v_children_1784_);
v___x_1799_ = lean_box(0);
v___x_1800_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1797_, v___x_1798_, v___x_1799_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1816_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1816_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1816_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1805_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1787_ == 0)
{
lean_ctor_set_tag(v___x_1786_, 5);
lean_ctor_set(v___x_1786_, 1, v_a_1790_);
lean_ctor_set(v___x_1786_, 0, v___x_1805_);
v___x_1807_ = v___x_1786_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1805_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_a_1790_);
v___x_1807_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1808_ = lean_box(1);
v___x_1809_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1808_, v_a_1801_);
v___x_1810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1807_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = l_Std_Format_nestD(v___x_1810_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1811_);
v___x_1813_ = v___x_1803_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec(v_a_1790_);
lean_del_object(v___x_1786_);
v_a_1817_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1800_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1800_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
else
{
lean_object* v___x_1825_; lean_object* v___x_1827_; 
lean_dec_ref(v_children_1784_);
lean_dec_ref_known(v_ctx_x3f_1775_, 1);
lean_dec_ref(v_i_1783_);
v___x_1825_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1787_ == 0)
{
lean_ctor_set_tag(v___x_1786_, 5);
lean_ctor_set(v___x_1786_, 1, v_a_1790_);
lean_ctor_set(v___x_1786_, 0, v___x_1825_);
v___x_1827_ = v___x_1786_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_a_1790_);
v___x_1827_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1828_ = l_Std_Format_nestD(v___x_1827_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v___x_1828_);
v___x_1830_ = v___x_1792_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
else
{
lean_del_object(v___x_1786_);
lean_dec_ref(v_children_1784_);
lean_dec_ref_known(v_ctx_x3f_1775_, 1);
lean_dec_ref(v_i_1783_);
return v___x_1789_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1848_; 
lean_dec(v_ctx_x3f_1775_);
v_mvarId_1835_ = lean_ctor_get(v_tree_1774_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_tree_1774_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1837_ = v_tree_1774_;
v_isShared_1838_ = v_isSharedCheck_1848_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_mvarId_1835_);
lean_dec(v_tree_1774_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1848_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; uint8_t v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1839_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__5));
v___x_1840_ = 1;
v___x_1841_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_1835_, v___x_1840_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set_tag(v___x_1837_, 3);
lean_ctor_set(v___x_1837_, 0, v___x_1841_);
v___x_1843_ = v___x_1837_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1839_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = l_Std_Format_nestD(v___x_1844_);
v___x_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
return v___x_1846_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object* v___x_1849_, lean_object* v_x_1850_, lean_object* v_x_1851_){
_start:
{
if (lean_obj_tag(v_x_1850_) == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
lean_dec(v___x_1849_);
v___x_1853_ = l_List_reverse___redArg(v_x_1851_);
v___x_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
return v___x_1854_;
}
else
{
lean_object* v_head_1855_; lean_object* v_tail_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1874_; 
v_head_1855_ = lean_ctor_get(v_x_1850_, 0);
v_tail_1856_ = lean_ctor_get(v_x_1850_, 1);
v_isSharedCheck_1874_ = !lean_is_exclusive(v_x_1850_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1858_ = v_x_1850_;
v_isShared_1859_ = v_isSharedCheck_1874_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_tail_1856_);
lean_inc(v_head_1855_);
lean_dec(v_x_1850_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1874_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; 
lean_inc(v___x_1849_);
v___x_1860_ = l_Lean_Elab_InfoTree_format(v_head_1855_, v___x_1849_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref_known(v___x_1860_, 1);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 1, v_x_1851_);
lean_ctor_set(v___x_1858_, 0, v_a_1861_);
v___x_1863_ = v___x_1858_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1861_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_x_1851_);
v___x_1863_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
v_x_1850_ = v_tail_1856_;
v_x_1851_ = v___x_1863_;
goto _start;
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_del_object(v___x_1858_);
lean_dec(v_tail_1856_);
lean_dec(v_x_1851_);
lean_dec(v___x_1849_);
v_a_1866_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1860_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1860_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
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
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object* v___x_1875_, lean_object* v_x_1876_, lean_object* v_x_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1875_, v_x_1876_, v_x_1877_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object* v_tree_1880_, lean_object* v_ctx_x3f_1881_, lean_object* v_a_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_Elab_InfoTree_format(v_tree_1880_, v_ctx_x3f_1881_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object* v_f_1884_, lean_object* v_s_1885_){
_start:
{
uint8_t v_enabled_1886_; lean_object* v_assignment_1887_; lean_object* v_lazyAssignment_1888_; lean_object* v_trees_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1897_; 
v_enabled_1886_ = lean_ctor_get_uint8(v_s_1885_, sizeof(void*)*3);
v_assignment_1887_ = lean_ctor_get(v_s_1885_, 0);
v_lazyAssignment_1888_ = lean_ctor_get(v_s_1885_, 1);
v_trees_1889_ = lean_ctor_get(v_s_1885_, 2);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_s_1885_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1891_ = v_s_1885_;
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_trees_1889_);
lean_inc(v_lazyAssignment_1888_);
lean_inc(v_assignment_1887_);
lean_dec(v_s_1885_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = lean_apply_1(v_f_1884_, v_trees_1889_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 2, v___x_1893_);
v___x_1895_ = v___x_1891_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_assignment_1887_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_lazyAssignment_1888_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v___x_1893_);
lean_ctor_set_uint8(v_reuseFailAlloc_1896_, sizeof(void*)*3, v_enabled_1886_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object* v_inst_1898_, lean_object* v_f_1899_){
_start:
{
lean_object* v_modifyInfoState_1900_; lean_object* v___f_1901_; lean_object* v___x_1902_; 
v_modifyInfoState_1900_ = lean_ctor_get(v_inst_1898_, 1);
lean_inc(v_modifyInfoState_1900_);
lean_dec_ref(v_inst_1898_);
v___f_1901_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1901_, 0, v_f_1899_);
v___x_1902_ = lean_apply_1(v_modifyInfoState_1900_, v___f_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object* v_m_1903_, lean_object* v_inst_1904_, lean_object* v_f_1905_){
_start:
{
lean_object* v_modifyInfoState_1906_; lean_object* v___f_1907_; lean_object* v___x_1908_; 
v_modifyInfoState_1906_ = lean_ctor_get(v_inst_1904_, 1);
lean_inc(v_modifyInfoState_1906_);
lean_dec_ref(v_inst_1904_);
v___f_1907_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1907_, 0, v_f_1905_);
v___x_1908_ = lean_apply_1(v_modifyInfoState_1906_, v___f_1907_);
return v___x_1908_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = lean_unsigned_to_nat(32u);
v___x_1910_ = lean_mk_empty_array_with_capacity(v___x_1909_);
v___x_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
return v___x_1911_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1912_ = ((size_t)5ULL);
v___x_1913_ = lean_unsigned_to_nat(0u);
v___x_1914_ = lean_unsigned_to_nat(32u);
v___x_1915_ = lean_mk_empty_array_with_capacity(v___x_1914_);
v___x_1916_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0);
v___x_1917_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
lean_ctor_set(v___x_1917_, 1, v___x_1915_);
lean_ctor_set(v___x_1917_, 2, v___x_1913_);
lean_ctor_set(v___x_1917_, 3, v___x_1913_);
lean_ctor_set_usize(v___x_1917_, 4, v___x_1912_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object* v_s_1918_){
_start:
{
uint8_t v_enabled_1919_; lean_object* v_assignment_1920_; lean_object* v_lazyAssignment_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1929_; 
v_enabled_1919_ = lean_ctor_get_uint8(v_s_1918_, sizeof(void*)*3);
v_assignment_1920_ = lean_ctor_get(v_s_1918_, 0);
v_lazyAssignment_1921_ = lean_ctor_get(v_s_1918_, 1);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_s_1918_);
if (v_isSharedCheck_1929_ == 0)
{
lean_object* v_unused_1930_; 
v_unused_1930_ = lean_ctor_get(v_s_1918_, 2);
lean_dec(v_unused_1930_);
v___x_1923_ = v_s_1918_;
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_lazyAssignment_1921_);
lean_inc(v_assignment_1920_);
lean_dec(v_s_1918_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 2, v___x_1925_);
v___x_1927_ = v___x_1923_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_assignment_1920_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_lazyAssignment_1921_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v___x_1925_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*3, v_enabled_1919_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object* v_toPure_1931_, lean_object* v_trees_1932_, lean_object* v_____r_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_apply_2(v_toPure_1931_, lean_box(0), v_trees_1932_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object* v_toPure_1935_, lean_object* v_modifyInfoState_1936_, lean_object* v___f_1937_, lean_object* v_toBind_1938_, lean_object* v_____do__lift_1939_){
_start:
{
lean_object* v_trees_1940_; lean_object* v___f_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v_trees_1940_ = lean_ctor_get(v_____do__lift_1939_, 2);
lean_inc_ref(v_trees_1940_);
lean_dec_ref(v_____do__lift_1939_);
v___f_1941_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1941_, 0, v_toPure_1935_);
lean_closure_set(v___f_1941_, 1, v_trees_1940_);
v___x_1942_ = lean_apply_1(v_modifyInfoState_1936_, v___f_1937_);
v___x_1943_ = lean_apply_4(v_toBind_1938_, lean_box(0), lean_box(0), v___x_1942_, v___f_1941_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object* v_inst_1945_, lean_object* v_inst_1946_){
_start:
{
lean_object* v_toApplicative_1947_; lean_object* v_toBind_1948_; lean_object* v_getInfoState_1949_; lean_object* v_modifyInfoState_1950_; lean_object* v_toPure_1951_; lean_object* v___f_1952_; lean_object* v___f_1953_; lean_object* v___x_1954_; 
v_toApplicative_1947_ = lean_ctor_get(v_inst_1945_, 0);
lean_inc_ref(v_toApplicative_1947_);
v_toBind_1948_ = lean_ctor_get(v_inst_1945_, 1);
lean_inc_n(v_toBind_1948_, 2);
lean_dec_ref(v_inst_1945_);
v_getInfoState_1949_ = lean_ctor_get(v_inst_1946_, 0);
lean_inc(v_getInfoState_1949_);
v_modifyInfoState_1950_ = lean_ctor_get(v_inst_1946_, 1);
lean_inc(v_modifyInfoState_1950_);
lean_dec_ref(v_inst_1946_);
v_toPure_1951_ = lean_ctor_get(v_toApplicative_1947_, 1);
lean_inc(v_toPure_1951_);
lean_dec_ref(v_toApplicative_1947_);
v___f_1952_ = ((lean_object*)(l_Lean_Elab_getResetInfoTrees___redArg___closed__0));
v___f_1953_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1953_, 0, v_toPure_1951_);
lean_closure_set(v___f_1953_, 1, v_modifyInfoState_1950_);
lean_closure_set(v___f_1953_, 2, v___f_1952_);
lean_closure_set(v___f_1953_, 3, v_toBind_1948_);
v___x_1954_ = lean_apply_4(v_toBind_1948_, lean_box(0), lean_box(0), v_getInfoState_1949_, v___f_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object* v_m_1955_, lean_object* v_inst_1956_, lean_object* v_inst_1957_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_1956_, v_inst_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object* v_t_1959_, lean_object* v_s_1960_){
_start:
{
uint8_t v_enabled_1961_; lean_object* v_assignment_1962_; lean_object* v_lazyAssignment_1963_; lean_object* v_trees_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1972_; 
v_enabled_1961_ = lean_ctor_get_uint8(v_s_1960_, sizeof(void*)*3);
v_assignment_1962_ = lean_ctor_get(v_s_1960_, 0);
v_lazyAssignment_1963_ = lean_ctor_get(v_s_1960_, 1);
v_trees_1964_ = lean_ctor_get(v_s_1960_, 2);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_s_1960_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1966_ = v_s_1960_;
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_trees_1964_);
lean_inc(v_lazyAssignment_1963_);
lean_inc(v_assignment_1962_);
lean_dec(v_s_1960_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1968_ = l_Lean_PersistentArray_push___redArg(v_trees_1964_, v_t_1959_);
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
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_assignment_1962_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_lazyAssignment_1963_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v___x_1968_);
lean_ctor_set_uint8(v_reuseFailAlloc_1971_, sizeof(void*)*3, v_enabled_1961_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object* v_toApplicative_1973_, lean_object* v_modifyInfoState_1974_, lean_object* v___f_1975_, lean_object* v_____do__lift_1976_){
_start:
{
uint8_t v_enabled_1977_; 
v_enabled_1977_ = lean_ctor_get_uint8(v_____do__lift_1976_, sizeof(void*)*3);
if (v_enabled_1977_ == 0)
{
lean_object* v_toPure_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec_ref(v___f_1975_);
lean_dec(v_modifyInfoState_1974_);
v_toPure_1978_ = lean_ctor_get(v_toApplicative_1973_, 1);
lean_inc(v_toPure_1978_);
lean_dec_ref(v_toApplicative_1973_);
v___x_1979_ = lean_box(0);
v___x_1980_ = lean_apply_2(v_toPure_1978_, lean_box(0), v___x_1979_);
return v___x_1980_;
}
else
{
lean_object* v___x_1981_; 
lean_dec_ref(v_toApplicative_1973_);
v___x_1981_ = lean_apply_1(v_modifyInfoState_1974_, v___f_1975_);
return v___x_1981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object* v_toApplicative_1982_, lean_object* v_modifyInfoState_1983_, lean_object* v___f_1984_, lean_object* v_____do__lift_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Elab_pushInfoTree___redArg___lam__1(v_toApplicative_1982_, v_modifyInfoState_1983_, v___f_1984_, v_____do__lift_1985_);
lean_dec_ref(v_____do__lift_1985_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object* v_inst_1987_, lean_object* v_inst_1988_, lean_object* v_t_1989_){
_start:
{
lean_object* v_toApplicative_1990_; lean_object* v_toBind_1991_; lean_object* v_getInfoState_1992_; lean_object* v_modifyInfoState_1993_; lean_object* v___f_1994_; lean_object* v___f_1995_; lean_object* v___x_1996_; 
v_toApplicative_1990_ = lean_ctor_get(v_inst_1987_, 0);
lean_inc_ref(v_toApplicative_1990_);
v_toBind_1991_ = lean_ctor_get(v_inst_1987_, 1);
lean_inc(v_toBind_1991_);
lean_dec_ref(v_inst_1987_);
v_getInfoState_1992_ = lean_ctor_get(v_inst_1988_, 0);
lean_inc(v_getInfoState_1992_);
v_modifyInfoState_1993_ = lean_ctor_get(v_inst_1988_, 1);
lean_inc(v_modifyInfoState_1993_);
lean_dec_ref(v_inst_1988_);
v___f_1994_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1994_, 0, v_t_1989_);
v___f_1995_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1995_, 0, v_toApplicative_1990_);
lean_closure_set(v___f_1995_, 1, v_modifyInfoState_1993_);
lean_closure_set(v___f_1995_, 2, v___f_1994_);
v___x_1996_ = lean_apply_4(v_toBind_1991_, lean_box(0), lean_box(0), v_getInfoState_1992_, v___f_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object* v_m_1997_, lean_object* v_inst_1998_, lean_object* v_inst_1999_, lean_object* v_t_2000_){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_1998_, v_inst_1999_, v_t_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object* v_toApplicative_2002_, lean_object* v_t_2003_, lean_object* v_inst_2004_, lean_object* v_inst_2005_, lean_object* v_____do__lift_2006_){
_start:
{
uint8_t v_enabled_2007_; 
v_enabled_2007_ = lean_ctor_get_uint8(v_____do__lift_2006_, sizeof(void*)*3);
if (v_enabled_2007_ == 0)
{
lean_object* v_toPure_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_dec_ref(v_inst_2005_);
lean_dec_ref(v_inst_2004_);
lean_dec_ref(v_t_2003_);
v_toPure_2008_ = lean_ctor_get(v_toApplicative_2002_, 1);
lean_inc(v_toPure_2008_);
lean_dec_ref(v_toApplicative_2002_);
v___x_2009_ = lean_box(0);
v___x_2010_ = lean_apply_2(v_toPure_2008_, lean_box(0), v___x_2009_);
return v___x_2010_;
}
else
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_dec_ref(v_toApplicative_2002_);
v___x_2011_ = lean_unsigned_to_nat(32u);
v___x_2012_ = lean_mk_empty_array_with_capacity(v___x_2011_);
lean_dec_ref(v___x_2012_);
v___x_2013_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2014_, 0, v_t_2003_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v___x_2015_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2004_, v_inst_2005_, v___x_2014_);
return v___x_2015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object* v_toApplicative_2016_, lean_object* v_t_2017_, lean_object* v_inst_2018_, lean_object* v_inst_2019_, lean_object* v_____do__lift_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_Elab_pushInfoLeaf___redArg___lam__0(v_toApplicative_2016_, v_t_2017_, v_inst_2018_, v_inst_2019_, v_____do__lift_2020_);
lean_dec_ref(v_____do__lift_2020_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object* v_inst_2022_, lean_object* v_inst_2023_, lean_object* v_t_2024_){
_start:
{
lean_object* v_toApplicative_2025_; lean_object* v_toBind_2026_; lean_object* v_getInfoState_2027_; lean_object* v___f_2028_; lean_object* v___x_2029_; 
v_toApplicative_2025_ = lean_ctor_get(v_inst_2022_, 0);
lean_inc_ref(v_toApplicative_2025_);
v_toBind_2026_ = lean_ctor_get(v_inst_2022_, 1);
lean_inc(v_toBind_2026_);
v_getInfoState_2027_ = lean_ctor_get(v_inst_2023_, 0);
lean_inc(v_getInfoState_2027_);
v___f_2028_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2028_, 0, v_toApplicative_2025_);
lean_closure_set(v___f_2028_, 1, v_t_2024_);
lean_closure_set(v___f_2028_, 2, v_inst_2022_);
lean_closure_set(v___f_2028_, 3, v_inst_2023_);
v___x_2029_ = lean_apply_4(v_toBind_2026_, lean_box(0), lean_box(0), v_getInfoState_2027_, v___f_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object* v_m_2030_, lean_object* v_inst_2031_, lean_object* v_inst_2032_, lean_object* v_t_2033_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2031_, v_inst_2032_, v_t_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object* v_inst_2035_, lean_object* v_inst_2036_, lean_object* v_info_2037_){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2038_, 0, v_info_2037_);
v___x_2039_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2035_, v_inst_2036_, v___x_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object* v_m_2040_, lean_object* v_inst_2041_, lean_object* v_inst_2042_, lean_object* v_info_2043_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_2041_, v_inst_2042_, v_info_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object* v_stx_2045_, lean_object* v_expectedType_x3f_2046_, lean_object* v_inst_2047_, lean_object* v_inst_2048_, lean_object* v_____do__lift_2049_){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2050_ = lean_box(0);
v___x_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
lean_ctor_set(v___x_2051_, 1, v_stx_2045_);
v___x_2052_ = l_Lean_LocalContext_empty;
v___x_2053_ = 0;
v___x_2054_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2054_, 0, v___x_2051_);
lean_ctor_set(v___x_2054_, 1, v___x_2052_);
lean_ctor_set(v___x_2054_, 2, v_expectedType_x3f_2046_);
lean_ctor_set(v___x_2054_, 3, v_____do__lift_2049_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*4, v___x_2053_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*4 + 1, v___x_2053_);
v___x_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
v___x_2056_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2047_, v_inst_2048_, v___x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object* v_inst_2057_, lean_object* v_inst_2058_, lean_object* v_inst_2059_, lean_object* v_inst_2060_, lean_object* v_stx_2061_, lean_object* v_n_2062_, lean_object* v_expectedType_x3f_2063_){
_start:
{
lean_object* v_toBind_2064_; lean_object* v___f_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v_toBind_2064_ = lean_ctor_get(v_inst_2057_, 1);
lean_inc(v_toBind_2064_);
lean_inc_ref(v_inst_2057_);
v___f_2065_ = lean_alloc_closure((void*)(l_Lean_Elab_addConstInfo___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2065_, 0, v_stx_2061_);
lean_closure_set(v___f_2065_, 1, v_expectedType_x3f_2063_);
lean_closure_set(v___f_2065_, 2, v_inst_2057_);
lean_closure_set(v___f_2065_, 3, v_inst_2058_);
v___x_2066_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_2057_, v_inst_2059_, v_inst_2060_, v_n_2062_);
v___x_2067_ = lean_apply_4(v_toBind_2064_, lean_box(0), lean_box(0), v___x_2066_, v___f_2065_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object* v_m_2068_, lean_object* v_inst_2069_, lean_object* v_inst_2070_, lean_object* v_inst_2071_, lean_object* v_inst_2072_, lean_object* v_stx_2073_, lean_object* v_n_2074_, lean_object* v_expectedType_x3f_2075_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_Lean_Elab_addConstInfo___redArg(v_inst_2069_, v_inst_2070_, v_inst_2071_, v_inst_2072_, v_stx_2073_, v_n_2074_, v_expectedType_x3f_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v___x_2080_; lean_object* v_infoState_2081_; uint8_t v_enabled_2082_; 
v___x_2080_ = lean_st_ref_get(v___y_2078_);
v_infoState_2081_ = lean_ctor_get(v___x_2080_, 7);
lean_inc_ref(v_infoState_2081_);
lean_dec(v___x_2080_);
v_enabled_2082_ = lean_ctor_get_uint8(v_infoState_2081_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2081_);
if (v_enabled_2082_ == 0)
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_dec_ref(v_t_2077_);
v___x_2083_ = lean_box(0);
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
return v___x_2084_;
}
else
{
lean_object* v___x_2085_; lean_object* v_infoState_2086_; lean_object* v_env_2087_; lean_object* v_nextMacroScope_2088_; lean_object* v_ngen_2089_; lean_object* v_auxDeclNGen_2090_; lean_object* v_traceState_2091_; lean_object* v_cache_2092_; lean_object* v_messages_2093_; lean_object* v_snapshotTasks_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2116_; 
v___x_2085_ = lean_st_ref_take(v___y_2078_);
v_infoState_2086_ = lean_ctor_get(v___x_2085_, 7);
v_env_2087_ = lean_ctor_get(v___x_2085_, 0);
v_nextMacroScope_2088_ = lean_ctor_get(v___x_2085_, 1);
v_ngen_2089_ = lean_ctor_get(v___x_2085_, 2);
v_auxDeclNGen_2090_ = lean_ctor_get(v___x_2085_, 3);
v_traceState_2091_ = lean_ctor_get(v___x_2085_, 4);
v_cache_2092_ = lean_ctor_get(v___x_2085_, 5);
v_messages_2093_ = lean_ctor_get(v___x_2085_, 6);
v_snapshotTasks_2094_ = lean_ctor_get(v___x_2085_, 8);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2096_ = v___x_2085_;
v_isShared_2097_ = v_isSharedCheck_2116_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_snapshotTasks_2094_);
lean_inc(v_infoState_2086_);
lean_inc(v_messages_2093_);
lean_inc(v_cache_2092_);
lean_inc(v_traceState_2091_);
lean_inc(v_auxDeclNGen_2090_);
lean_inc(v_ngen_2089_);
lean_inc(v_nextMacroScope_2088_);
lean_inc(v_env_2087_);
lean_dec(v___x_2085_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2116_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
uint8_t v_enabled_2098_; lean_object* v_assignment_2099_; lean_object* v_lazyAssignment_2100_; lean_object* v_trees_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2115_; 
v_enabled_2098_ = lean_ctor_get_uint8(v_infoState_2086_, sizeof(void*)*3);
v_assignment_2099_ = lean_ctor_get(v_infoState_2086_, 0);
v_lazyAssignment_2100_ = lean_ctor_get(v_infoState_2086_, 1);
v_trees_2101_ = lean_ctor_get(v_infoState_2086_, 2);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_infoState_2086_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2103_ = v_infoState_2086_;
v_isShared_2104_ = v_isSharedCheck_2115_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_trees_2101_);
lean_inc(v_lazyAssignment_2100_);
lean_inc(v_assignment_2099_);
lean_dec(v_infoState_2086_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2115_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2105_ = l_Lean_PersistentArray_push___redArg(v_trees_2101_, v_t_2077_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 2, v___x_2105_);
v___x_2107_ = v___x_2103_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_assignment_2099_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_lazyAssignment_2100_);
lean_ctor_set(v_reuseFailAlloc_2114_, 2, v___x_2105_);
lean_ctor_set_uint8(v_reuseFailAlloc_2114_, sizeof(void*)*3, v_enabled_2098_);
v___x_2107_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2109_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 7, v___x_2107_);
v___x_2109_ = v___x_2096_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_env_2087_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_nextMacroScope_2088_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_ngen_2089_);
lean_ctor_set(v_reuseFailAlloc_2113_, 3, v_auxDeclNGen_2090_);
lean_ctor_set(v_reuseFailAlloc_2113_, 4, v_traceState_2091_);
lean_ctor_set(v_reuseFailAlloc_2113_, 5, v_cache_2092_);
lean_ctor_set(v_reuseFailAlloc_2113_, 6, v_messages_2093_);
lean_ctor_set(v_reuseFailAlloc_2113_, 7, v___x_2107_);
lean_ctor_set(v_reuseFailAlloc_2113_, 8, v_snapshotTasks_2094_);
v___x_2109_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2110_ = lean_st_ref_set(v___y_2078_, v___x_2109_);
v___x_2111_ = lean_box(0);
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
return v___x_2112_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2117_, v___y_2118_);
lean_dec(v___y_2118_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object* v_t_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; lean_object* v_infoState_2126_; uint8_t v_enabled_2127_; 
v___x_2125_ = lean_st_ref_get(v___y_2123_);
v_infoState_2126_ = lean_ctor_get(v___x_2125_, 7);
lean_inc_ref(v_infoState_2126_);
lean_dec(v___x_2125_);
v_enabled_2127_ = lean_ctor_get_uint8(v_infoState_2126_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2126_);
if (v_enabled_2127_ == 0)
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
lean_dec_ref(v_t_2121_);
v___x_2128_ = lean_box(0);
v___x_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
return v___x_2129_;
}
else
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2130_ = lean_unsigned_to_nat(32u);
v___x_2131_ = lean_mk_empty_array_with_capacity(v___x_2130_);
lean_dec_ref(v___x_2131_);
v___x_2132_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2133_, 0, v_t_2121_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v___x_2133_, v___y_2123_);
return v___x_2134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object* v_t_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_2135_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
return v_res_2139_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2140_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
return v___x_2142_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2143_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2144_ = lean_unsigned_to_nat(0u);
v___x_2145_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
lean_ctor_set(v___x_2145_, 2, v___x_2144_);
lean_ctor_set(v___x_2145_, 3, v___x_2144_);
lean_ctor_set(v___x_2145_, 4, v___x_2143_);
lean_ctor_set(v___x_2145_, 5, v___x_2143_);
lean_ctor_set(v___x_2145_, 6, v___x_2143_);
lean_ctor_set(v___x_2145_, 7, v___x_2143_);
lean_ctor_set(v___x_2145_, 8, v___x_2143_);
lean_ctor_set(v___x_2145_, 9, v___x_2143_);
return v___x_2145_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2146_ = lean_box(1);
v___x_2147_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_2148_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
lean_ctor_set(v___x_2149_, 1, v___x_2147_);
lean_ctor_set(v___x_2149_, 2, v___x_2146_);
return v___x_2149_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_2152_ = l_Lean_stringToMessageData(v___x_2151_);
return v___x_2152_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_2155_ = l_Lean_stringToMessageData(v___x_2154_);
return v___x_2155_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_2158_ = l_Lean_stringToMessageData(v___x_2157_);
return v___x_2158_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_2161_ = l_Lean_stringToMessageData(v___x_2160_);
return v___x_2161_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_2164_ = l_Lean_stringToMessageData(v___x_2163_);
return v___x_2164_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_2167_ = l_Lean_stringToMessageData(v___x_2166_);
return v___x_2167_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2169_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_2170_ = l_Lean_stringToMessageData(v___x_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_2171_, lean_object* v_declHint_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v___x_2175_; lean_object* v_env_2176_; uint8_t v___x_2177_; 
v___x_2175_ = lean_st_ref_get(v___y_2173_);
v_env_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc_ref(v_env_2176_);
lean_dec(v___x_2175_);
v___x_2177_ = l_Lean_Name_isAnonymous(v_declHint_2172_);
if (v___x_2177_ == 0)
{
uint8_t v_isExporting_2178_; 
v_isExporting_2178_ = lean_ctor_get_uint8(v_env_2176_, sizeof(void*)*8);
if (v_isExporting_2178_ == 0)
{
lean_object* v___x_2179_; 
lean_dec_ref(v_env_2176_);
lean_dec(v_declHint_2172_);
v___x_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2179_, 0, v_msg_2171_);
return v___x_2179_;
}
else
{
lean_object* v___x_2180_; uint8_t v___x_2181_; 
lean_inc_ref(v_env_2176_);
v___x_2180_ = l_Lean_Environment_setExporting(v_env_2176_, v___x_2177_);
lean_inc(v_declHint_2172_);
lean_inc_ref(v___x_2180_);
v___x_2181_ = l_Lean_Environment_contains(v___x_2180_, v_declHint_2172_, v_isExporting_2178_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; 
lean_dec_ref(v___x_2180_);
lean_dec_ref(v_env_2176_);
lean_dec(v_declHint_2172_);
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v_msg_2171_);
return v___x_2182_;
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v_c_2188_; lean_object* v___x_2189_; 
v___x_2183_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_2184_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_2185_ = l_Lean_Options_empty;
v___x_2186_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2180_);
lean_ctor_set(v___x_2186_, 1, v___x_2183_);
lean_ctor_set(v___x_2186_, 2, v___x_2184_);
lean_ctor_set(v___x_2186_, 3, v___x_2185_);
lean_inc(v_declHint_2172_);
v___x_2187_ = l_Lean_MessageData_ofConstName(v_declHint_2172_, v___x_2177_);
v_c_2188_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2188_, 0, v___x_2186_);
lean_ctor_set(v_c_2188_, 1, v___x_2187_);
v___x_2189_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2176_, v_declHint_2172_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
lean_dec_ref(v_env_2176_);
lean_dec(v_declHint_2172_);
v___x_2190_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_2191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
lean_ctor_set(v___x_2191_, 1, v_c_2188_);
v___x_2192_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_2193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2191_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v___x_2194_ = l_Lean_MessageData_note(v___x_2193_);
v___x_2195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2195_, 0, v_msg_2171_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
v___x_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
return v___x_2196_;
}
else
{
lean_object* v_val_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2232_; 
v_val_2197_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2199_ = v___x_2189_;
v_isShared_2200_ = v_isSharedCheck_2232_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_val_2197_);
lean_dec(v___x_2189_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2232_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v_mod_2204_; uint8_t v___x_2205_; 
v___x_2201_ = lean_box(0);
v___x_2202_ = l_Lean_Environment_header(v_env_2176_);
lean_dec_ref(v_env_2176_);
v___x_2203_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2202_);
v_mod_2204_ = lean_array_get(v___x_2201_, v___x_2203_, v_val_2197_);
lean_dec(v_val_2197_);
lean_dec_ref(v___x_2203_);
v___x_2205_ = l_Lean_isPrivateName(v_declHint_2172_);
lean_dec(v_declHint_2172_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2217_; 
v___x_2206_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_2207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
lean_ctor_set(v___x_2207_, 1, v_c_2188_);
v___x_2208_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_2209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2207_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = l_Lean_MessageData_ofName(v_mod_2204_);
v___x_2211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2209_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_2213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2211_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v___x_2214_ = l_Lean_MessageData_note(v___x_2213_);
v___x_2215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2215_, 0, v_msg_2171_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set_tag(v___x_2199_, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2215_);
v___x_2217_ = v___x_2199_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2219_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_2220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
lean_ctor_set(v___x_2220_, 1, v_c_2188_);
v___x_2221_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2220_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = l_Lean_MessageData_ofName(v_mod_2204_);
v___x_2224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2222_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
v___x_2225_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_2226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2224_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
v___x_2227_ = l_Lean_MessageData_note(v___x_2226_);
v___x_2228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2228_, 0, v_msg_2171_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set_tag(v___x_2199_, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2228_);
v___x_2230_ = v___x_2199_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2233_; 
lean_dec_ref(v_env_2176_);
lean_dec(v_declHint_2172_);
v___x_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2233_, 0, v_msg_2171_);
return v___x_2233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_2234_, lean_object* v_declHint_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2234_, v_declHint_2235_, v___y_2236_);
lean_dec(v___y_2236_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_2239_, lean_object* v_declHint_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v___x_2244_; lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2254_; 
v___x_2244_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2239_, v_declHint_2240_, v___y_2242_);
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2247_ = v___x_2244_;
v_isShared_2248_ = v_isSharedCheck_2254_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2244_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2254_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2249_ = l_Lean_unknownIdentifierMessageTag;
v___x_2250_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
lean_ctor_set(v___x_2250_, 1, v_a_2245_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2250_);
v___x_2252_ = v___x_2247_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_2255_, lean_object* v_declHint_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2255_, v_declHint_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object* v_msgData_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v___x_2265_; lean_object* v_env_2266_; lean_object* v_options_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2265_ = lean_st_ref_get(v___y_2263_);
v_env_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc_ref(v_env_2266_);
lean_dec(v___x_2265_);
v_options_2267_ = lean_ctor_get(v___y_2262_, 2);
v___x_2268_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_2269_ = lean_unsigned_to_nat(32u);
v___x_2270_ = lean_mk_empty_array_with_capacity(v___x_2269_);
lean_dec_ref(v___x_2270_);
v___x_2271_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
lean_inc_ref(v_options_2267_);
v___x_2272_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2272_, 0, v_env_2266_);
lean_ctor_set(v___x_2272_, 1, v___x_2268_);
lean_ctor_set(v___x_2272_, 2, v___x_2271_);
lean_ctor_set(v___x_2272_, 3, v_options_2267_);
v___x_2273_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v_msgData_2261_);
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object* v_msgData_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_ref_2284_; lean_object* v___x_2285_; lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2294_; 
v_ref_2284_ = lean_ctor_get(v___y_2281_, 5);
v___x_2285_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_2280_, v___y_2281_, v___y_2282_);
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2288_ = v___x_2285_;
v_isShared_2289_ = v_isSharedCheck_2294_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2294_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2290_; lean_object* v___x_2292_; 
lean_inc(v_ref_2284_);
v___x_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2290_, 0, v_ref_2284_);
lean_ctor_set(v___x_2290_, 1, v_a_2286_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set_tag(v___x_2288_, 1);
lean_ctor_set(v___x_2288_, 0, v___x_2290_);
v___x_2292_ = v___x_2288_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_2300_, lean_object* v_msg_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_fileName_2305_; lean_object* v_fileMap_2306_; lean_object* v_options_2307_; lean_object* v_currRecDepth_2308_; lean_object* v_maxRecDepth_2309_; lean_object* v_ref_2310_; lean_object* v_currNamespace_2311_; lean_object* v_openDecls_2312_; lean_object* v_initHeartbeats_2313_; lean_object* v_maxHeartbeats_2314_; lean_object* v_quotContext_2315_; lean_object* v_currMacroScope_2316_; uint8_t v_diag_2317_; lean_object* v_cancelTk_x3f_2318_; uint8_t v_suppressElabErrors_2319_; lean_object* v_inheritedTraceOptions_2320_; lean_object* v_ref_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v_fileName_2305_ = lean_ctor_get(v___y_2302_, 0);
v_fileMap_2306_ = lean_ctor_get(v___y_2302_, 1);
v_options_2307_ = lean_ctor_get(v___y_2302_, 2);
v_currRecDepth_2308_ = lean_ctor_get(v___y_2302_, 3);
v_maxRecDepth_2309_ = lean_ctor_get(v___y_2302_, 4);
v_ref_2310_ = lean_ctor_get(v___y_2302_, 5);
v_currNamespace_2311_ = lean_ctor_get(v___y_2302_, 6);
v_openDecls_2312_ = lean_ctor_get(v___y_2302_, 7);
v_initHeartbeats_2313_ = lean_ctor_get(v___y_2302_, 8);
v_maxHeartbeats_2314_ = lean_ctor_get(v___y_2302_, 9);
v_quotContext_2315_ = lean_ctor_get(v___y_2302_, 10);
v_currMacroScope_2316_ = lean_ctor_get(v___y_2302_, 11);
v_diag_2317_ = lean_ctor_get_uint8(v___y_2302_, sizeof(void*)*14);
v_cancelTk_x3f_2318_ = lean_ctor_get(v___y_2302_, 12);
v_suppressElabErrors_2319_ = lean_ctor_get_uint8(v___y_2302_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2320_ = lean_ctor_get(v___y_2302_, 13);
v_ref_2321_ = l_Lean_replaceRef(v_ref_2300_, v_ref_2310_);
lean_inc_ref(v_inheritedTraceOptions_2320_);
lean_inc(v_cancelTk_x3f_2318_);
lean_inc(v_currMacroScope_2316_);
lean_inc(v_quotContext_2315_);
lean_inc(v_maxHeartbeats_2314_);
lean_inc(v_initHeartbeats_2313_);
lean_inc(v_openDecls_2312_);
lean_inc(v_currNamespace_2311_);
lean_inc(v_maxRecDepth_2309_);
lean_inc(v_currRecDepth_2308_);
lean_inc_ref(v_options_2307_);
lean_inc_ref(v_fileMap_2306_);
lean_inc_ref(v_fileName_2305_);
v___x_2322_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2322_, 0, v_fileName_2305_);
lean_ctor_set(v___x_2322_, 1, v_fileMap_2306_);
lean_ctor_set(v___x_2322_, 2, v_options_2307_);
lean_ctor_set(v___x_2322_, 3, v_currRecDepth_2308_);
lean_ctor_set(v___x_2322_, 4, v_maxRecDepth_2309_);
lean_ctor_set(v___x_2322_, 5, v_ref_2321_);
lean_ctor_set(v___x_2322_, 6, v_currNamespace_2311_);
lean_ctor_set(v___x_2322_, 7, v_openDecls_2312_);
lean_ctor_set(v___x_2322_, 8, v_initHeartbeats_2313_);
lean_ctor_set(v___x_2322_, 9, v_maxHeartbeats_2314_);
lean_ctor_set(v___x_2322_, 10, v_quotContext_2315_);
lean_ctor_set(v___x_2322_, 11, v_currMacroScope_2316_);
lean_ctor_set(v___x_2322_, 12, v_cancelTk_x3f_2318_);
lean_ctor_set(v___x_2322_, 13, v_inheritedTraceOptions_2320_);
lean_ctor_set_uint8(v___x_2322_, sizeof(void*)*14, v_diag_2317_);
lean_ctor_set_uint8(v___x_2322_, sizeof(void*)*14 + 1, v_suppressElabErrors_2319_);
v___x_2323_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2301_, v___x_2322_, v___y_2303_);
lean_dec_ref_known(v___x_2322_, 14);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_2324_, lean_object* v_msg_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2324_, v_msg_2325_, v___y_2326_, v___y_2327_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v_ref_2324_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_2330_, lean_object* v_msg_2331_, lean_object* v_declHint_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v___x_2336_; lean_object* v_a_2337_; lean_object* v___x_2338_; 
v___x_2336_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2331_, v_declHint_2332_, v___y_2333_, v___y_2334_);
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref(v___x_2336_);
v___x_2338_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2330_, v_a_2337_, v___y_2333_, v___y_2334_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2339_, lean_object* v_msg_2340_, lean_object* v_declHint_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2339_, v_msg_2340_, v_declHint_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v_ref_2339_);
return v_res_2345_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_2348_ = l_Lean_stringToMessageData(v___x_2347_);
return v___x_2348_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2));
v___x_2351_ = l_Lean_stringToMessageData(v___x_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_2352_, lean_object* v_constName_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v___x_2357_; uint8_t v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2357_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_2358_ = 0;
lean_inc(v_constName_2353_);
v___x_2359_ = l_Lean_MessageData_ofConstName(v_constName_2353_, v___x_2358_);
v___x_2360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2357_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_2362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2360_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
v___x_2363_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2352_, v___x_2362_, v_constName_2353_, v___y_2354_, v___y_2355_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2364_, lean_object* v_constName_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2364_, v_constName_2365_, v___y_2366_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v_ref_2364_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v_ref_2374_; lean_object* v___x_2375_; 
v_ref_2374_ = lean_ctor_get(v___y_2371_, 5);
v___x_2375_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2374_, v_constName_2370_, v___y_2371_, v___y_2372_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object* v_constName_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v___x_2385_; lean_object* v_env_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; 
v___x_2385_ = lean_st_ref_get(v___y_2383_);
v_env_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc_ref(v_env_2386_);
lean_dec(v___x_2385_);
v___x_2387_ = 0;
lean_inc(v_constName_2381_);
v___x_2388_ = l_Lean_Environment_findConstVal_x3f(v_env_2386_, v_constName_2381_, v___x_2387_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2381_, v___y_2382_, v___y_2383_);
return v___x_2389_;
}
else
{
lean_object* v_val_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec(v_constName_2381_);
v_val_2390_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2388_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_val_2390_);
lean_dec(v___x_2388_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
lean_ctor_set_tag(v___x_2392_, 0);
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_val_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
if (lean_obj_tag(v_a_2403_) == 0)
{
lean_object* v___x_2405_; 
v___x_2405_ = l_List_reverse___redArg(v_a_2404_);
return v___x_2405_;
}
else
{
lean_object* v_head_2406_; lean_object* v_tail_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2416_; 
v_head_2406_ = lean_ctor_get(v_a_2403_, 0);
v_tail_2407_ = lean_ctor_get(v_a_2403_, 1);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_a_2403_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2409_ = v_a_2403_;
v_isShared_2410_ = v_isSharedCheck_2416_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_tail_2407_);
lean_inc(v_head_2406_);
lean_dec(v_a_2403_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2416_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2411_ = l_Lean_mkLevelParam(v_head_2406_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 1, v_a_2404_);
lean_ctor_set(v___x_2409_, 0, v___x_2411_);
v___x_2413_ = v___x_2409_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2415_, 1, v_a_2404_);
v___x_2413_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
v_a_2403_ = v_tail_2407_;
v_a_2404_ = v___x_2413_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object* v_constName_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v___x_2421_; 
lean_inc(v_constName_2417_);
v___x_2421_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2417_, v___y_2418_, v___y_2419_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2433_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2424_ = v___x_2421_;
v_isShared_2425_ = v_isSharedCheck_2433_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2421_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2433_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v_levelParams_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2431_; 
v_levelParams_2426_ = lean_ctor_get(v_a_2422_, 1);
lean_inc(v_levelParams_2426_);
lean_dec(v_a_2422_);
v___x_2427_ = lean_box(0);
v___x_2428_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_2426_, v___x_2427_);
v___x_2429_ = l_Lean_mkConst(v_constName_2417_, v___x_2428_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v___x_2429_);
v___x_2431_ = v___x_2424_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2429_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec(v_constName_2417_);
v_a_2434_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2421_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2421_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object* v_constName_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object* v_stx_2447_, lean_object* v_n_2448_, lean_object* v_expectedType_x3f_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_2448_, v___y_2450_, v___y_2451_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
lean_dec_ref_known(v___x_2453_, 1);
v___x_2455_ = lean_box(0);
v___x_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
lean_ctor_set(v___x_2456_, 1, v_stx_2447_);
v___x_2457_ = l_Lean_LocalContext_empty;
v___x_2458_ = 0;
v___x_2459_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2459_, 0, v___x_2456_);
lean_ctor_set(v___x_2459_, 1, v___x_2457_);
lean_ctor_set(v___x_2459_, 2, v_expectedType_x3f_2449_);
lean_ctor_set(v___x_2459_, 3, v_a_2454_);
lean_ctor_set_uint8(v___x_2459_, sizeof(void*)*4, v___x_2458_);
lean_ctor_set_uint8(v___x_2459_, sizeof(void*)*4 + 1, v___x_2458_);
v___x_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
v___x_2461_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_2460_, v___y_2450_, v___y_2451_);
return v___x_2461_;
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec(v_expectedType_x3f_2449_);
lean_dec(v_stx_2447_);
v_a_2462_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2453_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2453_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object* v_stx_2470_, lean_object* v_n_2471_, lean_object* v_expectedType_x3f_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_2470_, v_n_2471_, v_expectedType_x3f_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object* v_id_2477_, lean_object* v_expectedType_x3f_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_){
_start:
{
lean_object* v___x_2482_; 
lean_inc(v_id_2477_);
v___x_2482_ = l_Lean_realizeGlobalConstNoOverload(v_id_2477_, v_a_2479_, v_a_2480_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2510_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2485_ = v___x_2482_;
v_isShared_2486_ = v_isSharedCheck_2510_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2510_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; lean_object* v_infoState_2488_; uint8_t v_enabled_2489_; 
v___x_2487_ = lean_st_ref_get(v_a_2480_);
v_infoState_2488_ = lean_ctor_get(v___x_2487_, 7);
lean_inc_ref(v_infoState_2488_);
lean_dec(v___x_2487_);
v_enabled_2489_ = lean_ctor_get_uint8(v_infoState_2488_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2488_);
if (v_enabled_2489_ == 0)
{
lean_object* v___x_2491_; 
lean_dec(v_expectedType_x3f_2478_);
lean_dec(v_id_2477_);
if (v_isShared_2486_ == 0)
{
v___x_2491_ = v___x_2485_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2483_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
else
{
lean_object* v___x_2493_; 
lean_del_object(v___x_2485_);
lean_inc(v_a_2483_);
v___x_2493_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2477_, v_a_2483_, v_expectedType_x3f_2478_, v_a_2479_, v_a_2480_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2500_ == 0)
{
lean_object* v_unused_2501_; 
v_unused_2501_ = lean_ctor_get(v___x_2493_, 0);
lean_dec(v_unused_2501_);
v___x_2495_ = v___x_2493_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_dec(v___x_2493_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v_a_2483_);
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2483_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
lean_dec(v_a_2483_);
v_a_2502_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___x_2493_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2493_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2478_);
lean_dec(v_id_2477_);
return v___x_2482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object* v_id_2511_, lean_object* v_expectedType_x3f_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_2511_, v_expectedType_x3f_2512_, v_a_2513_, v_a_2514_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object* v_t_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2517_, v___y_2519_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2527_, lean_object* v_constName_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2528_, v___y_2529_, v___y_2530_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2533_, lean_object* v_constName_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2533_, v_constName_2534_, v___y_2535_, v___y_2536_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2539_, lean_object* v_ref_2540_, lean_object* v_constName_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2540_, v_constName_2541_, v___y_2542_, v___y_2543_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2546_, lean_object* v_ref_2547_, lean_object* v_constName_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_2546_, v_ref_2547_, v_constName_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v_ref_2547_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2553_, lean_object* v_ref_2554_, lean_object* v_msg_2555_, lean_object* v_declHint_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2554_, v_msg_2555_, v_declHint_2556_, v___y_2557_, v___y_2558_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2561_, lean_object* v_ref_2562_, lean_object* v_msg_2563_, lean_object* v_declHint_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_2561_, v_ref_2562_, v_msg_2563_, v_declHint_2564_, v___y_2565_, v___y_2566_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v_ref_2562_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_2569_, lean_object* v_declHint_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2569_, v_declHint_2570_, v___y_2572_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2575_, lean_object* v_declHint_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2575_, v_declHint_2576_, v___y_2577_, v___y_2578_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_2581_, lean_object* v_ref_2582_, lean_object* v_msg_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2582_, v_msg_2583_, v___y_2584_, v___y_2585_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2588_, lean_object* v_ref_2589_, lean_object* v_msg_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_2588_, v_ref_2589_, v_msg_2590_, v___y_2591_, v___y_2592_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v_ref_2589_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_2595_, lean_object* v_msg_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v___x_2600_; 
v___x_2600_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2596_, v___y_2597_, v___y_2598_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_2601_, lean_object* v_msg_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_2601_, v_msg_2602_, v___y_2603_, v___y_2604_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object* v_id_2607_, lean_object* v_expectedType_x3f_2608_, lean_object* v_as_x27_2609_, lean_object* v_b_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
if (lean_obj_tag(v_as_x27_2609_) == 0)
{
lean_object* v___x_2614_; 
lean_dec(v_expectedType_x3f_2608_);
lean_dec(v_id_2607_);
v___x_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2614_, 0, v_b_2610_);
return v___x_2614_;
}
else
{
lean_object* v_head_2615_; lean_object* v_tail_2616_; lean_object* v___x_2617_; 
v_head_2615_ = lean_ctor_get(v_as_x27_2609_, 0);
v_tail_2616_ = lean_ctor_get(v_as_x27_2609_, 1);
lean_inc(v_expectedType_x3f_2608_);
lean_inc(v_head_2615_);
lean_inc(v_id_2607_);
v___x_2617_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2607_, v_head_2615_, v_expectedType_x3f_2608_, v___y_2611_, v___y_2612_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v___x_2618_; 
lean_dec_ref_known(v___x_2617_, 1);
v___x_2618_ = lean_box(0);
v_as_x27_2609_ = v_tail_2616_;
v_b_2610_ = v___x_2618_;
goto _start;
}
else
{
lean_dec(v_expectedType_x3f_2608_);
lean_dec(v_id_2607_);
return v___x_2617_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object* v_id_2620_, lean_object* v_expectedType_x3f_2621_, lean_object* v_as_x27_2622_, lean_object* v_b_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2620_, v_expectedType_x3f_2621_, v_as_x27_2622_, v_b_2623_, v___y_2624_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v_as_x27_2622_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object* v_id_2628_, lean_object* v_expectedType_x3f_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
lean_object* v___x_2633_; 
lean_inc(v_id_2628_);
v___x_2633_ = l_Lean_realizeGlobalConst(v_id_2628_, v_a_2630_, v_a_2631_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2662_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2636_ = v___x_2633_;
v_isShared_2637_ = v_isSharedCheck_2662_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2633_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2662_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; lean_object* v_infoState_2639_; uint8_t v_enabled_2640_; 
v___x_2638_ = lean_st_ref_get(v_a_2631_);
v_infoState_2639_ = lean_ctor_get(v___x_2638_, 7);
lean_inc_ref(v_infoState_2639_);
lean_dec(v___x_2638_);
v_enabled_2640_ = lean_ctor_get_uint8(v_infoState_2639_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2639_);
if (v_enabled_2640_ == 0)
{
lean_object* v___x_2642_; 
lean_dec(v_expectedType_x3f_2629_);
lean_dec(v_id_2628_);
if (v_isShared_2637_ == 0)
{
v___x_2642_ = v___x_2636_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2634_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
else
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
lean_del_object(v___x_2636_);
v___x_2644_ = lean_box(0);
v___x_2645_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2628_, v_expectedType_x3f_2629_, v_a_2634_, v___x_2644_, v_a_2630_, v_a_2631_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2652_ == 0)
{
lean_object* v_unused_2653_; 
v_unused_2653_ = lean_ctor_get(v___x_2645_, 0);
lean_dec(v_unused_2653_);
v___x_2647_ = v___x_2645_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_dec(v___x_2645_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v_a_2634_);
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2634_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec(v_a_2634_);
v_a_2654_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2645_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2645_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2629_);
lean_dec(v_id_2628_);
return v___x_2633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object* v_id_2663_, lean_object* v_expectedType_x3f_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_2663_, v_expectedType_x3f_2664_, v_a_2665_, v_a_2666_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object* v_id_2669_, lean_object* v_expectedType_x3f_2670_, lean_object* v_as_2671_, lean_object* v_as_x27_2672_, lean_object* v_b_2673_, lean_object* v_a_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2669_, v_expectedType_x3f_2670_, v_as_x27_2672_, v_b_2673_, v___y_2675_, v___y_2676_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object* v_id_2679_, lean_object* v_expectedType_x3f_2680_, lean_object* v_as_2681_, lean_object* v_as_x27_2682_, lean_object* v_b_2683_, lean_object* v_a_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_2679_, v_expectedType_x3f_2680_, v_as_2681_, v_as_x27_2682_, v_b_2683_, v_a_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v_as_x27_2682_);
lean_dec(v_as_2681_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object* v_ref_2689_, lean_object* v_as_x27_2690_, lean_object* v_b_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
if (lean_obj_tag(v_as_x27_2690_) == 0)
{
lean_object* v___x_2695_; 
lean_dec(v_ref_2689_);
v___x_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2695_, 0, v_b_2691_);
return v___x_2695_;
}
else
{
lean_object* v_head_2696_; lean_object* v_tail_2697_; lean_object* v_fst_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v_head_2696_ = lean_ctor_get(v_as_x27_2690_, 0);
v_tail_2697_ = lean_ctor_get(v_as_x27_2690_, 1);
v_fst_2698_ = lean_ctor_get(v_head_2696_, 0);
v___x_2699_ = lean_box(0);
lean_inc(v_fst_2698_);
lean_inc(v_ref_2689_);
v___x_2700_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_2689_, v_fst_2698_, v___x_2699_, v___y_2692_, v___y_2693_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v___x_2701_; 
lean_dec_ref_known(v___x_2700_, 1);
v___x_2701_ = lean_box(0);
v_as_x27_2690_ = v_tail_2697_;
v_b_2691_ = v___x_2701_;
goto _start;
}
else
{
lean_dec(v_ref_2689_);
return v___x_2700_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object* v_ref_2703_, lean_object* v_as_x27_2704_, lean_object* v_b_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2703_, v_as_x27_2704_, v_b_2705_, v___y_2706_, v___y_2707_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v_as_x27_2704_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object* v_ref_2710_, lean_object* v_id_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_Lean_realizeGlobalName(v_id_2711_, v_a_2712_, v_a_2713_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2744_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2744_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2744_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2720_; lean_object* v_infoState_2721_; uint8_t v_enabled_2722_; 
v___x_2720_ = lean_st_ref_get(v_a_2713_);
v_infoState_2721_ = lean_ctor_get(v___x_2720_, 7);
lean_inc_ref(v_infoState_2721_);
lean_dec(v___x_2720_);
v_enabled_2722_ = lean_ctor_get_uint8(v_infoState_2721_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2721_);
if (v_enabled_2722_ == 0)
{
lean_object* v___x_2724_; 
lean_dec(v_ref_2710_);
if (v_isShared_2719_ == 0)
{
v___x_2724_ = v___x_2718_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2716_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
else
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
lean_del_object(v___x_2718_);
v___x_2726_ = lean_box(0);
v___x_2727_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2710_, v_a_2716_, v___x_2726_, v_a_2712_, v_a_2713_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2734_ == 0)
{
lean_object* v_unused_2735_; 
v_unused_2735_ = lean_ctor_get(v___x_2727_, 0);
lean_dec(v_unused_2735_);
v___x_2729_ = v___x_2727_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_dec(v___x_2727_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v_a_2716_);
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2716_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
else
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_dec(v_a_2716_);
v_a_2736_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2727_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2727_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
}
}
else
{
lean_dec(v_ref_2710_);
return v___x_2715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object* v_ref_2745_, lean_object* v_id_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_2745_, v_id_2746_, v_a_2747_, v_a_2748_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object* v_ref_2751_, lean_object* v_as_2752_, lean_object* v_as_x27_2753_, lean_object* v_b_2754_, lean_object* v_a_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2751_, v_as_x27_2753_, v_b_2754_, v___y_2756_, v___y_2757_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object* v_ref_2760_, lean_object* v_as_2761_, lean_object* v_as_x27_2762_, lean_object* v_b_2763_, lean_object* v_a_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_2760_, v_as_2761_, v_as_x27_2762_, v_b_2763_, v_a_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v_as_x27_2762_);
lean_dec(v_as_2761_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object* v_self_2769_){
_start:
{
lean_object* v_fst_2770_; 
v_fst_2770_ = lean_ctor_get(v_self_2769_, 0);
lean_inc(v_fst_2770_);
return v_fst_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object* v_self_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_2771_);
lean_dec_ref(v_self_2771_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object* v_info_2773_, lean_object* v_treesSaved_2774_, lean_object* v_s_2775_){
_start:
{
if (lean_obj_tag(v_info_2773_) == 0)
{
uint8_t v_enabled_2776_; lean_object* v_assignment_2777_; lean_object* v_lazyAssignment_2778_; lean_object* v_trees_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2789_; 
v_enabled_2776_ = lean_ctor_get_uint8(v_s_2775_, sizeof(void*)*3);
v_assignment_2777_ = lean_ctor_get(v_s_2775_, 0);
v_lazyAssignment_2778_ = lean_ctor_get(v_s_2775_, 1);
v_trees_2779_ = lean_ctor_get(v_s_2775_, 2);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_s_2775_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2781_ = v_s_2775_;
v_isShared_2782_ = v_isSharedCheck_2789_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_trees_2779_);
lean_inc(v_lazyAssignment_2778_);
lean_inc(v_assignment_2777_);
lean_dec(v_s_2775_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2789_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v_val_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v_val_2783_ = lean_ctor_get(v_info_2773_, 0);
lean_inc(v_val_2783_);
lean_dec_ref_known(v_info_2773_, 1);
v___x_2784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2784_, 0, v_val_2783_);
lean_ctor_set(v___x_2784_, 1, v_trees_2779_);
v___x_2785_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2774_, v___x_2784_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 2, v___x_2785_);
v___x_2787_ = v___x_2781_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_assignment_2777_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v_lazyAssignment_2778_);
lean_ctor_set(v_reuseFailAlloc_2788_, 2, v___x_2785_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, sizeof(void*)*3, v_enabled_2776_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
else
{
uint8_t v_enabled_2790_; lean_object* v_assignment_2791_; lean_object* v_lazyAssignment_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2808_; 
v_enabled_2790_ = lean_ctor_get_uint8(v_s_2775_, sizeof(void*)*3);
v_assignment_2791_ = lean_ctor_get(v_s_2775_, 0);
v_lazyAssignment_2792_ = lean_ctor_get(v_s_2775_, 1);
v_isSharedCheck_2808_ = !lean_is_exclusive(v_s_2775_);
if (v_isSharedCheck_2808_ == 0)
{
lean_object* v_unused_2809_; 
v_unused_2809_ = lean_ctor_get(v_s_2775_, 2);
lean_dec(v_unused_2809_);
v___x_2794_ = v_s_2775_;
v_isShared_2795_ = v_isSharedCheck_2808_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_lazyAssignment_2792_);
lean_inc(v_assignment_2791_);
lean_dec(v_s_2775_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2808_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v_val_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2807_; 
v_val_2796_ = lean_ctor_get(v_info_2773_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_info_2773_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2798_ = v_info_2773_;
v_isShared_2799_ = v_isSharedCheck_2807_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_val_2796_);
lean_dec(v_info_2773_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2807_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
lean_ctor_set_tag(v___x_2798_, 2);
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_val_2796_);
v___x_2801_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2802_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2774_, v___x_2801_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 2, v___x_2802_);
v___x_2804_ = v___x_2794_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_assignment_2791_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_lazyAssignment_2792_);
lean_ctor_set(v_reuseFailAlloc_2805_, 2, v___x_2802_);
lean_ctor_set_uint8(v_reuseFailAlloc_2805_, sizeof(void*)*3, v_enabled_2790_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object* v_treesSaved_2810_, lean_object* v_modifyInfoState_2811_, lean_object* v_info_2812_){
_start:
{
lean_object* v___f_2813_; lean_object* v___x_2814_; 
v___f_2813_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2813_, 0, v_info_2812_);
lean_closure_set(v___f_2813_, 1, v_treesSaved_2810_);
v___x_2814_ = lean_apply_1(v_modifyInfoState_2811_, v___f_2813_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object* v___f_2815_, lean_object* v_info_2816_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = lean_apply_1(v___f_2815_, v_info_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object* v_toPure_2818_, lean_object* v_toBind_2819_, lean_object* v___f_2820_, lean_object* v_____do__lift_2821_){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2822_, 0, v_____do__lift_2821_);
v___x_2823_ = lean_apply_2(v_toPure_2818_, lean_box(0), v___x_2822_);
v___x_2824_ = lean_apply_4(v_toBind_2819_, lean_box(0), lean_box(0), v___x_2823_, v___f_2820_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object* v_toBind_2825_, lean_object* v_mkInfoOnError_2826_, lean_object* v___f_2827_, lean_object* v_mkInfo_2828_, lean_object* v___f_2829_, lean_object* v_a_x3f_2830_){
_start:
{
if (lean_obj_tag(v_a_x3f_2830_) == 0)
{
lean_object* v___x_2831_; 
lean_dec(v___f_2829_);
lean_dec(v_mkInfo_2828_);
v___x_2831_ = lean_apply_4(v_toBind_2825_, lean_box(0), lean_box(0), v_mkInfoOnError_2826_, v___f_2827_);
return v___x_2831_;
}
else
{
lean_object* v_val_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
lean_dec(v___f_2827_);
lean_dec(v_mkInfoOnError_2826_);
v_val_2832_ = lean_ctor_get(v_a_x3f_2830_, 0);
lean_inc(v_val_2832_);
lean_dec_ref_known(v_a_x3f_2830_, 1);
v___x_2833_ = lean_apply_1(v_mkInfo_2828_, v_val_2832_);
v___x_2834_ = lean_apply_4(v_toBind_2825_, lean_box(0), lean_box(0), v___x_2833_, v___f_2829_);
return v___x_2834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object* v_toApplicative_2835_, lean_object* v_modifyInfoState_2836_, lean_object* v_toBind_2837_, lean_object* v_mkInfoOnError_2838_, lean_object* v_mkInfo_2839_, lean_object* v_inst_2840_, lean_object* v_x_2841_, lean_object* v___f_2842_, lean_object* v_treesSaved_2843_){
_start:
{
lean_object* v_toFunctor_2844_; lean_object* v_toPure_2845_; lean_object* v_map_2846_; lean_object* v___f_2847_; lean_object* v___f_2848_; lean_object* v___f_2849_; lean_object* v___f_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v_toFunctor_2844_ = lean_ctor_get(v_toApplicative_2835_, 0);
lean_inc_ref(v_toFunctor_2844_);
v_toPure_2845_ = lean_ctor_get(v_toApplicative_2835_, 1);
lean_inc(v_toPure_2845_);
lean_dec_ref(v_toApplicative_2835_);
v_map_2846_ = lean_ctor_get(v_toFunctor_2844_, 0);
lean_inc(v_map_2846_);
lean_dec_ref(v_toFunctor_2844_);
v___f_2847_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2847_, 0, v_treesSaved_2843_);
lean_closure_set(v___f_2847_, 1, v_modifyInfoState_2836_);
v___f_2848_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2848_, 0, v___f_2847_);
lean_inc_ref(v___f_2848_);
lean_inc(v_toBind_2837_);
v___f_2849_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_2849_, 0, v_toPure_2845_);
lean_closure_set(v___f_2849_, 1, v_toBind_2837_);
lean_closure_set(v___f_2849_, 2, v___f_2848_);
v___f_2850_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__6), 6, 5);
lean_closure_set(v___f_2850_, 0, v_toBind_2837_);
lean_closure_set(v___f_2850_, 1, v_mkInfoOnError_2838_);
lean_closure_set(v___f_2850_, 2, v___f_2849_);
lean_closure_set(v___f_2850_, 3, v_mkInfo_2839_);
lean_closure_set(v___f_2850_, 4, v___f_2848_);
v___x_2851_ = lean_apply_4(v_inst_2840_, lean_box(0), lean_box(0), v_x_2841_, v___f_2850_);
v___x_2852_ = lean_apply_4(v_map_2846_, lean_box(0), lean_box(0), v___f_2842_, v___x_2851_);
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
lean_object* v_toApplicative_2876_; lean_object* v_toBind_2877_; lean_object* v_getInfoState_2878_; lean_object* v_modifyInfoState_2879_; lean_object* v___f_2880_; lean_object* v___f_2881_; lean_object* v___f_2882_; lean_object* v___x_2883_; 
v_toApplicative_2876_ = lean_ctor_get(v_inst_2870_, 0);
v_toBind_2877_ = lean_ctor_get(v_inst_2870_, 1);
lean_inc_n(v_toBind_2877_, 3);
v_getInfoState_2878_ = lean_ctor_get(v_inst_2871_, 0);
lean_inc(v_getInfoState_2878_);
v_modifyInfoState_2879_ = lean_ctor_get(v_inst_2871_, 1);
v___f_2880_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2873_);
lean_inc(v_modifyInfoState_2879_);
lean_inc_ref(v_toApplicative_2876_);
v___f_2881_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__5), 9, 8);
lean_closure_set(v___f_2881_, 0, v_toApplicative_2876_);
lean_closure_set(v___f_2881_, 1, v_modifyInfoState_2879_);
lean_closure_set(v___f_2881_, 2, v_toBind_2877_);
lean_closure_set(v___f_2881_, 3, v_mkInfoOnError_2875_);
lean_closure_set(v___f_2881_, 4, v_mkInfo_2874_);
lean_closure_set(v___f_2881_, 5, v_inst_2872_);
lean_closure_set(v___f_2881_, 6, v_x_2873_);
lean_closure_set(v___f_2881_, 7, v___f_2880_);
v___f_2882_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2882_, 0, v_x_2873_);
lean_closure_set(v___f_2882_, 1, v_inst_2870_);
lean_closure_set(v___f_2882_, 2, v_inst_2871_);
lean_closure_set(v___f_2882_, 3, v_toBind_2877_);
lean_closure_set(v___f_2882_, 4, v___f_2881_);
v___x_2883_ = lean_apply_4(v_toBind_2877_, lean_box(0), lean_box(0), v_getInfoState_2878_, v___f_2882_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* v_m_2884_, lean_object* v_inst_2885_, lean_object* v_inst_2886_, lean_object* v_00_u03b1_2887_, lean_object* v_inst_2888_, lean_object* v_x_2889_, lean_object* v_mkInfo_2890_, lean_object* v_mkInfoOnError_2891_){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Lean_Elab_withInfoContext_x27___redArg(v_inst_2885_, v_inst_2886_, v_inst_2888_, v_x_2889_, v_mkInfo_2890_, v_mkInfoOnError_2891_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object* v_treesSaved_2893_, lean_object* v_tree_2894_, lean_object* v_s_2895_){
_start:
{
uint8_t v_enabled_2896_; lean_object* v_assignment_2897_; lean_object* v_lazyAssignment_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2906_; 
v_enabled_2896_ = lean_ctor_get_uint8(v_s_2895_, sizeof(void*)*3);
v_assignment_2897_ = lean_ctor_get(v_s_2895_, 0);
v_lazyAssignment_2898_ = lean_ctor_get(v_s_2895_, 1);
v_isSharedCheck_2906_ = !lean_is_exclusive(v_s_2895_);
if (v_isSharedCheck_2906_ == 0)
{
lean_object* v_unused_2907_; 
v_unused_2907_ = lean_ctor_get(v_s_2895_, 2);
lean_dec(v_unused_2907_);
v___x_2900_ = v_s_2895_;
v_isShared_2901_ = v_isSharedCheck_2906_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_lazyAssignment_2898_);
lean_inc(v_assignment_2897_);
lean_dec(v_s_2895_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2906_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2902_; lean_object* v___x_2904_; 
v___x_2902_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2893_, v_tree_2894_);
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 2, v___x_2902_);
v___x_2904_ = v___x_2900_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_assignment_2897_);
lean_ctor_set(v_reuseFailAlloc_2905_, 1, v_lazyAssignment_2898_);
lean_ctor_set(v_reuseFailAlloc_2905_, 2, v___x_2902_);
lean_ctor_set_uint8(v_reuseFailAlloc_2905_, sizeof(void*)*3, v_enabled_2896_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object* v_treesSaved_2908_, lean_object* v_modifyInfoState_2909_, lean_object* v_tree_2910_){
_start:
{
lean_object* v___f_2911_; lean_object* v___x_2912_; 
v___f_2911_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2911_, 0, v_treesSaved_2908_);
lean_closure_set(v___f_2911_, 1, v_tree_2910_);
v___x_2912_ = lean_apply_1(v_modifyInfoState_2909_, v___f_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object* v_mkInfoTree_2913_, lean_object* v_toBind_2914_, lean_object* v___f_2915_, lean_object* v_st_2916_){
_start:
{
lean_object* v_trees_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v_trees_2917_ = lean_ctor_get(v_st_2916_, 2);
lean_inc_ref(v_trees_2917_);
lean_dec_ref(v_st_2916_);
v___x_2918_ = lean_apply_1(v_mkInfoTree_2913_, v_trees_2917_);
v___x_2919_ = lean_apply_4(v_toBind_2914_, lean_box(0), lean_box(0), v___x_2918_, v___f_2915_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object* v_toBind_2920_, lean_object* v_getInfoState_2921_, lean_object* v___f_2922_, lean_object* v_x_2923_){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = lean_apply_4(v_toBind_2920_, lean_box(0), lean_box(0), v_getInfoState_2921_, v___f_2922_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object* v_toBind_2925_, lean_object* v_getInfoState_2926_, lean_object* v___f_2927_, lean_object* v_x_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(v_toBind_2925_, v_getInfoState_2926_, v___f_2927_, v_x_2928_);
lean_dec(v_x_2928_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object* v_toApplicative_2930_, lean_object* v_modifyInfoState_2931_, lean_object* v_mkInfoTree_2932_, lean_object* v_toBind_2933_, lean_object* v_getInfoState_2934_, lean_object* v_inst_2935_, lean_object* v_x_2936_, lean_object* v___f_2937_, lean_object* v_treesSaved_2938_){
_start:
{
lean_object* v_toFunctor_2939_; lean_object* v_map_2940_; lean_object* v___f_2941_; lean_object* v___f_2942_; lean_object* v___f_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v_toFunctor_2939_ = lean_ctor_get(v_toApplicative_2930_, 0);
lean_inc_ref(v_toFunctor_2939_);
lean_dec_ref(v_toApplicative_2930_);
v_map_2940_ = lean_ctor_get(v_toFunctor_2939_, 0);
lean_inc(v_map_2940_);
lean_dec_ref(v_toFunctor_2939_);
v___f_2941_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2941_, 0, v_treesSaved_2938_);
lean_closure_set(v___f_2941_, 1, v_modifyInfoState_2931_);
lean_inc(v_toBind_2933_);
v___f_2942_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2942_, 0, v_mkInfoTree_2932_);
lean_closure_set(v___f_2942_, 1, v_toBind_2933_);
lean_closure_set(v___f_2942_, 2, v___f_2941_);
v___f_2943_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_2943_, 0, v_toBind_2933_);
lean_closure_set(v___f_2943_, 1, v_getInfoState_2934_);
lean_closure_set(v___f_2943_, 2, v___f_2942_);
v___x_2944_ = lean_apply_4(v_inst_2935_, lean_box(0), lean_box(0), v_x_2936_, v___f_2943_);
v___x_2945_ = lean_apply_4(v_map_2940_, lean_box(0), lean_box(0), v___f_2937_, v___x_2944_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object* v_inst_2946_, lean_object* v_inst_2947_, lean_object* v_inst_2948_, lean_object* v_x_2949_, lean_object* v_mkInfoTree_2950_){
_start:
{
lean_object* v_toApplicative_2951_; lean_object* v_toBind_2952_; lean_object* v_getInfoState_2953_; lean_object* v_modifyInfoState_2954_; lean_object* v___f_2955_; lean_object* v___f_2956_; lean_object* v___f_2957_; lean_object* v___x_2958_; 
v_toApplicative_2951_ = lean_ctor_get(v_inst_2946_, 0);
v_toBind_2952_ = lean_ctor_get(v_inst_2946_, 1);
lean_inc_n(v_toBind_2952_, 3);
v_getInfoState_2953_ = lean_ctor_get(v_inst_2947_, 0);
lean_inc_n(v_getInfoState_2953_, 2);
v_modifyInfoState_2954_ = lean_ctor_get(v_inst_2947_, 1);
v___f_2955_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2949_);
lean_inc(v_modifyInfoState_2954_);
lean_inc_ref(v_toApplicative_2951_);
v___f_2956_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2956_, 0, v_toApplicative_2951_);
lean_closure_set(v___f_2956_, 1, v_modifyInfoState_2954_);
lean_closure_set(v___f_2956_, 2, v_mkInfoTree_2950_);
lean_closure_set(v___f_2956_, 3, v_toBind_2952_);
lean_closure_set(v___f_2956_, 4, v_getInfoState_2953_);
lean_closure_set(v___f_2956_, 5, v_inst_2948_);
lean_closure_set(v___f_2956_, 6, v_x_2949_);
lean_closure_set(v___f_2956_, 7, v___f_2955_);
v___f_2957_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2957_, 0, v_x_2949_);
lean_closure_set(v___f_2957_, 1, v_inst_2946_);
lean_closure_set(v___f_2957_, 2, v_inst_2947_);
lean_closure_set(v___f_2957_, 3, v_toBind_2952_);
lean_closure_set(v___f_2957_, 4, v___f_2956_);
v___x_2958_ = lean_apply_4(v_toBind_2952_, lean_box(0), lean_box(0), v_getInfoState_2953_, v___f_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object* v_m_2959_, lean_object* v_inst_2960_, lean_object* v_inst_2961_, lean_object* v_00_u03b1_2962_, lean_object* v_inst_2963_, lean_object* v_x_2964_, lean_object* v_mkInfoTree_2965_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_2960_, v_inst_2961_, v_inst_2963_, v_x_2964_, v_mkInfoTree_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object* v_trees_2967_, lean_object* v_toPure_2968_, lean_object* v_____do__lift_2969_){
_start:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2970_, 0, v_____do__lift_2969_);
lean_ctor_set(v___x_2970_, 1, v_trees_2967_);
v___x_2971_ = lean_apply_2(v_toPure_2968_, lean_box(0), v___x_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object* v_toPure_2972_, lean_object* v_toBind_2973_, lean_object* v_mkInfo_2974_, lean_object* v_trees_2975_){
_start:
{
lean_object* v___f_2976_; lean_object* v___x_2977_; 
v___f_2976_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2976_, 0, v_trees_2975_);
lean_closure_set(v___f_2976_, 1, v_toPure_2972_);
v___x_2977_ = lean_apply_4(v_toBind_2973_, lean_box(0), lean_box(0), v_mkInfo_2974_, v___f_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object* v_inst_2978_, lean_object* v_inst_2979_, lean_object* v_inst_2980_, lean_object* v_x_2981_, lean_object* v_mkInfo_2982_){
_start:
{
lean_object* v_toApplicative_2983_; lean_object* v_toBind_2984_; lean_object* v_toPure_2985_; lean_object* v___f_2986_; lean_object* v___x_2987_; 
v_toApplicative_2983_ = lean_ctor_get(v_inst_2978_, 0);
v_toBind_2984_ = lean_ctor_get(v_inst_2978_, 1);
v_toPure_2985_ = lean_ctor_get(v_toApplicative_2983_, 1);
lean_inc(v_toBind_2984_);
lean_inc(v_toPure_2985_);
v___f_2986_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2986_, 0, v_toPure_2985_);
lean_closure_set(v___f_2986_, 1, v_toBind_2984_);
lean_closure_set(v___f_2986_, 2, v_mkInfo_2982_);
v___x_2987_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_2978_, v_inst_2979_, v_inst_2980_, v_x_2981_, v___f_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object* v_m_2988_, lean_object* v_inst_2989_, lean_object* v_inst_2990_, lean_object* v_00_u03b1_2991_, lean_object* v_inst_2992_, lean_object* v_x_2993_, lean_object* v_mkInfo_2994_){
_start:
{
lean_object* v_toApplicative_2995_; lean_object* v_toBind_2996_; lean_object* v_toPure_2997_; lean_object* v___f_2998_; lean_object* v___x_2999_; 
v_toApplicative_2995_ = lean_ctor_get(v_inst_2989_, 0);
v_toBind_2996_ = lean_ctor_get(v_inst_2989_, 1);
v_toPure_2997_ = lean_ctor_get(v_toApplicative_2995_, 1);
lean_inc(v_toBind_2996_);
lean_inc(v_toPure_2997_);
v___f_2998_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2998_, 0, v_toPure_2997_);
lean_closure_set(v___f_2998_, 1, v_toBind_2996_);
lean_closure_set(v___f_2998_, 2, v_mkInfo_2994_);
v___x_2999_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_2989_, v_inst_2990_, v_inst_2992_, v_x_2993_, v___f_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object* v_treesSaved_3000_, lean_object* v_trees_3001_, lean_object* v_s_3002_){
_start:
{
uint8_t v_enabled_3003_; lean_object* v_assignment_3004_; lean_object* v_lazyAssignment_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3013_; 
v_enabled_3003_ = lean_ctor_get_uint8(v_s_3002_, sizeof(void*)*3);
v_assignment_3004_ = lean_ctor_get(v_s_3002_, 0);
v_lazyAssignment_3005_ = lean_ctor_get(v_s_3002_, 1);
v_isSharedCheck_3013_ = !lean_is_exclusive(v_s_3002_);
if (v_isSharedCheck_3013_ == 0)
{
lean_object* v_unused_3014_; 
v_unused_3014_ = lean_ctor_get(v_s_3002_, 2);
lean_dec(v_unused_3014_);
v___x_3007_ = v_s_3002_;
v_isShared_3008_ = v_isSharedCheck_3013_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_lazyAssignment_3005_);
lean_inc(v_assignment_3004_);
lean_dec(v_s_3002_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3013_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3009_; lean_object* v___x_3011_; 
v___x_3009_ = l_Lean_PersistentArray_append___redArg(v_treesSaved_3000_, v_trees_3001_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 2, v___x_3009_);
v___x_3011_ = v___x_3007_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_assignment_3004_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_lazyAssignment_3005_);
lean_ctor_set(v_reuseFailAlloc_3012_, 2, v___x_3009_);
lean_ctor_set_uint8(v_reuseFailAlloc_3012_, sizeof(void*)*3, v_enabled_3003_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object* v_treesSaved_3015_, lean_object* v_trees_3016_, lean_object* v_s_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_3015_, v_trees_3016_, v_s_3017_);
lean_dec_ref(v_trees_3016_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object* v_treesSaved_3019_, lean_object* v_modifyInfoState_3020_, lean_object* v_trees_3021_){
_start:
{
lean_object* v___f_3022_; lean_object* v___x_3023_; 
v___f_3022_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3022_, 0, v_treesSaved_3019_);
lean_closure_set(v___f_3022_, 1, v_trees_3021_);
v___x_3023_ = lean_apply_1(v_modifyInfoState_3020_, v___f_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object* v_toPure_3024_, lean_object* v_tree_3025_, lean_object* v_____do__lift_3026_){
_start:
{
if (lean_obj_tag(v_____do__lift_3026_) == 0)
{
lean_object* v___x_3027_; 
v___x_3027_ = lean_apply_2(v_toPure_3024_, lean_box(0), v_tree_3025_);
return v___x_3027_;
}
else
{
lean_object* v_val_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v_val_3028_ = lean_ctor_get(v_____do__lift_3026_, 0);
lean_inc(v_val_3028_);
v___x_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3029_, 0, v_val_3028_);
lean_ctor_set(v___x_3029_, 1, v_tree_3025_);
v___x_3030_ = lean_apply_2(v_toPure_3024_, lean_box(0), v___x_3029_);
return v___x_3030_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object* v_toPure_3031_, lean_object* v_tree_3032_, lean_object* v_____do__lift_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_3031_, v_tree_3032_, v_____do__lift_3033_);
lean_dec(v_____do__lift_3033_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object* v_assignment_3035_, lean_object* v_toPure_3036_, lean_object* v_toBind_3037_, lean_object* v_ctx_x3f_3038_, lean_object* v_tree_3039_){
_start:
{
lean_object* v_tree_3040_; lean_object* v___f_3041_; lean_object* v___x_3042_; 
v_tree_3040_ = l_Lean_Elab_InfoTree_substitute(v_tree_3039_, v_assignment_3035_);
v___f_3041_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3041_, 0, v_toPure_3036_);
lean_closure_set(v___f_3041_, 1, v_tree_3040_);
v___x_3042_ = lean_apply_4(v_toBind_3037_, lean_box(0), lean_box(0), v_ctx_x3f_3038_, v___f_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object* v_assignment_3043_, lean_object* v_toPure_3044_, lean_object* v_toBind_3045_, lean_object* v_ctx_x3f_3046_, lean_object* v_tree_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(v_assignment_3043_, v_toPure_3044_, v_toBind_3045_, v_ctx_x3f_3046_, v_tree_3047_);
lean_dec_ref(v_assignment_3043_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object* v_toPure_3049_, lean_object* v_toBind_3050_, lean_object* v_ctx_x3f_3051_, lean_object* v_inst_3052_, lean_object* v___f_3053_, lean_object* v_st_3054_){
_start:
{
lean_object* v_assignment_3055_; lean_object* v_trees_3056_; lean_object* v___f_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v_assignment_3055_ = lean_ctor_get(v_st_3054_, 0);
lean_inc_ref(v_assignment_3055_);
v_trees_3056_ = lean_ctor_get(v_st_3054_, 2);
lean_inc_ref(v_trees_3056_);
lean_dec_ref(v_st_3054_);
lean_inc(v_toBind_3050_);
v___f_3057_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_3057_, 0, v_assignment_3055_);
lean_closure_set(v___f_3057_, 1, v_toPure_3049_);
lean_closure_set(v___f_3057_, 2, v_toBind_3050_);
lean_closure_set(v___f_3057_, 3, v_ctx_x3f_3051_);
v___x_3058_ = l_Lean_PersistentArray_mapM___redArg(v_inst_3052_, v___f_3057_, v_trees_3056_);
v___x_3059_ = lean_apply_4(v_toBind_3050_, lean_box(0), lean_box(0), v___x_3058_, v___f_3053_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object* v_toApplicative_3060_, lean_object* v_modifyInfoState_3061_, lean_object* v_toBind_3062_, lean_object* v_ctx_x3f_3063_, lean_object* v_inst_3064_, lean_object* v_getInfoState_3065_, lean_object* v_inst_3066_, lean_object* v_x_3067_, lean_object* v___f_3068_, lean_object* v_treesSaved_3069_){
_start:
{
lean_object* v_toFunctor_3070_; lean_object* v_toPure_3071_; lean_object* v_map_3072_; lean_object* v___f_3073_; lean_object* v___f_3074_; lean_object* v___f_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v_toFunctor_3070_ = lean_ctor_get(v_toApplicative_3060_, 0);
lean_inc_ref(v_toFunctor_3070_);
v_toPure_3071_ = lean_ctor_get(v_toApplicative_3060_, 1);
lean_inc(v_toPure_3071_);
lean_dec_ref(v_toApplicative_3060_);
v_map_3072_ = lean_ctor_get(v_toFunctor_3070_, 0);
lean_inc(v_map_3072_);
lean_dec_ref(v_toFunctor_3070_);
v___f_3073_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3073_, 0, v_treesSaved_3069_);
lean_closure_set(v___f_3073_, 1, v_modifyInfoState_3061_);
lean_inc(v_toBind_3062_);
v___f_3074_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4), 6, 5);
lean_closure_set(v___f_3074_, 0, v_toPure_3071_);
lean_closure_set(v___f_3074_, 1, v_toBind_3062_);
lean_closure_set(v___f_3074_, 2, v_ctx_x3f_3063_);
lean_closure_set(v___f_3074_, 3, v_inst_3064_);
lean_closure_set(v___f_3074_, 4, v___f_3073_);
v___f_3075_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3075_, 0, v_toBind_3062_);
lean_closure_set(v___f_3075_, 1, v_getInfoState_3065_);
lean_closure_set(v___f_3075_, 2, v___f_3074_);
v___x_3076_ = lean_apply_4(v_inst_3066_, lean_box(0), lean_box(0), v_x_3067_, v___f_3075_);
v___x_3077_ = lean_apply_4(v_map_3072_, lean_box(0), lean_box(0), v___f_3068_, v___x_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object* v_inst_3078_, lean_object* v_inst_3079_, lean_object* v_inst_3080_, lean_object* v_x_3081_, lean_object* v_ctx_x3f_3082_){
_start:
{
lean_object* v_toApplicative_3083_; lean_object* v_toBind_3084_; lean_object* v_getInfoState_3085_; lean_object* v_modifyInfoState_3086_; lean_object* v___f_3087_; lean_object* v___f_3088_; lean_object* v___f_3089_; lean_object* v___x_3090_; 
v_toApplicative_3083_ = lean_ctor_get(v_inst_3078_, 0);
v_toBind_3084_ = lean_ctor_get(v_inst_3078_, 1);
lean_inc_n(v_toBind_3084_, 3);
v_getInfoState_3085_ = lean_ctor_get(v_inst_3079_, 0);
lean_inc_n(v_getInfoState_3085_, 2);
v_modifyInfoState_3086_ = lean_ctor_get(v_inst_3079_, 1);
v___f_3087_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3081_);
lean_inc_ref(v_inst_3078_);
lean_inc(v_modifyInfoState_3086_);
lean_inc_ref(v_toApplicative_3083_);
v___f_3088_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6), 10, 9);
lean_closure_set(v___f_3088_, 0, v_toApplicative_3083_);
lean_closure_set(v___f_3088_, 1, v_modifyInfoState_3086_);
lean_closure_set(v___f_3088_, 2, v_toBind_3084_);
lean_closure_set(v___f_3088_, 3, v_ctx_x3f_3082_);
lean_closure_set(v___f_3088_, 4, v_inst_3078_);
lean_closure_set(v___f_3088_, 5, v_getInfoState_3085_);
lean_closure_set(v___f_3088_, 6, v_inst_3080_);
lean_closure_set(v___f_3088_, 7, v_x_3081_);
lean_closure_set(v___f_3088_, 8, v___f_3087_);
v___f_3089_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3089_, 0, v_x_3081_);
lean_closure_set(v___f_3089_, 1, v_inst_3078_);
lean_closure_set(v___f_3089_, 2, v_inst_3079_);
lean_closure_set(v___f_3089_, 3, v_toBind_3084_);
lean_closure_set(v___f_3089_, 4, v___f_3088_);
v___x_3090_ = lean_apply_4(v_toBind_3084_, lean_box(0), lean_box(0), v_getInfoState_3085_, v___f_3089_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object* v_m_3091_, lean_object* v_inst_3092_, lean_object* v_inst_3093_, lean_object* v_00_u03b1_3094_, lean_object* v_inst_3095_, lean_object* v_x_3096_, lean_object* v_ctx_x3f_3097_){
_start:
{
lean_object* v___x_3098_; 
v___x_3098_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3092_, v_inst_3093_, v_inst_3095_, v_x_3096_, v_ctx_x3f_3097_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object* v_toPure_3099_, lean_object* v_____do__lift_3100_){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3101_, 0, v_____do__lift_3100_);
v___x_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3101_);
v___x_3103_ = lean_apply_2(v_toPure_3099_, lean_box(0), v___x_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object* v_inst_3104_, lean_object* v_inst_3105_, lean_object* v_inst_3106_, lean_object* v_inst_3107_, lean_object* v_inst_3108_, lean_object* v_inst_3109_, lean_object* v_inst_3110_, lean_object* v_inst_3111_, lean_object* v_inst_3112_, lean_object* v_x_3113_){
_start:
{
lean_object* v_toApplicative_3114_; lean_object* v_toBind_3115_; lean_object* v_toPure_3116_; lean_object* v___x_3117_; lean_object* v___f_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v_toApplicative_3114_ = lean_ctor_get(v_inst_3104_, 0);
v_toBind_3115_ = lean_ctor_get(v_inst_3104_, 1);
v_toPure_3116_ = lean_ctor_get(v_toApplicative_3114_, 1);
lean_inc_ref(v_inst_3104_);
v___x_3117_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_3104_, v_inst_3108_, v_inst_3110_, v_inst_3109_, v_inst_3111_, v_inst_3106_, v_inst_3112_);
lean_inc(v_toPure_3116_);
v___f_3118_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3118_, 0, v_toPure_3116_);
lean_inc(v_toBind_3115_);
v___x_3119_ = lean_apply_4(v_toBind_3115_, lean_box(0), lean_box(0), v___x_3117_, v___f_3118_);
v___x_3120_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3104_, v_inst_3105_, v_inst_3107_, v_x_3113_, v___x_3119_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object* v_m_3121_, lean_object* v_inst_3122_, lean_object* v_inst_3123_, lean_object* v_00_u03b1_3124_, lean_object* v_inst_3125_, lean_object* v_inst_3126_, lean_object* v_inst_3127_, lean_object* v_inst_3128_, lean_object* v_inst_3129_, lean_object* v_inst_3130_, lean_object* v_inst_3131_, lean_object* v_x_3132_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = l_Lean_Elab_withSaveInfoContext___redArg(v_inst_3122_, v_inst_3123_, v_inst_3125_, v_inst_3126_, v_inst_3127_, v_inst_3128_, v_inst_3129_, v_inst_3130_, v_inst_3131_, v_x_3132_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object* v_toPure_3134_, lean_object* v_____x_3135_){
_start:
{
if (lean_obj_tag(v_____x_3135_) == 1)
{
lean_object* v_val_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3145_; 
v_val_3136_ = lean_ctor_get(v_____x_3135_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_____x_3135_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3138_ = v_____x_3135_;
v_isShared_3139_ = v_isSharedCheck_3145_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_val_3136_);
lean_dec(v_____x_3135_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3145_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; lean_object* v___x_3142_; 
v___x_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3140_, 0, v_val_3136_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3140_);
v___x_3142_ = v___x_3138_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3140_);
v___x_3142_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
lean_object* v___x_3143_; 
v___x_3143_ = lean_apply_2(v_toPure_3134_, lean_box(0), v___x_3142_);
return v___x_3143_;
}
}
}
else
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
lean_dec(v_____x_3135_);
v___x_3146_ = lean_box(0);
v___x_3147_ = lean_apply_2(v_toPure_3134_, lean_box(0), v___x_3146_);
return v___x_3147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object* v_inst_3148_, lean_object* v_inst_3149_, lean_object* v_inst_3150_, lean_object* v_inst_3151_, lean_object* v_x_3152_){
_start:
{
lean_object* v_toApplicative_3153_; lean_object* v_toBind_3154_; lean_object* v_toPure_3155_; lean_object* v___f_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v_toApplicative_3153_ = lean_ctor_get(v_inst_3148_, 0);
v_toBind_3154_ = lean_ctor_get(v_inst_3148_, 1);
v_toPure_3155_ = lean_ctor_get(v_toApplicative_3153_, 1);
lean_inc(v_toPure_3155_);
v___f_3156_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3156_, 0, v_toPure_3155_);
lean_inc(v_toBind_3154_);
v___x_3157_ = lean_apply_4(v_toBind_3154_, lean_box(0), lean_box(0), v_inst_3151_, v___f_3156_);
v___x_3158_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3148_, v_inst_3149_, v_inst_3150_, v_x_3152_, v___x_3157_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object* v_m_3159_, lean_object* v_inst_3160_, lean_object* v_inst_3161_, lean_object* v_00_u03b1_3162_, lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_x_3165_){
_start:
{
lean_object* v___x_3166_; 
v___x_3166_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(v_inst_3160_, v_inst_3161_, v_inst_3163_, v_inst_3164_, v_x_3165_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object* v_toPure_3167_, lean_object* v_autoImplicits_3168_){
_start:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3169_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3169_, 0, v_autoImplicits_3168_);
v___x_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
v___x_3171_ = lean_apply_2(v_toPure_3167_, lean_box(0), v___x_3170_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object* v_inst_3172_, lean_object* v_inst_3173_, lean_object* v_inst_3174_, lean_object* v_inst_3175_, lean_object* v_x_3176_){
_start:
{
lean_object* v_toApplicative_3177_; lean_object* v_toBind_3178_; lean_object* v_toPure_3179_; lean_object* v___f_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v_toApplicative_3177_ = lean_ctor_get(v_inst_3172_, 0);
v_toBind_3178_ = lean_ctor_get(v_inst_3172_, 1);
v_toPure_3179_ = lean_ctor_get(v_toApplicative_3177_, 1);
lean_inc(v_toPure_3179_);
v___f_3180_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3180_, 0, v_toPure_3179_);
lean_inc(v_toBind_3178_);
v___x_3181_ = lean_apply_4(v_toBind_3178_, lean_box(0), lean_box(0), v_inst_3175_, v___f_3180_);
v___x_3182_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3172_, v_inst_3173_, v_inst_3174_, v_x_3176_, v___x_3181_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object* v_m_3183_, lean_object* v_inst_3184_, lean_object* v_inst_3185_, lean_object* v_00_u03b1_3186_, lean_object* v_inst_3187_, lean_object* v_inst_3188_, lean_object* v_x_3189_){
_start:
{
lean_object* v___x_3190_; 
v___x_3190_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(v_inst_3184_, v_inst_3185_, v_inst_3187_, v_inst_3188_, v_x_3189_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object* v___x_3191_, lean_object* v___x_3192_, lean_object* v_mvarId_3193_, lean_object* v_toPure_3194_, lean_object* v_____do__lift_3195_){
_start:
{
lean_object* v_assignment_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v_assignment_3196_ = lean_ctor_get(v_____do__lift_3195_, 0);
v___x_3197_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_3191_, v___x_3192_, v_assignment_3196_, v_mvarId_3193_);
v___x_3198_ = lean_apply_2(v_toPure_3194_, lean_box(0), v___x_3197_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object* v___x_3199_, lean_object* v___x_3200_, lean_object* v_mvarId_3201_, lean_object* v_toPure_3202_, lean_object* v_____do__lift_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(v___x_3199_, v___x_3200_, v_mvarId_3201_, v_toPure_3202_, v_____do__lift_3203_);
lean_dec_ref(v_____do__lift_3203_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object* v_inst_3207_, lean_object* v_inst_3208_, lean_object* v_mvarId_3209_){
_start:
{
lean_object* v_toApplicative_3210_; lean_object* v_toBind_3211_; lean_object* v_getInfoState_3212_; lean_object* v_toPure_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___f_3216_; lean_object* v___x_3217_; 
v_toApplicative_3210_ = lean_ctor_get(v_inst_3207_, 0);
lean_inc_ref(v_toApplicative_3210_);
v_toBind_3211_ = lean_ctor_get(v_inst_3207_, 1);
lean_inc(v_toBind_3211_);
lean_dec_ref(v_inst_3207_);
v_getInfoState_3212_ = lean_ctor_get(v_inst_3208_, 0);
lean_inc(v_getInfoState_3212_);
lean_dec_ref(v_inst_3208_);
v_toPure_3213_ = lean_ctor_get(v_toApplicative_3210_, 1);
lean_inc(v_toPure_3213_);
lean_dec_ref(v_toApplicative_3210_);
v___x_3214_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3215_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___f_3216_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3216_, 0, v___x_3214_);
lean_closure_set(v___f_3216_, 1, v___x_3215_);
lean_closure_set(v___f_3216_, 2, v_mvarId_3209_);
lean_closure_set(v___f_3216_, 3, v_toPure_3213_);
v___x_3217_ = lean_apply_4(v_toBind_3211_, lean_box(0), lean_box(0), v_getInfoState_3212_, v___f_3216_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* v_m_3218_, lean_object* v_inst_3219_, lean_object* v_inst_3220_, lean_object* v_mvarId_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3219_, v_inst_3220_, v_mvarId_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object* v_mvarId_3223_, lean_object* v_infoTree_3224_, lean_object* v_s_3225_){
_start:
{
uint8_t v_enabled_3226_; lean_object* v_assignment_3227_; lean_object* v_lazyAssignment_3228_; lean_object* v_trees_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3239_; 
v_enabled_3226_ = lean_ctor_get_uint8(v_s_3225_, sizeof(void*)*3);
v_assignment_3227_ = lean_ctor_get(v_s_3225_, 0);
v_lazyAssignment_3228_ = lean_ctor_get(v_s_3225_, 1);
v_trees_3229_ = lean_ctor_get(v_s_3225_, 2);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_s_3225_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3231_ = v_s_3225_;
v_isShared_3232_ = v_isSharedCheck_3239_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_trees_3229_);
lean_inc(v_lazyAssignment_3228_);
lean_inc(v_assignment_3227_);
lean_dec(v_s_3225_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3239_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3237_; 
v___x_3233_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3234_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3235_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3233_, v___x_3234_, v_assignment_3227_, v_mvarId_3223_, v_infoTree_3224_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 0, v___x_3235_);
v___x_3237_ = v___x_3231_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v_lazyAssignment_3228_);
lean_ctor_set(v_reuseFailAlloc_3238_, 2, v_trees_3229_);
lean_ctor_set_uint8(v_reuseFailAlloc_3238_, sizeof(void*)*3, v_enabled_3226_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3243_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2));
v___x_3244_ = lean_unsigned_to_nat(2u);
v___x_3245_ = lean_unsigned_to_nat(380u);
v___x_3246_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1));
v___x_3247_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0));
v___x_3248_ = l_mkPanicMessageWithDecl(v___x_3247_, v___x_3246_, v___x_3245_, v___x_3244_, v___x_3243_);
return v___x_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object* v_inst_3249_, lean_object* v___f_3250_, lean_object* v_inst_3251_, lean_object* v_____do__lift_3252_){
_start:
{
if (lean_obj_tag(v_____do__lift_3252_) == 0)
{
lean_object* v_modifyInfoState_3253_; lean_object* v___x_3254_; 
lean_dec_ref(v_inst_3251_);
v_modifyInfoState_3253_ = lean_ctor_get(v_inst_3249_, 1);
lean_inc(v_modifyInfoState_3253_);
lean_dec_ref(v_inst_3249_);
v___x_3254_ = lean_apply_1(v_modifyInfoState_3253_, v___f_3250_);
return v___x_3254_;
}
else
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
lean_dec_ref(v___f_3250_);
lean_dec_ref(v_inst_3249_);
v___x_3255_ = lean_box(0);
v___x_3256_ = l_instInhabitedOfMonad___redArg(v_inst_3251_, v___x_3255_);
v___x_3257_ = lean_obj_once(&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3, &l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3_once, _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3);
v___x_3258_ = l_panic___redArg(v___x_3256_, v___x_3257_);
lean_dec(v___x_3256_);
return v___x_3258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object* v_inst_3259_, lean_object* v___f_3260_, lean_object* v_inst_3261_, lean_object* v_____do__lift_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(v_inst_3259_, v___f_3260_, v_inst_3261_, v_____do__lift_3262_);
lean_dec(v_____do__lift_3262_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object* v_inst_3264_, lean_object* v_inst_3265_, lean_object* v_mvarId_3266_, lean_object* v_infoTree_3267_){
_start:
{
lean_object* v_toBind_3268_; lean_object* v___f_3269_; lean_object* v___f_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v_toBind_3268_ = lean_ctor_get(v_inst_3264_, 1);
lean_inc(v_toBind_3268_);
lean_inc(v_mvarId_3266_);
v___f_3269_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3269_, 0, v_mvarId_3266_);
lean_closure_set(v___f_3269_, 1, v_infoTree_3267_);
lean_inc_ref(v_inst_3264_);
lean_inc_ref(v_inst_3265_);
v___f_3270_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3270_, 0, v_inst_3265_);
lean_closure_set(v___f_3270_, 1, v___f_3269_);
lean_closure_set(v___f_3270_, 2, v_inst_3264_);
v___x_3271_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3264_, v_inst_3265_, v_mvarId_3266_);
v___x_3272_ = lean_apply_4(v_toBind_3268_, lean_box(0), lean_box(0), v___x_3271_, v___f_3270_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* v_m_3273_, lean_object* v_inst_3274_, lean_object* v_inst_3275_, lean_object* v_mvarId_3276_, lean_object* v_infoTree_3277_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l_Lean_Elab_assignInfoHoleId___redArg(v_inst_3274_, v_inst_3275_, v_mvarId_3276_, v_infoTree_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object* v_stx_3279_, lean_object* v_output_3280_, lean_object* v_toPure_3281_, lean_object* v_____do__lift_3282_){
_start:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3283_, 0, v_____do__lift_3282_);
lean_ctor_set(v___x_3283_, 1, v_stx_3279_);
lean_ctor_set(v___x_3283_, 2, v_output_3280_);
v___x_3284_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3283_);
v___x_3285_ = lean_apply_2(v_toPure_3281_, lean_box(0), v___x_3284_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object* v_inst_3286_, lean_object* v_inst_3287_, lean_object* v_inst_3288_, lean_object* v_inst_3289_, lean_object* v_stx_3290_, lean_object* v_output_3291_, lean_object* v_x_3292_){
_start:
{
lean_object* v_toApplicative_3293_; lean_object* v_toBind_3294_; lean_object* v_toPure_3295_; lean_object* v___f_3296_; lean_object* v_mkInfo_3297_; lean_object* v___f_3298_; lean_object* v___x_3299_; 
v_toApplicative_3293_ = lean_ctor_get(v_inst_3287_, 0);
v_toBind_3294_ = lean_ctor_get(v_inst_3287_, 1);
v_toPure_3295_ = lean_ctor_get(v_toApplicative_3293_, 1);
lean_inc_n(v_toPure_3295_, 2);
v___f_3296_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3296_, 0, v_stx_3290_);
lean_closure_set(v___f_3296_, 1, v_output_3291_);
lean_closure_set(v___f_3296_, 2, v_toPure_3295_);
lean_inc_n(v_toBind_3294_, 2);
v_mkInfo_3297_ = lean_apply_4(v_toBind_3294_, lean_box(0), lean_box(0), v_inst_3289_, v___f_3296_);
v___f_3298_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3298_, 0, v_toPure_3295_);
lean_closure_set(v___f_3298_, 1, v_toBind_3294_);
lean_closure_set(v___f_3298_, 2, v_mkInfo_3297_);
v___x_3299_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3287_, v_inst_3288_, v_inst_3286_, v_x_3292_, v___f_3298_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* v_m_3300_, lean_object* v_00_u03b1_3301_, lean_object* v_inst_3302_, lean_object* v_inst_3303_, lean_object* v_inst_3304_, lean_object* v_inst_3305_, lean_object* v_stx_3306_, lean_object* v_output_3307_, lean_object* v_x_3308_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Lean_Elab_withMacroExpansionInfo___redArg(v_inst_3302_, v_inst_3303_, v_inst_3304_, v_inst_3305_, v_stx_3306_, v_output_3307_, v_x_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object* v_treesSaved_3310_, lean_object* v_mvarId_3311_, lean_object* v_s_3312_){
_start:
{
lean_object* v_trees_3313_; uint8_t v_enabled_3314_; lean_object* v_assignment_3315_; lean_object* v_lazyAssignment_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3336_; 
v_trees_3313_ = lean_ctor_get(v_s_3312_, 2);
v_enabled_3314_ = lean_ctor_get_uint8(v_s_3312_, sizeof(void*)*3);
v_assignment_3315_ = lean_ctor_get(v_s_3312_, 0);
v_lazyAssignment_3316_ = lean_ctor_get(v_s_3312_, 1);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_s_3312_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3318_ = v_s_3312_;
v_isShared_3319_ = v_isSharedCheck_3336_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_trees_3313_);
lean_inc(v_lazyAssignment_3316_);
lean_inc(v_assignment_3315_);
lean_dec(v_s_3312_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3336_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v_size_3320_; lean_object* v___x_3321_; uint8_t v___x_3322_; 
v_size_3320_ = lean_ctor_get(v_trees_3313_, 2);
v___x_3321_ = lean_unsigned_to_nat(0u);
v___x_3322_ = lean_nat_dec_lt(v___x_3321_, v_size_3320_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3324_; 
lean_dec_ref(v_trees_3313_);
lean_dec(v_mvarId_3311_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 2, v_treesSaved_3310_);
v___x_3324_ = v___x_3318_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_assignment_3315_);
lean_ctor_set(v_reuseFailAlloc_3325_, 1, v_lazyAssignment_3316_);
lean_ctor_set(v_reuseFailAlloc_3325_, 2, v_treesSaved_3310_);
lean_ctor_set_uint8(v_reuseFailAlloc_3325_, sizeof(void*)*3, v_enabled_3314_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
else
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3334_; 
v___x_3326_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3327_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3328_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_3329_ = lean_unsigned_to_nat(1u);
v___x_3330_ = lean_nat_sub(v_size_3320_, v___x_3329_);
v___x_3331_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3328_, v_trees_3313_, v___x_3330_);
lean_dec(v___x_3330_);
lean_dec_ref(v_trees_3313_);
v___x_3332_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3326_, v___x_3327_, v_assignment_3315_, v_mvarId_3311_, v___x_3331_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 2, v_treesSaved_3310_);
lean_ctor_set(v___x_3318_, 0, v___x_3332_);
v___x_3334_ = v___x_3318_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3332_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_lazyAssignment_3316_);
lean_ctor_set(v_reuseFailAlloc_3335_, 2, v_treesSaved_3310_);
lean_ctor_set_uint8(v_reuseFailAlloc_3335_, sizeof(void*)*3, v_enabled_3314_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object* v_modifyInfoState_3337_, lean_object* v___f_3338_, lean_object* v_x_3339_){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = lean_apply_1(v_modifyInfoState_3337_, v___f_3338_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object* v_modifyInfoState_3341_, lean_object* v___f_3342_, lean_object* v_x_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_3341_, v___f_3342_, v_x_3343_);
lean_dec(v_x_3343_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object* v_toApplicative_3345_, lean_object* v_mvarId_3346_, lean_object* v_modifyInfoState_3347_, lean_object* v_inst_3348_, lean_object* v_x_3349_, lean_object* v___f_3350_, lean_object* v_treesSaved_3351_){
_start:
{
lean_object* v_toFunctor_3352_; lean_object* v_map_3353_; lean_object* v___f_3354_; lean_object* v___f_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v_toFunctor_3352_ = lean_ctor_get(v_toApplicative_3345_, 0);
lean_inc_ref(v_toFunctor_3352_);
lean_dec_ref(v_toApplicative_3345_);
v_map_3353_ = lean_ctor_get(v_toFunctor_3352_, 0);
lean_inc(v_map_3353_);
lean_dec_ref(v_toFunctor_3352_);
v___f_3354_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3354_, 0, v_treesSaved_3351_);
lean_closure_set(v___f_3354_, 1, v_mvarId_3346_);
v___f_3355_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3355_, 0, v_modifyInfoState_3347_);
lean_closure_set(v___f_3355_, 1, v___f_3354_);
v___x_3356_ = lean_apply_4(v_inst_3348_, lean_box(0), lean_box(0), v_x_3349_, v___f_3355_);
v___x_3357_ = lean_apply_4(v_map_3353_, lean_box(0), lean_box(0), v___f_3350_, v___x_3356_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object* v_inst_3358_, lean_object* v_inst_3359_, lean_object* v_inst_3360_, lean_object* v_mvarId_3361_, lean_object* v_x_3362_){
_start:
{
lean_object* v_toApplicative_3363_; lean_object* v_toBind_3364_; lean_object* v_getInfoState_3365_; lean_object* v_modifyInfoState_3366_; lean_object* v___f_3367_; lean_object* v___f_3368_; lean_object* v___f_3369_; lean_object* v___x_3370_; 
v_toApplicative_3363_ = lean_ctor_get(v_inst_3359_, 0);
v_toBind_3364_ = lean_ctor_get(v_inst_3359_, 1);
lean_inc_n(v_toBind_3364_, 2);
v_getInfoState_3365_ = lean_ctor_get(v_inst_3360_, 0);
lean_inc(v_getInfoState_3365_);
v_modifyInfoState_3366_ = lean_ctor_get(v_inst_3360_, 1);
v___f_3367_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3362_);
lean_inc(v_modifyInfoState_3366_);
lean_inc_ref(v_toApplicative_3363_);
v___f_3368_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 7, 6);
lean_closure_set(v___f_3368_, 0, v_toApplicative_3363_);
lean_closure_set(v___f_3368_, 1, v_mvarId_3361_);
lean_closure_set(v___f_3368_, 2, v_modifyInfoState_3366_);
lean_closure_set(v___f_3368_, 3, v_inst_3358_);
lean_closure_set(v___f_3368_, 4, v_x_3362_);
lean_closure_set(v___f_3368_, 5, v___f_3367_);
v___f_3369_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3369_, 0, v_x_3362_);
lean_closure_set(v___f_3369_, 1, v_inst_3359_);
lean_closure_set(v___f_3369_, 2, v_inst_3360_);
lean_closure_set(v___f_3369_, 3, v_toBind_3364_);
lean_closure_set(v___f_3369_, 4, v___f_3368_);
v___x_3370_ = lean_apply_4(v_toBind_3364_, lean_box(0), lean_box(0), v_getInfoState_3365_, v___f_3369_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object* v_m_3371_, lean_object* v_00_u03b1_3372_, lean_object* v_inst_3373_, lean_object* v_inst_3374_, lean_object* v_inst_3375_, lean_object* v_mvarId_3376_, lean_object* v_x_3377_){
_start:
{
lean_object* v_toApplicative_3378_; lean_object* v_toBind_3379_; lean_object* v_getInfoState_3380_; lean_object* v_modifyInfoState_3381_; lean_object* v___f_3382_; lean_object* v___f_3383_; lean_object* v___f_3384_; lean_object* v___x_3385_; 
v_toApplicative_3378_ = lean_ctor_get(v_inst_3374_, 0);
v_toBind_3379_ = lean_ctor_get(v_inst_3374_, 1);
lean_inc_n(v_toBind_3379_, 2);
v_getInfoState_3380_ = lean_ctor_get(v_inst_3375_, 0);
lean_inc(v_getInfoState_3380_);
v_modifyInfoState_3381_ = lean_ctor_get(v_inst_3375_, 1);
v___f_3382_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3377_);
lean_inc(v_modifyInfoState_3381_);
lean_inc_ref(v_toApplicative_3378_);
v___f_3383_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 7, 6);
lean_closure_set(v___f_3383_, 0, v_toApplicative_3378_);
lean_closure_set(v___f_3383_, 1, v_mvarId_3376_);
lean_closure_set(v___f_3383_, 2, v_modifyInfoState_3381_);
lean_closure_set(v___f_3383_, 3, v_inst_3373_);
lean_closure_set(v___f_3383_, 4, v_x_3377_);
lean_closure_set(v___f_3383_, 5, v___f_3382_);
v___f_3384_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3384_, 0, v_x_3377_);
lean_closure_set(v___f_3384_, 1, v_inst_3374_);
lean_closure_set(v___f_3384_, 2, v_inst_3375_);
lean_closure_set(v___f_3384_, 3, v_toBind_3379_);
lean_closure_set(v___f_3384_, 4, v___f_3383_);
v___x_3385_ = lean_apply_4(v_toBind_3379_, lean_box(0), lean_box(0), v_getInfoState_3380_, v___f_3384_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t v_flag_3386_, lean_object* v_s_3387_){
_start:
{
lean_object* v_assignment_3388_; lean_object* v_lazyAssignment_3389_; lean_object* v_trees_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
v_assignment_3388_ = lean_ctor_get(v_s_3387_, 0);
v_lazyAssignment_3389_ = lean_ctor_get(v_s_3387_, 1);
v_trees_3390_ = lean_ctor_get(v_s_3387_, 2);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_s_3387_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v_s_3387_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_trees_3390_);
lean_inc(v_lazyAssignment_3389_);
lean_inc(v_assignment_3388_);
lean_dec(v_s_3387_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_assignment_3388_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v_lazyAssignment_3389_);
lean_ctor_set(v_reuseFailAlloc_3396_, 2, v_trees_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
lean_ctor_set_uint8(v___x_3395_, sizeof(void*)*3, v_flag_3386_);
return v___x_3395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object* v_flag_3398_, lean_object* v_s_3399_){
_start:
{
uint8_t v_flag_boxed_3400_; lean_object* v_res_3401_; 
v_flag_boxed_3400_ = lean_unbox(v_flag_3398_);
v_res_3401_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_3400_, v_s_3399_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object* v_inst_3402_, uint8_t v_flag_3403_){
_start:
{
lean_object* v_modifyInfoState_3404_; lean_object* v___x_3405_; lean_object* v___f_3406_; lean_object* v___x_3407_; 
v_modifyInfoState_3404_ = lean_ctor_get(v_inst_3402_, 1);
lean_inc(v_modifyInfoState_3404_);
lean_dec_ref(v_inst_3402_);
v___x_3405_ = lean_box(v_flag_3403_);
v___f_3406_ = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3406_, 0, v___x_3405_);
v___x_3407_ = lean_apply_1(v_modifyInfoState_3404_, v___f_3406_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object* v_inst_3408_, lean_object* v_flag_3409_){
_start:
{
uint8_t v_flag_boxed_3410_; lean_object* v_res_3411_; 
v_flag_boxed_3410_ = lean_unbox(v_flag_3409_);
v_res_3411_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3408_, v_flag_boxed_3410_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object* v_m_3412_, lean_object* v_inst_3413_, uint8_t v_flag_3414_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3413_, v_flag_3414_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object* v_m_3416_, lean_object* v_inst_3417_, lean_object* v_flag_3418_){
_start:
{
uint8_t v_flag_boxed_3419_; lean_object* v_res_3420_; 
v_flag_boxed_3419_ = lean_unbox(v_flag_3418_);
v_res_3420_ = l_Lean_Elab_enableInfoTree(v_m_3416_, v_inst_3417_, v_flag_boxed_3419_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object* v_x_3421_){
_start:
{
lean_object* v_fst_3422_; 
v_fst_3422_ = lean_ctor_get(v_x_3421_, 0);
lean_inc(v_fst_3422_);
return v_fst_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object* v_x_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_3423_);
lean_dec_ref(v_x_3423_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object* v_x_3425_, lean_object* v_____r_3426_){
_start:
{
lean_inc(v_x_3425_);
return v_x_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object* v_x_3427_, lean_object* v_____r_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_3427_, v_____r_3428_);
lean_dec(v_x_3427_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object* v___x_3430_, lean_object* v_x_3431_){
_start:
{
lean_inc(v___x_3430_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object* v___x_3432_, lean_object* v_x_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_3432_, v_x_3433_);
lean_dec(v_x_3433_);
lean_dec(v___x_3432_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object* v_toFunctor_3435_, lean_object* v_inst_3436_, uint8_t v_flag_3437_, lean_object* v_toBind_3438_, lean_object* v___f_3439_, lean_object* v_inst_3440_, lean_object* v___f_3441_, lean_object* v_____do__lift_3442_){
_start:
{
uint8_t v_enabled_3443_; lean_object* v_map_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___f_3448_; lean_object* v_y_3449_; lean_object* v___x_3450_; 
v_enabled_3443_ = lean_ctor_get_uint8(v_____do__lift_3442_, sizeof(void*)*3);
v_map_3444_ = lean_ctor_get(v_toFunctor_3435_, 0);
lean_inc(v_map_3444_);
lean_dec_ref(v_toFunctor_3435_);
lean_inc_ref(v_inst_3436_);
v___x_3445_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3436_, v_flag_3437_);
v___x_3446_ = lean_apply_4(v_toBind_3438_, lean_box(0), lean_box(0), v___x_3445_, v___f_3439_);
v___x_3447_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3436_, v_enabled_3443_);
v___f_3448_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_3448_, 0, v___x_3447_);
v_y_3449_ = lean_apply_4(v_inst_3440_, lean_box(0), lean_box(0), v___x_3446_, v___f_3448_);
v___x_3450_ = lean_apply_4(v_map_3444_, lean_box(0), lean_box(0), v___f_3441_, v_y_3449_);
return v___x_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object* v_toFunctor_3451_, lean_object* v_inst_3452_, lean_object* v_flag_3453_, lean_object* v_toBind_3454_, lean_object* v___f_3455_, lean_object* v_inst_3456_, lean_object* v___f_3457_, lean_object* v_____do__lift_3458_){
_start:
{
uint8_t v_flag_boxed_3459_; lean_object* v_res_3460_; 
v_flag_boxed_3459_ = lean_unbox(v_flag_3453_);
v_res_3460_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_3451_, v_inst_3452_, v_flag_boxed_3459_, v_toBind_3454_, v___f_3455_, v_inst_3456_, v___f_3457_, v_____do__lift_3458_);
lean_dec_ref(v_____do__lift_3458_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object* v_inst_3462_, lean_object* v_inst_3463_, lean_object* v_inst_3464_, uint8_t v_flag_3465_, lean_object* v_x_3466_){
_start:
{
lean_object* v_toApplicative_3467_; lean_object* v_toBind_3468_; lean_object* v_getInfoState_3469_; lean_object* v_toFunctor_3470_; lean_object* v___f_3471_; lean_object* v___f_3472_; lean_object* v___x_3473_; lean_object* v___f_3474_; lean_object* v___x_3475_; 
v_toApplicative_3467_ = lean_ctor_get(v_inst_3462_, 0);
lean_inc_ref(v_toApplicative_3467_);
v_toBind_3468_ = lean_ctor_get(v_inst_3462_, 1);
lean_inc_n(v_toBind_3468_, 2);
lean_dec_ref(v_inst_3462_);
v_getInfoState_3469_ = lean_ctor_get(v_inst_3463_, 0);
lean_inc(v_getInfoState_3469_);
v_toFunctor_3470_ = lean_ctor_get(v_toApplicative_3467_, 0);
lean_inc_ref(v_toFunctor_3470_);
lean_dec_ref(v_toApplicative_3467_);
v___f_3471_ = ((lean_object*)(l_Lean_Elab_withEnableInfoTree___redArg___closed__0));
v___f_3472_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3472_, 0, v_x_3466_);
v___x_3473_ = lean_box(v_flag_3465_);
v___f_3474_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_3474_, 0, v_toFunctor_3470_);
lean_closure_set(v___f_3474_, 1, v_inst_3463_);
lean_closure_set(v___f_3474_, 2, v___x_3473_);
lean_closure_set(v___f_3474_, 3, v_toBind_3468_);
lean_closure_set(v___f_3474_, 4, v___f_3472_);
lean_closure_set(v___f_3474_, 5, v_inst_3464_);
lean_closure_set(v___f_3474_, 6, v___f_3471_);
v___x_3475_ = lean_apply_4(v_toBind_3468_, lean_box(0), lean_box(0), v_getInfoState_3469_, v___f_3474_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object* v_inst_3476_, lean_object* v_inst_3477_, lean_object* v_inst_3478_, lean_object* v_flag_3479_, lean_object* v_x_3480_){
_start:
{
uint8_t v_flag_boxed_3481_; lean_object* v_res_3482_; 
v_flag_boxed_3481_ = lean_unbox(v_flag_3479_);
v_res_3482_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3476_, v_inst_3477_, v_inst_3478_, v_flag_boxed_3481_, v_x_3480_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object* v_m_3483_, lean_object* v_00_u03b1_3484_, lean_object* v_inst_3485_, lean_object* v_inst_3486_, lean_object* v_inst_3487_, uint8_t v_flag_3488_, lean_object* v_x_3489_){
_start:
{
lean_object* v___x_3490_; 
v___x_3490_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3485_, v_inst_3486_, v_inst_3487_, v_flag_3488_, v_x_3489_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object* v_m_3491_, lean_object* v_00_u03b1_3492_, lean_object* v_inst_3493_, lean_object* v_inst_3494_, lean_object* v_inst_3495_, lean_object* v_flag_3496_, lean_object* v_x_3497_){
_start:
{
uint8_t v_flag_boxed_3498_; lean_object* v_res_3499_; 
v_flag_boxed_3498_ = lean_unbox(v_flag_3496_);
v_res_3499_ = l_Lean_Elab_withEnableInfoTree(v_m_3491_, v_00_u03b1_3492_, v_inst_3493_, v_inst_3494_, v_inst_3495_, v_flag_boxed_3498_, v_x_3497_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object* v_toPure_3500_, lean_object* v_____do__lift_3501_){
_start:
{
lean_object* v_trees_3502_; lean_object* v___x_3503_; 
v_trees_3502_ = lean_ctor_get(v_____do__lift_3501_, 2);
lean_inc_ref(v_trees_3502_);
lean_dec_ref(v_____do__lift_3501_);
v___x_3503_ = lean_apply_2(v_toPure_3500_, lean_box(0), v_trees_3502_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object* v_inst_3504_, lean_object* v_inst_3505_){
_start:
{
lean_object* v_toApplicative_3506_; lean_object* v_toBind_3507_; lean_object* v_getInfoState_3508_; lean_object* v_toPure_3509_; lean_object* v___f_3510_; lean_object* v___x_3511_; 
v_toApplicative_3506_ = lean_ctor_get(v_inst_3505_, 0);
lean_inc_ref(v_toApplicative_3506_);
v_toBind_3507_ = lean_ctor_get(v_inst_3505_, 1);
lean_inc(v_toBind_3507_);
lean_dec_ref(v_inst_3505_);
v_getInfoState_3508_ = lean_ctor_get(v_inst_3504_, 0);
lean_inc(v_getInfoState_3508_);
lean_dec_ref(v_inst_3504_);
v_toPure_3509_ = lean_ctor_get(v_toApplicative_3506_, 1);
lean_inc(v_toPure_3509_);
lean_dec_ref(v_toApplicative_3506_);
v___f_3510_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3510_, 0, v_toPure_3509_);
v___x_3511_ = lean_apply_4(v_toBind_3507_, lean_box(0), lean_box(0), v_getInfoState_3508_, v___f_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object* v_m_3512_, lean_object* v_inst_3513_, lean_object* v_inst_3514_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_3513_, v_inst_3514_);
return v___x_3515_;
}
}
lean_object* runtime_initialize_Lean_Elab_InfoTree_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_PPGoal(uint8_t builtin);
lean_object* runtime_initialize_Lean_ReservedNameAction(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
