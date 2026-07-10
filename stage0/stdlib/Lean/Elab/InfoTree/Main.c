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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_a_229_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_toCommandContextInfo_236_; lean_object* v_env_237_; lean_object* v_options_238_; lean_object* v_currNamespace_239_; lean_object* v_openDecls_240_; lean_object* v_ngen_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; lean_object* v_env_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_315_; uint8_t v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; uint8_t v___y_319_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v_env_351_; lean_object* v___x_352_; uint8_t v___x_353_; lean_object* v___y_355_; lean_object* v___y_356_; uint8_t v___y_386_; uint8_t v___x_407_; 
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
v___x_340_ = l_Lean_inheritedTraceOptions;
v___x_341_ = lean_st_ref_get(v___x_340_);
v___x_342_ = lean_st_ref_get(v___x_253_);
v___x_343_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14));
v___x_344_ = l_Lean_instInhabitedFileMap_default;
v___x_345_ = l_Lean_Options_empty;
v___x_346_ = lean_unsigned_to_nat(1000u);
v___x_347_ = lean_box(0);
v___x_348_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15);
v___x_349_ = lean_box(0);
v___x_350_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_350_, 0, v___x_343_);
lean_ctor_set(v___x_350_, 1, v___x_344_);
lean_ctor_set(v___x_350_, 2, v___x_345_);
lean_ctor_set(v___x_350_, 3, v___x_232_);
lean_ctor_set(v___x_350_, 4, v___x_346_);
lean_ctor_set(v___x_350_, 5, v___x_347_);
lean_ctor_set(v___x_350_, 6, v_currNamespace_239_);
lean_ctor_set(v___x_350_, 7, v_openDecls_240_);
lean_ctor_set(v___x_350_, 8, v___x_235_);
lean_ctor_set(v___x_350_, 9, v___x_348_);
lean_ctor_set(v___x_350_, 10, v___x_246_);
lean_ctor_set(v___x_350_, 11, v___x_242_);
lean_ctor_set(v___x_350_, 12, v___x_349_);
lean_ctor_set(v___x_350_, 13, v___x_341_);
lean_ctor_set_uint8(v___x_350_, sizeof(void*)*14, v___x_244_);
lean_ctor_set_uint8(v___x_350_, sizeof(void*)*14 + 1, v___x_244_);
v_env_351_ = lean_ctor_get(v___x_342_, 0);
lean_inc_ref(v_env_351_);
lean_dec(v___x_342_);
v___x_352_ = l_Lean_diagnostics;
v___x_353_ = lean_uint8_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16);
v___x_407_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_351_);
lean_dec_ref(v_env_351_);
if (v___x_407_ == 0)
{
if (v___x_353_ == 0)
{
v___y_386_ = v___x_249_;
goto v___jp_385_;
}
else
{
v___y_386_ = v___x_407_;
goto v___jp_385_;
}
}
else
{
v___y_386_ = v___x_353_;
goto v___jp_385_;
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
lean_object* v_fileName_259_; lean_object* v_fileMap_260_; lean_object* v_currRecDepth_261_; lean_object* v_ref_262_; lean_object* v_currNamespace_263_; lean_object* v_openDecls_264_; lean_object* v_initHeartbeats_265_; lean_object* v_maxHeartbeats_266_; lean_object* v_quotContext_267_; lean_object* v_currMacroScope_268_; lean_object* v_cancelTk_x3f_269_; uint8_t v_suppressElabErrors_270_; lean_object* v_inheritedTraceOptions_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_311_; 
v_fileName_259_ = lean_ctor_get(v___y_257_, 0);
v_fileMap_260_ = lean_ctor_get(v___y_257_, 1);
v_currRecDepth_261_ = lean_ctor_get(v___y_257_, 3);
v_ref_262_ = lean_ctor_get(v___y_257_, 5);
v_currNamespace_263_ = lean_ctor_get(v___y_257_, 6);
v_openDecls_264_ = lean_ctor_get(v___y_257_, 7);
v_initHeartbeats_265_ = lean_ctor_get(v___y_257_, 8);
v_maxHeartbeats_266_ = lean_ctor_get(v___y_257_, 9);
v_quotContext_267_ = lean_ctor_get(v___y_257_, 10);
v_currMacroScope_268_ = lean_ctor_get(v___y_257_, 11);
v_cancelTk_x3f_269_ = lean_ctor_get(v___y_257_, 12);
v_suppressElabErrors_270_ = lean_ctor_get_uint8(v___y_257_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_271_ = lean_ctor_get(v___y_257_, 13);
v_isSharedCheck_311_ = !lean_is_exclusive(v___y_257_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; lean_object* v_unused_313_; 
v_unused_312_ = lean_ctor_get(v___y_257_, 4);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v___y_257_, 2);
lean_dec(v_unused_313_);
v___x_273_ = v___y_257_;
v_isShared_274_ = v_isSharedCheck_311_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_inheritedTraceOptions_271_);
lean_inc(v_cancelTk_x3f_269_);
lean_inc(v_currMacroScope_268_);
lean_inc(v_quotContext_267_);
lean_inc(v_maxHeartbeats_266_);
lean_inc(v_initHeartbeats_265_);
lean_inc(v_openDecls_264_);
lean_inc(v_currNamespace_263_);
lean_inc(v_ref_262_);
lean_inc(v_currRecDepth_261_);
lean_inc(v_fileMap_260_);
lean_inc(v_fileName_259_);
lean_dec(v___y_257_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_311_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_275_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v_options_238_, v___y_256_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 4, v___x_275_);
lean_ctor_set(v___x_273_, 2, v_options_238_);
v___x_277_ = v___x_273_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_fileName_259_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_fileMap_260_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v_options_238_);
lean_ctor_set(v_reuseFailAlloc_310_, 3, v_currRecDepth_261_);
lean_ctor_set(v_reuseFailAlloc_310_, 4, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_310_, 5, v_ref_262_);
lean_ctor_set(v_reuseFailAlloc_310_, 6, v_currNamespace_263_);
lean_ctor_set(v_reuseFailAlloc_310_, 7, v_openDecls_264_);
lean_ctor_set(v_reuseFailAlloc_310_, 8, v_initHeartbeats_265_);
lean_ctor_set(v_reuseFailAlloc_310_, 9, v_maxHeartbeats_266_);
lean_ctor_set(v_reuseFailAlloc_310_, 10, v_quotContext_267_);
lean_ctor_set(v_reuseFailAlloc_310_, 11, v_currMacroScope_268_);
lean_ctor_set(v_reuseFailAlloc_310_, 12, v_cancelTk_x3f_269_);
lean_ctor_set(v_reuseFailAlloc_310_, 13, v_inheritedTraceOptions_271_);
lean_ctor_set_uint8(v_reuseFailAlloc_310_, sizeof(void*)*14 + 1, v_suppressElabErrors_270_);
v___x_277_ = v_reuseFailAlloc_310_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
lean_object* v___x_278_; 
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*14, v___y_255_);
v___x_278_ = lean_apply_3(v_x_226_, v___x_277_, v___y_258_, lean_box(0));
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_287_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_287_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_283_ = lean_st_ref_get(v___x_253_);
lean_dec(v___x_253_);
lean_dec(v___x_283_);
if (v_isShared_282_ == 0)
{
v___x_285_ = v___x_281_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_279_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_309_; 
lean_dec(v___x_253_);
v_a_288_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_309_ == 0)
{
v___x_290_ = v___x_278_;
v_isShared_291_ = v_isSharedCheck_309_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_278_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_309_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
if (lean_obj_tag(v_a_288_) == 0)
{
lean_object* v_msg_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v_msg_292_ = lean_ctor_get(v_a_288_, 1);
lean_inc_ref(v_msg_292_);
lean_dec_ref_known(v_a_288_, 2);
v___x_293_ = l_Lean_MessageData_toString(v_msg_292_);
v___x_294_ = lean_mk_io_user_error(v___x_293_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_294_);
v___x_296_ = v___x_290_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
else
{
lean_object* v_id_298_; lean_object* v___x_299_; 
lean_del_object(v___x_290_);
v_id_298_ = lean_ctor_get(v_a_288_, 0);
lean_inc(v_id_298_);
lean_dec_ref_known(v_a_288_, 2);
v___x_299_ = l_Lean_InternalExceptionId_getName(v_id_298_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v_id_298_);
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_300_);
lean_dec_ref_known(v___x_299_, 1);
v___x_301_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11));
v___x_302_ = l_Lean_Name_toString(v_a_300_, v___x_249_);
v___x_303_ = lean_string_append(v___x_301_, v___x_302_);
lean_dec_ref(v___x_302_);
v_a_229_ = v___x_303_;
goto v___jp_228_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec_ref_known(v___x_299_, 1);
v___x_304_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12));
v___x_305_ = l_Nat_reprFast(v_id_298_);
v___x_306_ = lean_string_append(v___x_304_, v___x_305_);
lean_dec_ref(v___x_305_);
v___x_307_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13));
v___x_308_ = lean_string_append(v___x_306_, v___x_307_);
v_a_229_ = v___x_308_;
goto v___jp_228_;
}
}
}
}
}
}
}
v___jp_314_:
{
uint8_t v___x_320_; 
v___x_320_ = lean_bool_not(v___y_319_);
if (v___x_320_ == 0)
{
v___y_255_ = v___y_316_;
v___y_256_ = v___y_317_;
v___y_257_ = v___y_315_;
v___y_258_ = v___y_318_;
goto v___jp_254_;
}
else
{
lean_object* v___x_321_; lean_object* v_env_322_; lean_object* v_nextMacroScope_323_; lean_object* v_ngen_324_; lean_object* v_auxDeclNGen_325_; lean_object* v_traceState_326_; lean_object* v_messages_327_; lean_object* v_infoState_328_; lean_object* v_snapshotTasks_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_338_; 
v___x_321_ = lean_st_ref_take(v___y_318_);
v_env_322_ = lean_ctor_get(v___x_321_, 0);
v_nextMacroScope_323_ = lean_ctor_get(v___x_321_, 1);
v_ngen_324_ = lean_ctor_get(v___x_321_, 2);
v_auxDeclNGen_325_ = lean_ctor_get(v___x_321_, 3);
v_traceState_326_ = lean_ctor_get(v___x_321_, 4);
v_messages_327_ = lean_ctor_get(v___x_321_, 6);
v_infoState_328_ = lean_ctor_get(v___x_321_, 7);
v_snapshotTasks_329_ = lean_ctor_get(v___x_321_, 8);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_338_ == 0)
{
lean_object* v_unused_339_; 
v_unused_339_ = lean_ctor_get(v___x_321_, 5);
lean_dec(v_unused_339_);
v___x_331_ = v___x_321_;
v_isShared_332_ = v_isSharedCheck_338_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_snapshotTasks_329_);
lean_inc(v_infoState_328_);
lean_inc(v_messages_327_);
lean_inc(v_traceState_326_);
lean_inc(v_auxDeclNGen_325_);
lean_inc(v_ngen_324_);
lean_inc(v_nextMacroScope_323_);
lean_inc(v_env_322_);
lean_dec(v___x_321_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_338_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = l_Lean_Kernel_enableDiag(v_env_322_, v___y_316_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 5, v___x_233_);
lean_ctor_set(v___x_331_, 0, v___x_333_);
v___x_335_ = v___x_331_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_nextMacroScope_323_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_ngen_324_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v_auxDeclNGen_325_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v_traceState_326_);
lean_ctor_set(v_reuseFailAlloc_337_, 5, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_337_, 6, v_messages_327_);
lean_ctor_set(v_reuseFailAlloc_337_, 7, v_infoState_328_);
lean_ctor_set(v_reuseFailAlloc_337_, 8, v_snapshotTasks_329_);
v___x_335_ = v_reuseFailAlloc_337_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_336_; 
v___x_336_ = lean_st_ref_set(v___y_318_, v___x_335_);
v___y_255_ = v___y_316_;
v___y_256_ = v___y_317_;
v___y_257_ = v___y_315_;
v___y_258_ = v___y_318_;
goto v___jp_254_;
}
}
}
}
v___jp_354_:
{
lean_object* v___x_357_; lean_object* v_fileName_358_; lean_object* v_fileMap_359_; lean_object* v_currRecDepth_360_; lean_object* v_ref_361_; lean_object* v_currNamespace_362_; lean_object* v_openDecls_363_; lean_object* v_initHeartbeats_364_; lean_object* v_maxHeartbeats_365_; lean_object* v_quotContext_366_; lean_object* v_currMacroScope_367_; lean_object* v_cancelTk_x3f_368_; uint8_t v_suppressElabErrors_369_; lean_object* v_inheritedTraceOptions_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_382_; 
v___x_357_ = lean_st_ref_get(v___y_356_);
v_fileName_358_ = lean_ctor_get(v___y_355_, 0);
v_fileMap_359_ = lean_ctor_get(v___y_355_, 1);
v_currRecDepth_360_ = lean_ctor_get(v___y_355_, 3);
v_ref_361_ = lean_ctor_get(v___y_355_, 5);
v_currNamespace_362_ = lean_ctor_get(v___y_355_, 6);
v_openDecls_363_ = lean_ctor_get(v___y_355_, 7);
v_initHeartbeats_364_ = lean_ctor_get(v___y_355_, 8);
v_maxHeartbeats_365_ = lean_ctor_get(v___y_355_, 9);
v_quotContext_366_ = lean_ctor_get(v___y_355_, 10);
v_currMacroScope_367_ = lean_ctor_get(v___y_355_, 11);
v_cancelTk_x3f_368_ = lean_ctor_get(v___y_355_, 12);
v_suppressElabErrors_369_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_370_ = lean_ctor_get(v___y_355_, 13);
v_isSharedCheck_382_ = !lean_is_exclusive(v___y_355_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; lean_object* v_unused_384_; 
v_unused_383_ = lean_ctor_get(v___y_355_, 4);
lean_dec(v_unused_383_);
v_unused_384_ = lean_ctor_get(v___y_355_, 2);
lean_dec(v_unused_384_);
v___x_372_ = v___y_355_;
v_isShared_373_ = v_isSharedCheck_382_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_inheritedTraceOptions_370_);
lean_inc(v_cancelTk_x3f_368_);
lean_inc(v_currMacroScope_367_);
lean_inc(v_quotContext_366_);
lean_inc(v_maxHeartbeats_365_);
lean_inc(v_initHeartbeats_364_);
lean_inc(v_openDecls_363_);
lean_inc(v_currNamespace_362_);
lean_inc(v_ref_361_);
lean_inc(v_currRecDepth_360_);
lean_inc(v_fileMap_359_);
lean_inc(v_fileName_358_);
lean_dec(v___y_355_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_382_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v_env_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
v_env_374_ = lean_ctor_get(v___x_357_, 0);
lean_inc_ref(v_env_374_);
lean_dec(v___x_357_);
v___x_375_ = l_Lean_maxRecDepth;
v___x_376_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v___x_376_);
lean_ctor_set(v___x_372_, 2, v___x_345_);
v___x_378_ = v___x_372_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_fileName_358_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_fileMap_359_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_381_, 3, v_currRecDepth_360_);
lean_ctor_set(v_reuseFailAlloc_381_, 4, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_381_, 5, v_ref_361_);
lean_ctor_set(v_reuseFailAlloc_381_, 6, v_currNamespace_362_);
lean_ctor_set(v_reuseFailAlloc_381_, 7, v_openDecls_363_);
lean_ctor_set(v_reuseFailAlloc_381_, 8, v_initHeartbeats_364_);
lean_ctor_set(v_reuseFailAlloc_381_, 9, v_maxHeartbeats_365_);
lean_ctor_set(v_reuseFailAlloc_381_, 10, v_quotContext_366_);
lean_ctor_set(v_reuseFailAlloc_381_, 11, v_currMacroScope_367_);
lean_ctor_set(v_reuseFailAlloc_381_, 12, v_cancelTk_x3f_368_);
lean_ctor_set(v_reuseFailAlloc_381_, 13, v_inheritedTraceOptions_370_);
lean_ctor_set_uint8(v_reuseFailAlloc_381_, sizeof(void*)*14 + 1, v_suppressElabErrors_369_);
v___x_378_ = v_reuseFailAlloc_381_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
uint8_t v___x_379_; uint8_t v___x_380_; 
lean_ctor_set_uint8(v___x_378_, sizeof(void*)*14, v___x_353_);
v___x_379_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v_options_238_, v___x_352_);
v___x_380_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_374_);
lean_dec_ref(v_env_374_);
if (v___x_380_ == 0)
{
if (v___x_379_ == 0)
{
v___y_315_ = v___x_378_;
v___y_316_ = v___x_379_;
v___y_317_ = v___x_375_;
v___y_318_ = v___y_356_;
v___y_319_ = v___x_249_;
goto v___jp_314_;
}
else
{
v___y_315_ = v___x_378_;
v___y_316_ = v___x_379_;
v___y_317_ = v___x_375_;
v___y_318_ = v___y_356_;
v___y_319_ = v___x_380_;
goto v___jp_314_;
}
}
else
{
v___y_315_ = v___x_378_;
v___y_316_ = v___x_379_;
v___y_317_ = v___x_375_;
v___y_318_ = v___y_356_;
v___y_319_ = v___x_379_;
goto v___jp_314_;
}
}
}
}
v___jp_385_:
{
uint8_t v___x_387_; 
v___x_387_ = lean_bool_not(v___y_386_);
if (v___x_387_ == 0)
{
lean_inc(v___x_253_);
v___y_355_ = v___x_350_;
v___y_356_ = v___x_253_;
goto v___jp_354_;
}
else
{
lean_object* v___x_388_; lean_object* v_env_389_; lean_object* v_nextMacroScope_390_; lean_object* v_ngen_391_; lean_object* v_auxDeclNGen_392_; lean_object* v_traceState_393_; lean_object* v_messages_394_; lean_object* v_infoState_395_; lean_object* v_snapshotTasks_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_405_; 
v___x_388_ = lean_st_ref_take(v___x_253_);
v_env_389_ = lean_ctor_get(v___x_388_, 0);
v_nextMacroScope_390_ = lean_ctor_get(v___x_388_, 1);
v_ngen_391_ = lean_ctor_get(v___x_388_, 2);
v_auxDeclNGen_392_ = lean_ctor_get(v___x_388_, 3);
v_traceState_393_ = lean_ctor_get(v___x_388_, 4);
v_messages_394_ = lean_ctor_get(v___x_388_, 6);
v_infoState_395_ = lean_ctor_get(v___x_388_, 7);
v_snapshotTasks_396_ = lean_ctor_get(v___x_388_, 8);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; 
v_unused_406_ = lean_ctor_get(v___x_388_, 5);
lean_dec(v_unused_406_);
v___x_398_ = v___x_388_;
v_isShared_399_ = v_isSharedCheck_405_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_snapshotTasks_396_);
lean_inc(v_infoState_395_);
lean_inc(v_messages_394_);
lean_inc(v_traceState_393_);
lean_inc(v_auxDeclNGen_392_);
lean_inc(v_ngen_391_);
lean_inc(v_nextMacroScope_390_);
lean_inc(v_env_389_);
lean_dec(v___x_388_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_405_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = l_Lean_Kernel_enableDiag(v_env_389_, v___x_353_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 5, v___x_233_);
lean_ctor_set(v___x_398_, 0, v___x_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_nextMacroScope_390_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_ngen_391_);
lean_ctor_set(v_reuseFailAlloc_404_, 3, v_auxDeclNGen_392_);
lean_ctor_set(v_reuseFailAlloc_404_, 4, v_traceState_393_);
lean_ctor_set(v_reuseFailAlloc_404_, 5, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_404_, 6, v_messages_394_);
lean_ctor_set(v_reuseFailAlloc_404_, 7, v_infoState_395_);
lean_ctor_set(v_reuseFailAlloc_404_, 8, v_snapshotTasks_396_);
v___x_402_ = v_reuseFailAlloc_404_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; 
v___x_403_ = lean_st_ref_set(v___x_253_, v___x_402_);
lean_inc(v___x_253_);
v___y_355_ = v___x_350_;
v___y_356_ = v___x_253_;
goto v___jp_354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___boxed(lean_object* v_info_408_, lean_object* v_x_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_408_, v_x_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM(lean_object* v_00_u03b1_412_, lean_object* v_info_413_, lean_object* v_x_414_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_413_, v_x_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___boxed(lean_object* v_00_u03b1_417_, lean_object* v_info_418_, lean_object* v_x_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Elab_ContextInfo_runCoreM(v_00_u03b1_417_, v_info_418_, v_x_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(lean_object* v___x_422_, lean_object* v_x_423_, lean_object* v___x_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_st_mk_ref(v___x_422_);
lean_inc(v___x_428_);
v___x_429_ = lean_apply_5(v_x_423_, v___x_424_, v___x_428_, v___y_425_, v___y_426_, lean_box(0));
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_439_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_439_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_439_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_439_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_434_ = lean_st_ref_get(v___x_428_);
lean_dec(v___x_428_);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v_a_430_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_435_);
v___x_437_ = v___x_432_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_dec(v___x_428_);
v_a_440_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_429_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_429_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed(lean_object* v___x_448_, lean_object* v_x_449_, lean_object* v___x_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(v___x_448_, v_x_449_, v___x_450_, v___y_451_, v___y_452_);
return v_res_454_;
}
}
static uint64_t _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1(void){
_start:
{
lean_object* v___x_461_; uint64_t v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_462_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2(void){
_start:
{
uint64_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = lean_uint64_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1);
v___x_464_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_465_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set_uint64(v___x_465_, sizeof(void*)*1, v___x_463_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4(void){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_468_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_472_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
lean_ctor_set(v___x_472_, 2, v___x_471_);
lean_ctor_set(v___x_472_, 3, v___x_471_);
lean_ctor_set(v___x_472_, 4, v___x_471_);
lean_ctor_set(v___x_472_, 5, v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = lean_unsigned_to_nat(32u);
v___x_474_ = lean_mk_empty_array_with_capacity(v___x_473_);
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8(void){
_start:
{
size_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_476_ = ((size_t)5ULL);
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = lean_unsigned_to_nat(32u);
v___x_479_ = lean_mk_empty_array_with_capacity(v___x_478_);
v___x_480_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7);
v___x_481_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_479_);
lean_ctor_set(v___x_481_, 2, v___x_477_);
lean_ctor_set(v___x_481_, 3, v___x_477_);
lean_ctor_set_usize(v___x_481_, 4, v___x_476_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
lean_ctor_set(v___x_483_, 2, v___x_482_);
lean_ctor_set(v___x_483_, 3, v___x_482_);
lean_ctor_set(v___x_483_, 4, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object* v_info_484_, lean_object* v_lctx_485_, lean_object* v_x_486_){
_start:
{
lean_object* v___x_488_; uint8_t v___x_489_; uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_toCommandContextInfo_496_; lean_object* v_mctx_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___f_502_; lean_object* v___x_503_; 
v___x_488_ = lean_box(1);
v___x_489_ = 0;
v___x_490_ = 1;
v___x_491_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2);
v___x_492_ = lean_unsigned_to_nat(0u);
v___x_493_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3));
v___x_494_ = lean_box(0);
v___x_495_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_495_, 0, v___x_491_);
lean_ctor_set(v___x_495_, 1, v___x_488_);
lean_ctor_set(v___x_495_, 2, v_lctx_485_);
lean_ctor_set(v___x_495_, 3, v___x_493_);
lean_ctor_set(v___x_495_, 4, v___x_494_);
lean_ctor_set(v___x_495_, 5, v___x_492_);
lean_ctor_set(v___x_495_, 6, v___x_494_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*7, v___x_489_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*7 + 1, v___x_489_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*7 + 2, v___x_489_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*7 + 3, v___x_490_);
v_toCommandContextInfo_496_ = lean_ctor_get(v_info_484_, 0);
v_mctx_497_ = lean_ctor_get(v_toCommandContextInfo_496_, 3);
v___x_498_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6);
v___x_499_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8);
v___x_500_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9);
lean_inc_ref(v_mctx_497_);
v___x_501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_501_, 0, v_mctx_497_);
lean_ctor_set(v___x_501_, 1, v___x_498_);
lean_ctor_set(v___x_501_, 2, v___x_488_);
lean_ctor_set(v___x_501_, 3, v___x_499_);
lean_ctor_set(v___x_501_, 4, v___x_500_);
v___f_502_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_502_, 0, v___x_501_);
lean_closure_set(v___f_502_, 1, v_x_486_);
lean_closure_set(v___f_502_, 2, v___x_495_);
v___x_503_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_484_, v___f_502_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_512_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_512_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v_fst_508_; lean_object* v___x_510_; 
v_fst_508_ = lean_ctor_get(v_a_504_, 0);
lean_inc(v_fst_508_);
lean_dec(v_a_504_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v_fst_508_);
v___x_510_ = v___x_506_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_fst_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
v_a_513_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_503_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_503_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object* v_info_521_, lean_object* v_lctx_522_, lean_object* v_x_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_521_, v_lctx_522_, v_x_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object* v_00_u03b1_526_, lean_object* v_info_527_, lean_object* v_lctx_528_, lean_object* v_x_529_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_527_, v_lctx_528_, v_x_529_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object* v_00_u03b1_532_, lean_object* v_info_533_, lean_object* v_lctx_534_, lean_object* v_x_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Elab_ContextInfo_runMetaM(v_00_u03b1_532_, v_info_533_, v_lctx_534_, v_x_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object* v_info_538_, lean_object* v_lctx_539_){
_start:
{
lean_object* v_toCommandContextInfo_540_; lean_object* v_env_541_; lean_object* v_mctx_542_; lean_object* v_options_543_; lean_object* v_currNamespace_544_; lean_object* v_openDecls_545_; lean_object* v___x_546_; 
v_toCommandContextInfo_540_ = lean_ctor_get(v_info_538_, 0);
v_env_541_ = lean_ctor_get(v_toCommandContextInfo_540_, 0);
v_mctx_542_ = lean_ctor_get(v_toCommandContextInfo_540_, 3);
v_options_543_ = lean_ctor_get(v_toCommandContextInfo_540_, 4);
v_currNamespace_544_ = lean_ctor_get(v_toCommandContextInfo_540_, 5);
v_openDecls_545_ = lean_ctor_get(v_toCommandContextInfo_540_, 6);
lean_inc(v_openDecls_545_);
lean_inc(v_currNamespace_544_);
lean_inc_ref(v_options_543_);
lean_inc_ref(v_mctx_542_);
lean_inc_ref(v_env_541_);
v___x_546_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_546_, 0, v_env_541_);
lean_ctor_set(v___x_546_, 1, v_mctx_542_);
lean_ctor_set(v___x_546_, 2, v_lctx_539_);
lean_ctor_set(v___x_546_, 3, v_options_543_);
lean_ctor_set(v___x_546_, 4, v_currNamespace_544_);
lean_ctor_set(v___x_546_, 5, v_openDecls_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object* v_info_547_, lean_object* v_lctx_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_547_, v_lctx_548_);
lean_dec_ref(v_info_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object* v_info_550_, lean_object* v_lctx_551_, lean_object* v_stx_552_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_550_, v_lctx_551_);
v___x_555_ = l_Lean_ppTerm(v___x_554_, v_stx_552_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object* v_info_557_, lean_object* v_lctx_558_, lean_object* v_stx_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Elab_ContextInfo_ppSyntax(v_info_557_, v_lctx_558_, v_stx_559_);
lean_dec_ref(v_info_557_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(lean_object* v_ctx_577_, lean_object* v_pos_578_, lean_object* v_info_579_){
_start:
{
lean_object* v_toCommandContextInfo_580_; lean_object* v_fileMap_581_; lean_object* v___x_582_; lean_object* v_line_583_; lean_object* v_column_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_607_; 
v_toCommandContextInfo_580_ = lean_ctor_get(v_ctx_577_, 0);
lean_inc_ref(v_toCommandContextInfo_580_);
lean_dec_ref(v_ctx_577_);
v_fileMap_581_ = lean_ctor_get(v_toCommandContextInfo_580_, 2);
lean_inc_ref(v_fileMap_581_);
lean_dec_ref(v_toCommandContextInfo_580_);
v___x_582_ = l_Lean_FileMap_toPosition(v_fileMap_581_, v_pos_578_);
v_line_583_ = lean_ctor_get(v___x_582_, 0);
v_column_584_ = lean_ctor_get(v___x_582_, 1);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_607_ == 0)
{
v___x_586_ = v___x_582_;
v_isShared_587_ = v_isSharedCheck_607_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_column_584_);
lean_inc(v_line_583_);
lean_dec(v___x_582_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_607_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_588_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_589_ = l_Nat_reprFast(v_line_583_);
v___x_590_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 5);
lean_ctor_set(v___x_586_, 1, v___x_590_);
lean_ctor_set(v___x_586_, 0, v___x_588_);
v___x_592_ = v___x_586_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v___x_590_);
v___x_592_ = v_reuseFailAlloc_606_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v_pos_599_; 
v___x_593_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
v___x_594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_592_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = l_Nat_reprFast(v_column_584_);
v___x_596_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
v___x_597_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_594_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v_pos_599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_pos_599_, 0, v___x_597_);
lean_ctor_set(v_pos_599_, 1, v___x_598_);
switch(lean_obj_tag(v_info_579_))
{
case 0:
{
return v_pos_599_;
}
case 1:
{
uint8_t v_canonical_603_; 
v_canonical_603_ = lean_ctor_get_uint8(v_info_579_, sizeof(void*)*2);
if (v_canonical_603_ == 1)
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9));
v___x_605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_605_, 0, v_pos_599_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
return v___x_605_;
}
else
{
goto v___jp_600_;
}
}
default: 
{
goto v___jp_600_;
}
}
v___jp_600_:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7));
v___x_602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_602_, 0, v_pos_599_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
return v___x_602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(lean_object* v_ctx_608_, lean_object* v_pos_609_, lean_object* v_info_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_608_, v_pos_609_, v_info_610_);
lean_dec(v_info_610_);
lean_dec(v_pos_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(lean_object* v_ctx_615_, lean_object* v_stx_616_){
_start:
{
lean_object* v___y_618_; lean_object* v___y_619_; uint8_t v___x_627_; lean_object* v___y_629_; lean_object* v___x_632_; 
v___x_627_ = 0;
v___x_632_ = l_Lean_Syntax_getPos_x3f(v_stx_616_, v___x_627_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v___x_633_; 
v___x_633_ = lean_unsigned_to_nat(0u);
v___y_629_ = v___x_633_;
goto v___jp_628_;
}
else
{
lean_object* v_val_634_; 
v_val_634_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_val_634_);
lean_dec_ref_known(v___x_632_, 1);
v___y_629_ = v_val_634_;
goto v___jp_628_;
}
v___jp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_620_ = l_Lean_Syntax_getHeadInfo(v_stx_616_);
lean_inc_ref(v_ctx_615_);
v___x_621_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_615_, v___y_618_, v___x_620_);
lean_dec(v___x_620_);
lean_dec(v___y_618_);
v___x_622_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = l_Lean_Syntax_getTailInfo(v_stx_616_);
v___x_625_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_615_, v___y_619_, v___x_624_);
lean_dec(v___x_624_);
lean_dec(v___y_619_);
v___x_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_623_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
return v___x_626_;
}
v___jp_628_:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Syntax_getTailPos_x3f(v_stx_616_, v___x_627_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_inc(v___y_629_);
v___y_618_ = v___y_629_;
v___y_619_ = v___y_629_;
goto v___jp_617_;
}
else
{
lean_object* v_val_631_; 
v_val_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v___x_630_, 1);
v___y_618_ = v___y_629_;
v___y_619_ = v_val_631_;
goto v___jp_617_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(lean_object* v_ctx_635_, lean_object* v_stx_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_635_, v_stx_636_);
lean_dec(v_stx_636_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(lean_object* v_ctx_641_, lean_object* v_info_642_){
_start:
{
lean_object* v_elaborator_643_; lean_object* v_stx_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_659_; 
v_elaborator_643_ = lean_ctor_get(v_info_642_, 0);
v_stx_644_ = lean_ctor_get(v_info_642_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v_info_642_);
if (v_isSharedCheck_659_ == 0)
{
v___x_646_ = v_info_642_;
v_isShared_647_ = v_isSharedCheck_659_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_stx_644_);
lean_inc(v_elaborator_643_);
lean_dec(v_info_642_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_659_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
uint8_t v___x_648_; 
v___x_648_ = l_Lean_Name_isAnonymous(v_elaborator_643_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_649_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_641_, v_stx_644_);
lean_dec(v_stx_644_);
v___x_650_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
if (v_isShared_647_ == 0)
{
lean_ctor_set_tag(v___x_646_, 5);
lean_ctor_set(v___x_646_, 1, v___x_650_);
lean_ctor_set(v___x_646_, 0, v___x_649_);
v___x_652_ = v___x_646_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v___x_650_);
v___x_652_ = v_reuseFailAlloc_657_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
uint8_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_653_ = 1;
v___x_654_ = l_Lean_Name_toString(v_elaborator_643_, v___x_653_);
v___x_655_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
v___x_656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_652_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
return v___x_656_;
}
}
else
{
lean_object* v___x_658_; 
lean_del_object(v___x_646_);
lean_dec(v_elaborator_643_);
v___x_658_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_641_, v_stx_644_);
lean_dec(v_stx_644_);
return v___x_658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object* v_info_660_, lean_object* v_ctx_661_, lean_object* v_x_662_){
_start:
{
lean_object* v_lctx_664_; lean_object* v___x_665_; 
v_lctx_664_ = lean_ctor_get(v_info_660_, 1);
lean_inc_ref(v_lctx_664_);
lean_dec_ref(v_info_660_);
v___x_665_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_661_, v_lctx_664_, v_x_662_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(lean_object* v_info_666_, lean_object* v_ctx_667_, lean_object* v_x_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_666_, v_ctx_667_, v_x_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM(lean_object* v_00_u03b1_671_, lean_object* v_info_672_, lean_object* v_ctx_673_, lean_object* v_x_674_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_672_, v_ctx_673_, v_x_674_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___boxed(lean_object* v_00_u03b1_677_, lean_object* v_info_678_, lean_object* v_ctx_679_, lean_object* v_x_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Elab_TermInfo_runMetaM(v_00_u03b1_677_, v_info_678_, v_ctx_679_, v_x_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0(lean_object* v_ctx_697_, lean_object* v_toElabInfo_698_, lean_object* v_expr_699_, uint8_t v_isBinder_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v_a_721_; lean_object* v___y_731_; uint8_t v___y_732_; lean_object* v___y_735_; lean_object* v_a_736_; lean_object* v___x_739_; 
lean_inc(v___y_704_);
lean_inc_ref(v___y_703_);
lean_inc(v___y_702_);
lean_inc_ref(v___y_701_);
lean_inc_ref(v_expr_699_);
v___x_739_ = lean_infer_type(v_expr_699_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_741_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_739_, 1);
v___x_741_ = l_Lean_Meta_ppExpr(v_a_740_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_741_, 1);
v_a_721_ = v_a_742_;
goto v___jp_720_;
}
else
{
lean_object* v_a_743_; 
v_a_743_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_743_);
v___y_735_ = v___x_741_;
v_a_736_ = v_a_743_;
goto v___jp_734_;
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
v_a_744_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_739_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_739_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
lean_inc(v_a_744_);
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
v___y_735_ = v___x_749_;
v_a_736_ = v_a_744_;
goto v___jp_734_;
}
}
}
v___jp_706_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
lean_inc_ref(v___y_709_);
v___x_710_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_710_, 0, v___y_709_);
v___x_711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_711_, 0, v___y_707_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v___y_708_);
v___x_715_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_697_, v_toElabInfo_698_);
v___x_718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
v___jp_720_:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Meta_ppExpr(v_expr_699_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_722_, 1);
v___x_724_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__3));
v___x_725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v_a_723_);
v___x_726_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
v___x_727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
if (v_isBinder_700_ == 0)
{
lean_object* v___x_728_; 
v___x_728_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__6));
v___y_707_ = v___x_727_;
v___y_708_ = v_a_721_;
v___y_709_ = v___x_728_;
goto v___jp_706_;
}
else
{
lean_object* v___x_729_; 
v___x_729_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__7));
v___y_707_ = v___x_727_;
v___y_708_ = v_a_721_;
v___y_709_ = v___x_729_;
goto v___jp_706_;
}
}
else
{
lean_dec(v_a_721_);
lean_dec_ref(v_toElabInfo_698_);
lean_dec_ref(v_ctx_697_);
return v___x_722_;
}
}
v___jp_730_:
{
if (v___y_732_ == 0)
{
lean_object* v___x_733_; 
lean_dec_ref(v___y_731_);
v___x_733_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__9));
v_a_721_ = v___x_733_;
goto v___jp_720_;
}
else
{
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec_ref(v_expr_699_);
lean_dec_ref(v_toElabInfo_698_);
lean_dec_ref(v_ctx_697_);
return v___y_731_;
}
}
v___jp_734_:
{
uint8_t v___x_737_; 
v___x_737_ = l_Lean_Exception_isInterrupt(v_a_736_);
if (v___x_737_ == 0)
{
uint8_t v___x_738_; 
v___x_738_ = l_Lean_Exception_isRuntime(v_a_736_);
v___y_731_ = v___y_735_;
v___y_732_ = v___x_738_;
goto v___jp_730_;
}
else
{
lean_dec_ref(v_a_736_);
v___y_731_ = v___y_735_;
v___y_732_ = v___x_737_;
goto v___jp_730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0___boxed(lean_object* v_ctx_752_, lean_object* v_toElabInfo_753_, lean_object* v_expr_754_, lean_object* v_isBinder_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
uint8_t v_isBinder_boxed_761_; lean_object* v_res_762_; 
v_isBinder_boxed_761_ = lean_unbox(v_isBinder_755_);
v_res_762_ = l_Lean_Elab_TermInfo_format___lam__0(v_ctx_752_, v_toElabInfo_753_, v_expr_754_, v_isBinder_boxed_761_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format(lean_object* v_ctx_763_, lean_object* v_info_764_){
_start:
{
lean_object* v_toElabInfo_766_; lean_object* v_expr_767_; uint8_t v_isBinder_768_; lean_object* v___x_769_; lean_object* v___f_770_; lean_object* v___x_771_; 
v_toElabInfo_766_ = lean_ctor_get(v_info_764_, 0);
v_expr_767_ = lean_ctor_get(v_info_764_, 3);
v_isBinder_768_ = lean_ctor_get_uint8(v_info_764_, sizeof(void*)*4);
v___x_769_ = lean_box(v_isBinder_768_);
lean_inc_ref(v_expr_767_);
lean_inc_ref(v_toElabInfo_766_);
lean_inc_ref(v_ctx_763_);
v___f_770_ = lean_alloc_closure((void*)(l_Lean_Elab_TermInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_770_, 0, v_ctx_763_);
lean_closure_set(v___f_770_, 1, v_toElabInfo_766_);
lean_closure_set(v___f_770_, 2, v_expr_767_);
lean_closure_set(v___f_770_, 3, v___x_769_);
v___x_771_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_764_, v_ctx_763_, v___f_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___boxed(lean_object* v_ctx_772_, lean_object* v_info_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_Elab_TermInfo_format(v_ctx_772_, v_info_773_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialTermInfo_format(lean_object* v_ctx_779_, lean_object* v_info_780_){
_start:
{
lean_object* v_toElabInfo_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v_toElabInfo_781_ = lean_ctor_get(v_info_780_, 0);
lean_inc_ref(v_toElabInfo_781_);
lean_dec_ref(v_info_780_);
v___x_782_ = ((lean_object*)(l_Lean_Elab_PartialTermInfo_format___closed__1));
v___x_783_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_779_, v_toElabInfo_781_);
v___x_784_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(lean_object* v_x_791_){
_start:
{
if (lean_obj_tag(v_x_791_) == 0)
{
lean_object* v___x_792_; 
v___x_792_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_792_;
}
else
{
lean_object* v_val_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_803_; 
v_val_793_ = lean_ctor_get(v_x_791_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v_x_791_);
if (v_isSharedCheck_803_ == 0)
{
v___x_795_ = v_x_791_;
v_isShared_796_ = v_isSharedCheck_803_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_val_793_);
lean_dec(v_x_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_803_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_797_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_798_ = lean_expr_dbg_to_string(v_val_793_);
lean_dec(v_val_793_);
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 3);
lean_ctor_set(v___x_795_, 0, v___x_798_);
v___x_800_ = v___x_795_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_802_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; 
v___x_801_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_797_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
return v___x_801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0(lean_object* v_ctx_810_, lean_object* v_lctx_811_, lean_object* v_stx_812_, lean_object* v_expectedType_x3f_813_, lean_object* v_info_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_839_; 
v___x_820_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_810_, v_lctx_811_, v_stx_812_);
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_839_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_839_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_839_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_825_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__1));
v___x_826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v_a_821_);
v___x_827_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_826_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_813_);
v___x_830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_828_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = l_Lean_Elab_CompletionInfo_stx(v_info_814_);
v___x_834_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_810_, v___x_833_);
lean_dec(v___x_833_);
v___x_835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_832_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_835_);
v___x_837_ = v___x_823_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___boxed(lean_object* v_ctx_840_, lean_object* v_lctx_841_, lean_object* v_stx_842_, lean_object* v_expectedType_x3f_843_, lean_object* v_info_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_Elab_CompletionInfo_format___lam__0(v_ctx_840_, v_lctx_841_, v_stx_842_, v_expectedType_x3f_843_, v_info_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec_ref(v_info_844_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format(lean_object* v_ctx_857_, lean_object* v_info_858_){
_start:
{
switch(lean_obj_tag(v_info_858_))
{
case 0:
{
lean_object* v_termInfo_860_; lean_object* v_expectedType_x3f_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_882_; 
v_termInfo_860_ = lean_ctor_get(v_info_858_, 0);
v_expectedType_x3f_861_ = lean_ctor_get(v_info_858_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v_info_858_);
if (v_isSharedCheck_882_ == 0)
{
v___x_863_ = v_info_858_;
v_isShared_864_ = v_isSharedCheck_882_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_expectedType_x3f_861_);
lean_inc(v_termInfo_860_);
lean_dec(v_info_858_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_882_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Elab_TermInfo_format(v_ctx_857_, v_termInfo_860_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_881_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_881_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_881_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_881_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__1));
if (v_isShared_864_ == 0)
{
lean_ctor_set_tag(v___x_863_, 5);
lean_ctor_set(v___x_863_, 1, v_a_866_);
lean_ctor_set(v___x_863_, 0, v___x_870_);
v___x_872_ = v___x_863_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_a_866_);
v___x_872_ = v_reuseFailAlloc_880_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_873_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_861_);
v___x_876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_876_);
v___x_878_ = v___x_868_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
else
{
lean_del_object(v___x_863_);
lean_dec(v_expectedType_x3f_861_);
return v___x_865_;
}
}
}
case 1:
{
lean_object* v_stx_883_; lean_object* v_lctx_884_; lean_object* v_expectedType_x3f_885_; lean_object* v___f_886_; lean_object* v___x_887_; 
v_stx_883_ = lean_ctor_get(v_info_858_, 0);
lean_inc(v_stx_883_);
v_lctx_884_ = lean_ctor_get(v_info_858_, 2);
lean_inc_ref_n(v_lctx_884_, 2);
v_expectedType_x3f_885_ = lean_ctor_get(v_info_858_, 3);
lean_inc(v_expectedType_x3f_885_);
lean_inc_ref(v_ctx_857_);
v___f_886_ = lean_alloc_closure((void*)(l_Lean_Elab_CompletionInfo_format___lam__0___boxed), 10, 5);
lean_closure_set(v___f_886_, 0, v_ctx_857_);
lean_closure_set(v___f_886_, 1, v_lctx_884_);
lean_closure_set(v___f_886_, 2, v_stx_883_);
lean_closure_set(v___f_886_, 3, v_expectedType_x3f_885_);
lean_closure_set(v___f_886_, 4, v_info_858_);
v___x_887_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_857_, v_lctx_884_, v___f_886_);
return v___x_887_;
}
default: 
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_888_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__3));
v___x_889_ = l_Lean_Elab_CompletionInfo_stx(v_info_858_);
lean_dec_ref(v_info_858_);
v___x_890_ = lean_box(0);
v___x_891_ = 0;
lean_inc(v___x_889_);
v___x_892_ = l_Lean_Syntax_formatStx(v___x_889_, v___x_890_, v___x_891_);
v___x_893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_888_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_857_, v___x_889_);
lean_dec(v___x_889_);
v___x_897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___boxed(lean_object* v_ctx_899_, lean_object* v_info_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_Elab_CompletionInfo_format(v_ctx_899_, v_info_900_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format(lean_object* v_ctx_906_, lean_object* v_info_907_){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_909_ = ((lean_object*)(l_Lean_Elab_CommandInfo_format___closed__1));
v___x_910_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_906_, v_info_907_);
v___x_911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format___boxed(lean_object* v_ctx_913_, lean_object* v_info_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_Elab_CommandInfo_format(v_ctx_913_, v_info_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format(lean_object* v_ctx_920_, lean_object* v_info_921_){
_start:
{
lean_object* v_stx_923_; lean_object* v_optionName_924_; lean_object* v___x_925_; uint8_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v_stx_923_ = lean_ctor_get(v_info_921_, 0);
lean_inc(v_stx_923_);
v_optionName_924_ = lean_ctor_get(v_info_921_, 1);
lean_inc(v_optionName_924_);
lean_dec_ref(v_info_921_);
v___x_925_ = ((lean_object*)(l_Lean_Elab_OptionInfo_format___closed__1));
v___x_926_ = 1;
v___x_927_ = l_Lean_Name_toString(v_optionName_924_, v___x_926_);
v___x_928_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
v___x_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_925_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_920_, v_stx_923_);
lean_dec(v_stx_923_);
v___x_933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format___boxed(lean_object* v_ctx_935_, lean_object* v_info_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_Elab_OptionInfo_format(v_ctx_935_, v_info_936_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format(lean_object* v_ctx_942_, lean_object* v_info_943_){
_start:
{
lean_object* v_stx_945_; lean_object* v_errorName_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_962_; 
v_stx_945_ = lean_ctor_get(v_info_943_, 0);
v_errorName_946_ = lean_ctor_get(v_info_943_, 1);
v_isSharedCheck_962_ = !lean_is_exclusive(v_info_943_);
if (v_isSharedCheck_962_ == 0)
{
v___x_948_ = v_info_943_;
v_isShared_949_ = v_isSharedCheck_962_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_errorName_946_);
lean_inc(v_stx_945_);
lean_dec(v_info_943_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_962_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; uint8_t v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_950_ = ((lean_object*)(l_Lean_Elab_ErrorNameInfo_format___closed__1));
v___x_951_ = 1;
v___x_952_ = l_Lean_Name_toString(v_errorName_946_, v___x_951_);
v___x_953_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
if (v_isShared_949_ == 0)
{
lean_ctor_set_tag(v___x_948_, 5);
lean_ctor_set(v___x_948_, 1, v___x_953_);
lean_ctor_set(v___x_948_, 0, v___x_950_);
v___x_955_ = v___x_948_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v___x_953_);
v___x_955_ = v_reuseFailAlloc_961_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_956_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_942_, v_stx_945_);
lean_dec(v_stx_945_);
v___x_959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format___boxed(lean_object* v_ctx_963_, lean_object* v_info_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_963_, v_info_964_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0(lean_object* v_val_973_, lean_object* v_fieldName_974_, lean_object* v_ctx_975_, lean_object* v_stx_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; 
lean_inc(v___y_980_);
lean_inc_ref(v___y_979_);
lean_inc(v___y_978_);
lean_inc_ref(v___y_977_);
lean_inc_ref(v_val_973_);
v___x_982_ = lean_infer_type(v_val_973_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_984_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = l_Lean_Meta_ppExpr(v_a_983_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1015_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_1015_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1015_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_Meta_ppExpr(v_val_973_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1014_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1014_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1014_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; uint8_t v___x_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
v___x_994_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__1));
v___x_995_ = 1;
v___x_996_ = l_Lean_Name_toString(v_fieldName_974_, v___x_995_);
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 3);
lean_ctor_set(v___x_987_, 0, v___x_996_);
v___x_998_ = v___x_987_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_996_);
v___x_998_ = v_reuseFailAlloc_1013_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_994_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v_a_985_);
v___x_1003_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__3));
v___x_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v_a_990_);
v___x_1006_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_975_, v_stx_976_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_1009_);
v___x_1011_ = v___x_992_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
else
{
lean_del_object(v___x_987_);
lean_dec(v_a_985_);
lean_dec_ref(v_ctx_975_);
lean_dec(v_fieldName_974_);
return v___x_989_;
}
}
}
else
{
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec_ref(v_ctx_975_);
lean_dec(v_fieldName_974_);
lean_dec_ref(v_val_973_);
return v___x_984_;
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec_ref(v_ctx_975_);
lean_dec(v_fieldName_974_);
lean_dec_ref(v_val_973_);
v_a_1016_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_982_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_982_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0___boxed(lean_object* v_val_1024_, lean_object* v_fieldName_1025_, lean_object* v_ctx_1026_, lean_object* v_stx_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Elab_FieldInfo_format___lam__0(v_val_1024_, v_fieldName_1025_, v_ctx_1026_, v_stx_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v_stx_1027_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format(lean_object* v_ctx_1034_, lean_object* v_info_1035_){
_start:
{
lean_object* v_fieldName_1037_; lean_object* v_lctx_1038_; lean_object* v_val_1039_; lean_object* v_stx_1040_; lean_object* v___f_1041_; lean_object* v___x_1042_; 
v_fieldName_1037_ = lean_ctor_get(v_info_1035_, 1);
lean_inc(v_fieldName_1037_);
v_lctx_1038_ = lean_ctor_get(v_info_1035_, 2);
lean_inc_ref(v_lctx_1038_);
v_val_1039_ = lean_ctor_get(v_info_1035_, 3);
lean_inc_ref(v_val_1039_);
v_stx_1040_ = lean_ctor_get(v_info_1035_, 4);
lean_inc(v_stx_1040_);
lean_dec_ref(v_info_1035_);
lean_inc_ref(v_ctx_1034_);
v___f_1041_ = lean_alloc_closure((void*)(l_Lean_Elab_FieldInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1041_, 0, v_val_1039_);
lean_closure_set(v___f_1041_, 1, v_fieldName_1037_);
lean_closure_set(v___f_1041_, 2, v_ctx_1034_);
lean_closure_set(v___f_1041_, 3, v_stx_1040_);
v___x_1042_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1034_, v_lctx_1038_, v___f_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___boxed(lean_object* v_ctx_1043_, lean_object* v_info_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_Elab_FieldInfo_format(v_ctx_1043_, v_info_1044_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(lean_object* v_pre_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_){
_start:
{
if (lean_obj_tag(v_x_1049_) == 0)
{
lean_dec(v_pre_1047_);
return v_x_1048_;
}
else
{
lean_object* v_head_1050_; lean_object* v_tail_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1060_; 
v_head_1050_ = lean_ctor_get(v_x_1049_, 0);
v_tail_1051_ = lean_ctor_get(v_x_1049_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_x_1049_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1053_ = v_x_1049_;
v_isShared_1054_ = v_isSharedCheck_1060_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_tail_1051_);
lean_inc(v_head_1050_);
lean_dec(v_x_1049_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1060_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
lean_inc(v_pre_1047_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set_tag(v___x_1053_, 5);
lean_ctor_set(v___x_1053_, 1, v_pre_1047_);
lean_ctor_set(v___x_1053_, 0, v_x_1048_);
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_x_1048_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_pre_1047_);
v___x_1056_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v_head_1050_);
v_x_1048_ = v___x_1057_;
v_x_1049_ = v_tail_1051_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(lean_object* v_pre_1061_, lean_object* v_x_1062_){
_start:
{
if (lean_obj_tag(v_x_1062_) == 0)
{
lean_object* v___x_1063_; 
lean_dec(v_pre_1061_);
v___x_1063_ = lean_box(0);
return v___x_1063_;
}
else
{
lean_object* v_head_1064_; lean_object* v_tail_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1073_; 
v_head_1064_ = lean_ctor_get(v_x_1062_, 0);
v_tail_1065_ = lean_ctor_get(v_x_1062_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_x_1062_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1067_ = v_x_1062_;
v_isShared_1068_ = v_isSharedCheck_1073_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_tail_1065_);
lean_inc(v_head_1064_);
lean_dec(v_x_1062_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1073_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
lean_inc(v_pre_1061_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set_tag(v___x_1067_, 5);
lean_ctor_set(v___x_1067_, 1, v_head_1064_);
lean_ctor_set(v___x_1067_, 0, v_pre_1061_);
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_pre_1061_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_head_1064_);
v___x_1070_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(v_pre_1061_, v___x_1070_, v_tail_1065_);
return v___x_1071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(lean_object* v_x_1074_, lean_object* v_x_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
if (lean_obj_tag(v_x_1074_) == 0)
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = l_List_reverse___redArg(v_x_1075_);
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
else
{
lean_object* v_head_1083_; lean_object* v_tail_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1102_; 
v_head_1083_ = lean_ctor_get(v_x_1074_, 0);
v_tail_1084_ = lean_ctor_get(v_x_1074_, 1);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_x_1074_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1086_ = v_x_1074_;
v_isShared_1087_ = v_isSharedCheck_1102_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_tail_1084_);
lean_inc(v_head_1083_);
lean_dec(v_x_1074_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1102_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_Meta_ppGoal(v_head_1083_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v_head_1083_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1091_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 1);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 1, v_x_1075_);
lean_ctor_set(v___x_1086_, 0, v_a_1089_);
v___x_1091_ = v___x_1086_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1089_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_x_1075_);
v___x_1091_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
v_x_1074_ = v_tail_1084_;
v_x_1075_ = v___x_1091_;
goto _start;
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_del_object(v___x_1086_);
lean_dec(v_tail_1084_);
lean_dec(v_x_1075_);
v_a_1094_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1088_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1088_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(lean_object* v_x_1103_, lean_object* v_x_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_x_1103_, v_x_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0(lean_object* v_goals_1114_, lean_object* v___x_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_goals_1114_, v___x_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1131_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1124_ = v___x_1121_;
v_isShared_1125_ = v_isSharedCheck_1131_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1121_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1131_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1126_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1127_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1126_, v_a_1122_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1127_);
v___x_1129_ = v___x_1124_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
v_a_1132_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1121_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1121_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(lean_object* v_goals_1140_, lean_object* v___x_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0(v_goals_1140_, v___x_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
return v_res_1147_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0(void){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1148_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__0, &l_Lean_Elab_ContextInfo_ppGoals___closed__0_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0);
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = lean_unsigned_to_nat(32u);
v___x_1152_ = lean_mk_empty_array_with_capacity(v___x_1151_);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3(void){
_start:
{
size_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1154_ = ((size_t)5ULL);
v___x_1155_ = lean_unsigned_to_nat(0u);
v___x_1156_ = lean_unsigned_to_nat(32u);
v___x_1157_ = lean_mk_empty_array_with_capacity(v___x_1156_);
v___x_1158_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_1159_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
lean_ctor_set(v___x_1159_, 1, v___x_1157_);
lean_ctor_set(v___x_1159_, 2, v___x_1155_);
lean_ctor_set(v___x_1159_, 3, v___x_1155_);
lean_ctor_set_usize(v___x_1159_, 4, v___x_1154_);
return v___x_1159_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1160_ = lean_box(1);
v___x_1161_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_1162_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__1, &l_Lean_Elab_ContextInfo_ppGoals___closed__1_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1);
v___x_1163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
lean_ctor_set(v___x_1163_, 1, v___x_1161_);
lean_ctor_set(v___x_1163_, 2, v___x_1160_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object* v_ctx_1167_, lean_object* v_goals_1168_){
_start:
{
uint8_t v___x_1170_; 
v___x_1170_ = l_List_isEmpty___redArg(v_goals_1168_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___f_1173_; lean_object* v___x_1174_; 
v___x_1171_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__4, &l_Lean_Elab_ContextInfo_ppGoals___closed__4_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4);
v___x_1172_ = lean_box(0);
v___f_1173_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1173_, 0, v_goals_1168_);
lean_closure_set(v___f_1173_, 1, v___x_1172_);
v___x_1174_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1167_, v___x_1171_, v___f_1173_);
return v___x_1174_;
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_dec(v_goals_1168_);
lean_dec_ref(v_ctx_1167_);
v___x_1175_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___closed__6));
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
return v___x_1176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object* v_ctx_1177_, lean_object* v_goals_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctx_1177_, v_goals_1178_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format(lean_object* v_ctx_1190_, lean_object* v_info_1191_){
_start:
{
lean_object* v_toCommandContextInfo_1193_; lean_object* v_parentDecl_x3f_1194_; lean_object* v_autoImplicits_1195_; lean_object* v_env_1196_; lean_object* v_cmdEnv_x3f_1197_; lean_object* v_fileMap_1198_; lean_object* v_options_1199_; lean_object* v_currNamespace_1200_; lean_object* v_openDecls_1201_; lean_object* v_ngen_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1244_; 
v_toCommandContextInfo_1193_ = lean_ctor_get(v_ctx_1190_, 0);
lean_inc_ref(v_toCommandContextInfo_1193_);
v_parentDecl_x3f_1194_ = lean_ctor_get(v_ctx_1190_, 1);
v_autoImplicits_1195_ = lean_ctor_get(v_ctx_1190_, 2);
v_env_1196_ = lean_ctor_get(v_toCommandContextInfo_1193_, 0);
v_cmdEnv_x3f_1197_ = lean_ctor_get(v_toCommandContextInfo_1193_, 1);
v_fileMap_1198_ = lean_ctor_get(v_toCommandContextInfo_1193_, 2);
v_options_1199_ = lean_ctor_get(v_toCommandContextInfo_1193_, 4);
v_currNamespace_1200_ = lean_ctor_get(v_toCommandContextInfo_1193_, 5);
v_openDecls_1201_ = lean_ctor_get(v_toCommandContextInfo_1193_, 6);
v_ngen_1202_ = lean_ctor_get(v_toCommandContextInfo_1193_, 7);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_toCommandContextInfo_1193_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; 
v_unused_1245_ = lean_ctor_get(v_toCommandContextInfo_1193_, 3);
lean_dec(v_unused_1245_);
v___x_1204_ = v_toCommandContextInfo_1193_;
v_isShared_1205_ = v_isSharedCheck_1244_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_ngen_1202_);
lean_inc(v_openDecls_1201_);
lean_inc(v_currNamespace_1200_);
lean_inc(v_options_1199_);
lean_inc(v_fileMap_1198_);
lean_inc(v_cmdEnv_x3f_1197_);
lean_inc(v_env_1196_);
lean_dec(v_toCommandContextInfo_1193_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1244_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v_toElabInfo_1206_; lean_object* v_mctxBefore_1207_; lean_object* v_goalsBefore_1208_; lean_object* v_mctxAfter_1209_; lean_object* v_goalsAfter_1210_; lean_object* v___x_1212_; 
v_toElabInfo_1206_ = lean_ctor_get(v_info_1191_, 0);
lean_inc_ref(v_toElabInfo_1206_);
v_mctxBefore_1207_ = lean_ctor_get(v_info_1191_, 1);
lean_inc_ref(v_mctxBefore_1207_);
v_goalsBefore_1208_ = lean_ctor_get(v_info_1191_, 2);
lean_inc(v_goalsBefore_1208_);
v_mctxAfter_1209_ = lean_ctor_get(v_info_1191_, 3);
lean_inc_ref(v_mctxAfter_1209_);
v_goalsAfter_1210_ = lean_ctor_get(v_info_1191_, 4);
lean_inc(v_goalsAfter_1210_);
lean_dec_ref(v_info_1191_);
lean_inc_ref(v_ngen_1202_);
lean_inc(v_openDecls_1201_);
lean_inc(v_currNamespace_1200_);
lean_inc_ref(v_options_1199_);
lean_inc_ref(v_fileMap_1198_);
lean_inc(v_cmdEnv_x3f_1197_);
lean_inc_ref(v_env_1196_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 3, v_mctxBefore_1207_);
v___x_1212_ = v___x_1204_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_env_1196_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_cmdEnv_x3f_1197_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v_fileMap_1198_);
lean_ctor_set(v_reuseFailAlloc_1243_, 3, v_mctxBefore_1207_);
lean_ctor_set(v_reuseFailAlloc_1243_, 4, v_options_1199_);
lean_ctor_set(v_reuseFailAlloc_1243_, 5, v_currNamespace_1200_);
lean_ctor_set(v_reuseFailAlloc_1243_, 6, v_openDecls_1201_);
lean_ctor_set(v_reuseFailAlloc_1243_, 7, v_ngen_1202_);
v___x_1212_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v_ctxB_1213_; lean_object* v___x_1214_; 
lean_inc_ref(v_autoImplicits_1195_);
lean_inc(v_parentDecl_x3f_1194_);
v_ctxB_1213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxB_1213_, 0, v___x_1212_);
lean_ctor_set(v_ctxB_1213_, 1, v_parentDecl_x3f_1194_);
lean_ctor_set(v_ctxB_1213_, 2, v_autoImplicits_1195_);
v___x_1214_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxB_1213_, v_goalsBefore_1208_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1216_; lean_object* v_ctxA_1217_; lean_object* v___x_1218_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1216_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1216_, 0, v_env_1196_);
lean_ctor_set(v___x_1216_, 1, v_cmdEnv_x3f_1197_);
lean_ctor_set(v___x_1216_, 2, v_fileMap_1198_);
lean_ctor_set(v___x_1216_, 3, v_mctxAfter_1209_);
lean_ctor_set(v___x_1216_, 4, v_options_1199_);
lean_ctor_set(v___x_1216_, 5, v_currNamespace_1200_);
lean_ctor_set(v___x_1216_, 6, v_openDecls_1201_);
lean_ctor_set(v___x_1216_, 7, v_ngen_1202_);
lean_inc_ref(v_autoImplicits_1195_);
lean_inc(v_parentDecl_x3f_1194_);
v_ctxA_1217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxA_1217_, 0, v___x_1216_);
lean_ctor_set(v_ctxA_1217_, 1, v_parentDecl_x3f_1194_);
lean_ctor_set(v_ctxA_1217_, 2, v_autoImplicits_1195_);
v___x_1218_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxA_1217_, v_goalsAfter_1210_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1242_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1242_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1242_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v_stx_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1240_; 
v_stx_1223_ = lean_ctor_get(v_toElabInfo_1206_, 1);
lean_inc(v_stx_1223_);
v___x_1224_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__1));
v___x_1225_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1190_, v_toElabInfo_1206_);
v___x_1226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1226_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = lean_box(0);
v___x_1230_ = 0;
v___x_1231_ = l_Lean_Syntax_formatStx(v_stx_1223_, v___x_1229_, v___x_1230_);
v___x_1232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1228_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__3));
v___x_1234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
lean_ctor_set(v___x_1235_, 1, v_a_1215_);
v___x_1236_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__5));
v___x_1237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v_a_1219_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1238_);
v___x_1240_ = v___x_1221_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
else
{
lean_dec(v_a_1215_);
lean_dec_ref(v_toElabInfo_1206_);
lean_dec_ref(v_ctx_1190_);
return v___x_1218_;
}
}
else
{
lean_dec(v_goalsAfter_1210_);
lean_dec_ref(v_mctxAfter_1209_);
lean_dec_ref(v_toElabInfo_1206_);
lean_dec_ref(v_ngen_1202_);
lean_dec(v_openDecls_1201_);
lean_dec(v_currNamespace_1200_);
lean_dec_ref(v_options_1199_);
lean_dec_ref(v_fileMap_1198_);
lean_dec(v_cmdEnv_x3f_1197_);
lean_dec_ref(v_env_1196_);
lean_dec_ref(v_ctx_1190_);
return v___x_1214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format___boxed(lean_object* v_ctx_1246_, lean_object* v_info_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_Elab_TacticInfo_format(v_ctx_1246_, v_info_1247_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object* v_ctx_1256_, lean_object* v_info_1257_){
_start:
{
lean_object* v_lctx_1259_; lean_object* v_stx_1260_; lean_object* v_output_1261_; lean_object* v___x_1262_; lean_object* v_a_1263_; lean_object* v___x_1264_; lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1277_; 
v_lctx_1259_ = lean_ctor_get(v_info_1257_, 0);
lean_inc_ref_n(v_lctx_1259_, 2);
v_stx_1260_ = lean_ctor_get(v_info_1257_, 1);
lean_inc(v_stx_1260_);
v_output_1261_ = lean_ctor_get(v_info_1257_, 2);
lean_inc(v_output_1261_);
lean_dec_ref(v_info_1257_);
v___x_1262_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1256_, v_lctx_1259_, v_stx_1260_);
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref(v___x_1262_);
v___x_1264_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1256_, v_lctx_1259_, v_output_1261_);
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1267_ = v___x_1264_;
v_isShared_1268_ = v_isSharedCheck_1277_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1277_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1269_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__1));
v___x_1270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set(v___x_1270_, 1, v_a_1263_);
v___x_1271_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__3));
v___x_1272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1270_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
lean_ctor_set(v___x_1273_, 1, v_a_1265_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1273_);
v___x_1275_ = v___x_1267_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object* v_ctx_1278_, lean_object* v_info_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1278_, v_info_1279_);
lean_dec_ref(v_ctx_1278_);
return v_res_1281_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__0(void){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1282_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__1(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__0, &l_Lean_Elab_UserWidgetInfo_format___closed__0_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__0);
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
return v___x_1284_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__2(void){
_start:
{
uint8_t v___x_1285_; size_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1285_ = 1;
v___x_1286_ = ((size_t)0ULL);
v___x_1287_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__1, &l_Lean_Elab_UserWidgetInfo_format___closed__1_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__1);
v___x_1288_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
lean_ctor_set_usize(v___x_1288_, 2, v___x_1286_);
lean_ctor_set_uint8(v___x_1288_, sizeof(void*)*3, v___x_1285_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_UserWidgetInfo_format(lean_object* v_info_1292_){
_start:
{
lean_object* v_toWidgetInstance_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1322_; 
v_toWidgetInstance_1293_ = lean_ctor_get(v_info_1292_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_info_1292_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; 
v_unused_1323_ = lean_ctor_get(v_info_1292_, 1);
lean_dec(v_unused_1323_);
v___x_1295_ = v_info_1292_;
v_isShared_1296_ = v_isSharedCheck_1322_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_toWidgetInstance_1293_);
lean_dec(v_info_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1322_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v_id_1297_; lean_object* v_props_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v_fst_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1320_; 
v_id_1297_ = lean_ctor_get(v_toWidgetInstance_1293_, 0);
lean_inc(v_id_1297_);
v_props_1298_ = lean_ctor_get(v_toWidgetInstance_1293_, 1);
lean_inc_ref(v_props_1298_);
lean_dec_ref(v_toWidgetInstance_1293_);
v___x_1299_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__2, &l_Lean_Elab_UserWidgetInfo_format___closed__2_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__2);
v___x_1300_ = lean_apply_1(v_props_1298_, v___x_1299_);
v_fst_1301_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; 
v_unused_1321_ = lean_ctor_get(v___x_1300_, 1);
lean_dec(v_unused_1321_);
v___x_1303_ = v___x_1300_;
v_isShared_1304_ = v_isSharedCheck_1320_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_fst_1301_);
lean_dec(v___x_1300_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1320_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1305_; uint8_t v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
v___x_1305_ = ((lean_object*)(l_Lean_Elab_UserWidgetInfo_format___closed__4));
v___x_1306_ = 1;
v___x_1307_ = l_Lean_Name_toString(v_id_1297_, v___x_1306_);
v___x_1308_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set_tag(v___x_1303_, 5);
lean_ctor_set(v___x_1303_, 1, v___x_1308_);
lean_ctor_set(v___x_1303_, 0, v___x_1305_);
v___x_1310_ = v___x_1303_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1311_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
if (v_isShared_1296_ == 0)
{
lean_ctor_set_tag(v___x_1295_, 5);
lean_ctor_set(v___x_1295_, 1, v___x_1311_);
lean_ctor_set(v___x_1295_, 0, v___x_1310_);
v___x_1313_ = v___x_1295_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1314_ = lean_unsigned_to_nat(80u);
v___x_1315_ = l_Lean_Json_pretty(v_fst_1301_, v___x_1314_);
v___x_1316_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
v___x_1317_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1313_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
return v___x_1317_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FVarAliasInfo_format(lean_object* v_info_1330_){
_start:
{
lean_object* v_userName_1331_; lean_object* v_id_1332_; lean_object* v_baseId_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_userName_1331_ = lean_ctor_get(v_info_1330_, 0);
lean_inc(v_userName_1331_);
v_id_1332_ = lean_ctor_get(v_info_1330_, 1);
lean_inc(v_id_1332_);
v_baseId_1333_ = lean_ctor_get(v_info_1330_, 2);
lean_inc(v_baseId_1333_);
lean_dec_ref(v_info_1330_);
v___x_1334_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__1));
v___x_1335_ = l_Lean_Name_eraseMacroScopes(v_userName_1331_);
lean_dec(v_userName_1331_);
v___x_1336_ = 1;
v___x_1337_ = l_Lean_Name_toString(v___x_1335_, v___x_1336_);
v___x_1338_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
v___x_1339_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1334_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
v___x_1340_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_1341_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1339_);
lean_ctor_set(v___x_1341_, 1, v___x_1340_);
v___x_1342_ = l_Lean_Name_toString(v_id_1332_, v___x_1336_);
v___x_1343_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
v___x_1344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1341_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
v___x_1345_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__3));
v___x_1346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1344_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = l_Lean_Name_toString(v_baseId_1333_, v___x_1336_);
v___x_1348_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
v___x_1349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1346_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format(lean_object* v_ctx_1353_, lean_object* v_info_1354_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1355_ = ((lean_object*)(l_Lean_Elab_FieldRedeclInfo_format___closed__1));
v___x_1356_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1353_, v_info_1354_);
v___x_1357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format___boxed(lean_object* v_ctx_1358_, lean_object* v_info_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1358_, v_info_1359_);
lean_dec(v_info_1359_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f(lean_object* v_ppCtx_1363_, lean_object* v_info_1364_){
_start:
{
lean_object* v_mkDocString_x3f_1366_; 
v_mkDocString_x3f_1366_ = lean_ctor_get(v_info_1364_, 2);
lean_inc(v_mkDocString_x3f_1366_);
lean_dec_ref(v_info_1364_);
if (lean_obj_tag(v_mkDocString_x3f_1366_) == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec_ref(v_ppCtx_1363_);
v___x_1367_ = lean_box(0);
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
return v___x_1368_;
}
else
{
lean_object* v_val_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1401_; 
v_val_1369_ = lean_ctor_get(v_mkDocString_x3f_1366_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_mkDocString_x3f_1366_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1371_ = v_mkDocString_x3f_1366_;
v_isShared_1372_ = v_isSharedCheck_1401_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_val_1369_);
lean_dec(v_mkDocString_x3f_1366_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1401_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_apply_2(v_val_1369_, v_ppCtx_1363_, lean_box(0));
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1384_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1376_ = v___x_1373_;
v_isShared_1377_ = v_isSharedCheck_1384_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1373_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1384_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v_a_1374_);
v___x_1379_ = v___x_1371_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1381_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v___x_1379_);
v___x_1381_ = v___x_1376_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1400_; 
v_a_1385_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1387_ = v___x_1373_;
v_isShared_1388_ = v_isSharedCheck_1400_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1373_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1400_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1389_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0));
v___x_1390_ = lean_io_error_to_string(v_a_1385_);
v___x_1391_ = lean_string_append(v___x_1389_, v___x_1390_);
lean_dec_ref(v___x_1390_);
v___x_1392_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1393_ = lean_string_append(v___x_1391_, v___x_1392_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1393_);
v___x_1395_ = v___x_1371_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1397_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set_tag(v___x_1387_, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1395_);
v___x_1397_ = v___x_1387_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___boxed(lean_object* v_ppCtx_1402_, lean_object* v_info_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_ppCtx_1402_, v_info_1403_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(lean_object* v_x_1406_, lean_object* v_x_1407_){
_start:
{
if (lean_obj_tag(v_x_1406_) == 0)
{
lean_object* v___x_1408_; 
v___x_1408_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_1408_;
}
else
{
lean_object* v_val_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1420_; 
v_val_1409_ = lean_ctor_get(v_x_1406_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_x_1406_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1411_ = v_x_1406_;
v_isShared_1412_ = v_isSharedCheck_1420_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_val_1409_);
lean_dec(v_x_1406_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1420_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1413_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_1414_ = l_String_quote(v_val_1409_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set_tag(v___x_1411_, 3);
lean_ctor_set(v___x_1411_, 0, v___x_1414_);
v___x_1416_ = v___x_1411_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1413_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
v___x_1418_ = l_Repr_addAppParen(v___x_1417_, v_x_1407_);
return v___x_1418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(lean_object* v_x_1421_, lean_object* v_x_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_x_1421_, v_x_1422_);
lean_dec(v_x_1422_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object* v_ctx_1438_, lean_object* v_info_1439_){
_start:
{
lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v_toTermInfo_1447_; lean_object* v_location_x3f_1448_; uint8_t v_explicit_1449_; lean_object* v___y_1451_; 
v_toTermInfo_1447_ = lean_ctor_get(v_info_1439_, 0);
lean_inc_ref(v_toTermInfo_1447_);
v_location_x3f_1448_ = lean_ctor_get(v_info_1439_, 1);
lean_inc(v_location_x3f_1448_);
v_explicit_1449_ = lean_ctor_get_uint8(v_info_1439_, sizeof(void*)*3);
if (lean_obj_tag(v_location_x3f_1448_) == 1)
{
lean_object* v_val_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1533_; 
v_val_1472_ = lean_ctor_get(v_location_x3f_1448_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v_location_x3f_1448_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1474_ = v_location_x3f_1448_;
v_isShared_1475_ = v_isSharedCheck_1533_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_val_1472_);
lean_dec(v_location_x3f_1448_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1533_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v_range_1476_; lean_object* v_pos_1477_; lean_object* v_endPos_1478_; lean_object* v_module_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1531_; 
v_range_1476_ = lean_ctor_get(v_val_1472_, 1);
v_pos_1477_ = lean_ctor_get(v_range_1476_, 0);
lean_inc_ref(v_pos_1477_);
v_endPos_1478_ = lean_ctor_get(v_range_1476_, 2);
lean_inc_ref(v_endPos_1478_);
v_module_1479_ = lean_ctor_get(v_val_1472_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_val_1472_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; 
v_unused_1532_ = lean_ctor_get(v_val_1472_, 1);
lean_dec(v_unused_1532_);
v___x_1481_ = v_val_1472_;
v_isShared_1482_ = v_isSharedCheck_1531_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_module_1479_);
lean_dec(v_val_1472_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1531_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v_line_1483_; lean_object* v_column_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1530_; 
v_line_1483_ = lean_ctor_get(v_pos_1477_, 0);
v_column_1484_ = lean_ctor_get(v_pos_1477_, 1);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_pos_1477_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1486_ = v_pos_1477_;
v_isShared_1487_ = v_isSharedCheck_1530_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_column_1484_);
lean_inc(v_line_1483_);
lean_dec(v_pos_1477_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1530_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v_line_1488_; lean_object* v_column_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1529_; 
v_line_1488_ = lean_ctor_get(v_endPos_1478_, 0);
v_column_1489_ = lean_ctor_get(v_endPos_1478_, 1);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_endPos_1478_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1491_ = v_endPos_1478_;
v_isShared_1492_ = v_isSharedCheck_1529_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_column_1489_);
lean_inc(v_line_1488_);
lean_dec(v_endPos_1478_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1529_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
uint8_t v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1493_ = 1;
v___x_1494_ = l_Lean_Name_toString(v_module_1479_, v___x_1493_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set_tag(v___x_1474_, 3);
lean_ctor_set(v___x_1474_, 0, v___x_1494_);
v___x_1496_ = v___x_1474_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1497_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
if (v_isShared_1492_ == 0)
{
lean_ctor_set_tag(v___x_1491_, 5);
lean_ctor_set(v___x_1491_, 1, v___x_1497_);
lean_ctor_set(v___x_1491_, 0, v___x_1496_);
v___x_1499_ = v___x_1491_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1500_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_1501_ = l_Nat_reprFast(v_line_1483_);
v___x_1502_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set_tag(v___x_1486_, 5);
lean_ctor_set(v___x_1486_, 1, v___x_1502_);
lean_ctor_set(v___x_1486_, 0, v___x_1500_);
v___x_1504_ = v___x_1486_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
if (v_isShared_1482_ == 0)
{
lean_ctor_set_tag(v___x_1481_, 5);
lean_ctor_set(v___x_1481_, 1, v___x_1505_);
lean_ctor_set(v___x_1481_, 0, v___x_1504_);
v___x_1507_ = v___x_1481_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1508_ = l_Nat_reprFast(v_column_1484_);
v___x_1509_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
v___x_1510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1507_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
v___x_1511_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v___x_1512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1510_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1499_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_1515_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1513_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
v___x_1516_ = l_Nat_reprFast(v_line_1488_);
v___x_1517_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
v___x_1518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1500_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
v___x_1519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
lean_ctor_set(v___x_1519_, 1, v___x_1505_);
v___x_1520_ = l_Nat_reprFast(v_column_1489_);
v___x_1521_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
v___x_1522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1519_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
v___x_1523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
lean_ctor_set(v___x_1523_, 1, v___x_1511_);
v___x_1524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1515_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___y_1451_ = v___x_1524_;
goto v___jp_1450_;
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
lean_object* v___x_1534_; 
lean_dec(v_location_x3f_1448_);
v___x_1534_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
v___y_1451_ = v___x_1534_;
goto v___jp_1450_;
}
v___jp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_inc_ref(v___y_1443_);
v___x_1444_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___y_1443_);
v___x_1445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___y_1442_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
v___jp_1450_:
{
lean_object* v_lctx_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v_a_1455_; lean_object* v___x_1456_; 
v_lctx_1452_ = lean_ctor_get(v_toTermInfo_1447_, 1);
lean_inc_ref(v_lctx_1452_);
v___x_1453_ = l_Lean_Elab_ContextInfo_toPPContext(v_ctx_1438_, v_lctx_1452_);
v___x_1454_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v___x_1453_, v_info_1439_);
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref(v___x_1454_);
v___x_1456_ = l_Lean_Elab_TermInfo_format(v_ctx_1438_, v_toTermInfo_1447_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 1);
v___x_1458_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__1));
v___x_1459_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
lean_ctor_set(v___x_1459_, 1, v_a_1457_);
v___x_1460_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__3));
v___x_1461_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1459_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
lean_ctor_set(v___x_1462_, 1, v___y_1451_);
v___x_1463_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__5));
v___x_1464_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1462_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v___x_1465_ = lean_unsigned_to_nat(0u);
v___x_1466_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_a_1455_, v___x_1465_);
v___x_1467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1464_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__7));
v___x_1469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1467_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
if (v_explicit_1449_ == 0)
{
lean_object* v___x_1470_; 
v___x_1470_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__8));
v___y_1442_ = v___x_1469_;
v___y_1443_ = v___x_1470_;
goto v___jp_1441_;
}
else
{
lean_object* v___x_1471_; 
v___x_1471_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__9));
v___y_1442_ = v___x_1469_;
v___y_1443_ = v___x_1471_;
goto v___jp_1441_;
}
}
else
{
lean_dec(v_a_1455_);
lean_dec(v___y_1451_);
return v___x_1456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object* v_ctx_1535_, lean_object* v_info_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1535_, v_info_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object* v_ctx_1542_, lean_object* v_info_1543_){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1544_ = ((lean_object*)(l_Lean_Elab_ChoiceInfo_format___closed__1));
v___x_1545_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1542_, v_info_1543_);
v___x_1546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object* v_ctx_1550_, lean_object* v_info_1551_){
_start:
{
lean_object* v_stx_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_stx_1552_ = lean_ctor_get(v_info_1551_, 1);
v___x_1553_ = ((lean_object*)(l_Lean_Elab_DocInfo_format___closed__1));
lean_inc(v_stx_1552_);
v___x_1554_ = l_Lean_Syntax_getKind(v_stx_1552_);
v___x_1555_ = 1;
v___x_1556_ = l_Lean_Name_toString(v___x_1554_, v___x_1555_);
v___x_1557_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
v___x_1558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1553_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1558_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1550_, v_info_1551_);
v___x_1562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1560_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object* v_ctx_1572_, lean_object* v_info_1573_){
_start:
{
lean_object* v_toElabInfo_1574_; lean_object* v_name_1575_; uint8_t v_kind_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_toElabInfo_1574_ = lean_ctor_get(v_info_1573_, 0);
lean_inc_ref(v_toElabInfo_1574_);
v_name_1575_ = lean_ctor_get(v_info_1573_, 1);
lean_inc(v_name_1575_);
v_kind_1576_ = lean_ctor_get_uint8(v_info_1573_, sizeof(void*)*2);
lean_dec_ref(v_info_1573_);
v___x_1577_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__1));
v___x_1578_ = 1;
v___x_1579_ = l_Lean_Name_toString(v_name_1575_, v___x_1578_);
v___x_1580_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
v___x_1581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1577_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__3));
v___x_1583_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1581_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = lean_unsigned_to_nat(0u);
v___x_1585_ = l_Lean_Elab_instReprDocElabKind_repr(v_kind_1576_, v___x_1584_);
v___x_1586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1583_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__5));
v___x_1588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1572_, v_toElabInfo_1574_);
v___x_1590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object* v_ctx_1591_, lean_object* v_x_1592_){
_start:
{
switch(lean_obj_tag(v_x_1592_))
{
case 0:
{
lean_object* v_i_1594_; lean_object* v___x_1595_; 
v_i_1594_ = lean_ctor_get(v_x_1592_, 0);
lean_inc_ref(v_i_1594_);
lean_dec_ref_known(v_x_1592_, 1);
v___x_1595_ = l_Lean_Elab_TacticInfo_format(v_ctx_1591_, v_i_1594_);
return v___x_1595_;
}
case 1:
{
lean_object* v_i_1596_; lean_object* v___x_1597_; 
v_i_1596_ = lean_ctor_get(v_x_1592_, 0);
lean_inc_ref(v_i_1596_);
lean_dec_ref_known(v_x_1592_, 1);
v___x_1597_ = l_Lean_Elab_TermInfo_format(v_ctx_1591_, v_i_1596_);
return v___x_1597_;
}
case 2:
{
lean_object* v_i_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1606_; 
v_i_1598_ = lean_ctor_get(v_x_1592_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_x_1592_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1600_ = v_x_1592_;
v_isShared_1601_ = v_isSharedCheck_1606_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_i_1598_);
lean_dec(v_x_1592_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1606_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1602_ = l_Lean_Elab_PartialTermInfo_format(v_ctx_1591_, v_i_1598_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1602_);
v___x_1604_ = v___x_1600_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
case 3:
{
lean_object* v_i_1607_; lean_object* v___x_1608_; 
v_i_1607_ = lean_ctor_get(v_x_1592_, 0);
lean_inc_ref(v_i_1607_);
lean_dec_ref_known(v_x_1592_, 1);
v___x_1608_ = l_Lean_Elab_CommandInfo_format(v_ctx_1591_, v_i_1607_);
return v___x_1608_;
}
case 4:
{
lean_object* v_i_1609_; lean_object* v___x_1610_; 
v_i_1609_ = lean_ctor_get(v_x_1592_, 0);
lean_inc_ref(v_i_1609_);
lean_dec_ref_known(v_x_1592_, 1);
v___x_1610_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1591_, v_i_1609_);
lean_dec_ref(v_ctx_1591_);
return v___x_1610_;
}
case 5:
{
lean_object* v_i_1611_; lean_object* v___x_1612_; 
v_i_1611_ = lean_ctor_get(v_x_1592_, 0);
lean_inc_ref(v_i_1611_);
lean_dec_ref_known(v_x_1592_, 1);
v___x_1612_ = l_Lean_Elab_OptionInfo_format(v_ctx_1591_, v_i_1611_);
return v___x_1612_;
}
case 6:
{
lean_object* v_i_1613_; lean_object* v___x_1614_; 
v_i_1613_ = lean_ctor_get(v_x_1592_, 0);
lean_inc_ref(v_i_1613_);
lean_dec_ref_known(v_x_1592_, 1);
v___x_1614_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_1591_, v_i_1613_);
return v___x_1614_;
}
case 7:
{
lean_object* v_i_1615_; lean_object* v___x_1616_; 
v_i_1615_ = lean_ctor_get(v_x_1592_, 0);
lean_inc_ref(v_i_1615_);
lean_dec_ref_known(v_x_1592_, 1);
v___x_1616_ = l_Lean_Elab_FieldInfo_format(v_ctx_1591_, v_i_1615_);
return v___x_1616_;
}
case 8:
{
lean_object* v_i_1617_; lean_object* v___x_1618_; 
v_i_1617_ = lean_ctor_get(v_x_1592_, 0);
lean_inc_ref(v_i_1617_);
lean_dec_ref_known(v_x_1592_, 1);
v___x_1618_ = l_Lean_Elab_CompletionInfo_format(v_ctx_1591_, v_i_1617_);
return v___x_1618_;
}
case 9:
{
lean_object* v_i_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1627_; 
lean_dec_ref(v_ctx_1591_);
v_i_1619_ = lean_ctor_get(v_x_1592_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_x_1592_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1621_ = v_x_1592_;
v_isShared_1622_ = v_isSharedCheck_1627_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_i_1619_);
lean_dec(v_x_1592_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1627_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1625_; 
v___x_1623_ = l_Lean_Elab_UserWidgetInfo_format(v_i_1619_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set_tag(v___x_1621_, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1623_);
v___x_1625_ = v___x_1621_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
case 10:
{
lean_object* v_i_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1636_; 
lean_dec_ref(v_ctx_1591_);
v_i_1628_ = lean_ctor_get(v_x_1592_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v_x_1592_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1630_ = v_x_1592_;
v_isShared_1631_ = v_isSharedCheck_1636_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_i_1628_);
lean_dec(v_x_1592_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1636_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1632_ = l_Lean_Elab_CustomInfo_format(v_i_1628_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set_tag(v___x_1630_, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1632_);
v___x_1634_ = v___x_1630_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1632_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
case 11:
{
lean_object* v_i_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1645_; 
lean_dec_ref(v_ctx_1591_);
v_i_1637_ = lean_ctor_get(v_x_1592_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_x_1592_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1639_ = v_x_1592_;
v_isShared_1640_ = v_isSharedCheck_1645_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_i_1637_);
lean_dec(v_x_1592_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1645_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1641_ = l_Lean_Elab_FVarAliasInfo_format(v_i_1637_);
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
case 12:
{
lean_object* v_i_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1654_; 
v_i_1646_ = lean_ctor_get(v_x_1592_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_x_1592_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1648_ = v_x_1592_;
v_isShared_1649_ = v_isSharedCheck_1654_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_i_1646_);
lean_dec(v_x_1592_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1654_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1591_, v_i_1646_);
lean_dec(v_i_1646_);
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
case 13:
{
lean_object* v_i_1655_; lean_object* v___x_1656_; 
v_i_1655_ = lean_ctor_get(v_x_1592_, 0);
lean_inc_ref(v_i_1655_);
lean_dec_ref_known(v_x_1592_, 1);
v___x_1656_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1591_, v_i_1655_);
return v___x_1656_;
}
case 14:
{
lean_object* v_i_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1665_; 
v_i_1657_ = lean_ctor_get(v_x_1592_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_x_1592_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1659_ = v_x_1592_;
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_i_1657_);
lean_dec(v_x_1592_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = l_Lean_Elab_ChoiceInfo_format(v_ctx_1591_, v_i_1657_);
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
case 15:
{
lean_object* v_i_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1674_; 
v_i_1666_ = lean_ctor_get(v_x_1592_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_x_1592_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1668_ = v_x_1592_;
v_isShared_1669_ = v_isSharedCheck_1674_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_i_1666_);
lean_dec(v_x_1592_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1674_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1670_ = l_Lean_Elab_DocInfo_format(v_ctx_1591_, v_i_1666_);
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
default: 
{
lean_object* v_i_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1683_; 
v_i_1675_ = lean_ctor_get(v_x_1592_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_x_1592_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1677_ = v_x_1592_;
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_i_1675_);
lean_dec(v_x_1592_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = l_Lean_Elab_DocElabInfo_format(v_ctx_1591_, v_i_1675_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object* v_ctx_1684_, lean_object* v_x_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_Elab_Info_format(v_ctx_1684_, v_x_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object* v_x_1688_, lean_object* v_x_1689_){
_start:
{
if (lean_obj_tag(v_x_1689_) == 0)
{
return v_x_1688_;
}
else
{
lean_object* v_head_1690_; lean_object* v_tail_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v_head_1690_ = lean_ctor_get(v_x_1689_, 0);
v_tail_1691_ = lean_ctor_get(v_x_1689_, 1);
v___x_1692_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2));
v___x_1693_ = lean_string_append(v_x_1688_, v___x_1692_);
v___x_1694_ = lean_expr_dbg_to_string(v_head_1690_);
v___x_1695_ = lean_string_append(v___x_1693_, v___x_1694_);
lean_dec_ref(v___x_1694_);
v_x_1688_ = v___x_1695_;
v_x_1689_ = v_tail_1691_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object* v_x_1697_, lean_object* v_x_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v_x_1697_, v_x_1698_);
lean_dec(v_x_1698_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object* v_x_1702_){
_start:
{
if (lean_obj_tag(v_x_1702_) == 0)
{
lean_object* v___x_1703_; 
v___x_1703_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0));
return v___x_1703_;
}
else
{
lean_object* v_tail_1704_; 
v_tail_1704_ = lean_ctor_get(v_x_1702_, 1);
if (lean_obj_tag(v_tail_1704_) == 0)
{
lean_object* v_head_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v_head_1705_ = lean_ctor_get(v_x_1702_, 0);
v___x_1706_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1707_ = lean_expr_dbg_to_string(v_head_1705_);
v___x_1708_ = lean_string_append(v___x_1706_, v___x_1707_);
lean_dec_ref(v___x_1707_);
v___x_1709_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1710_ = lean_string_append(v___x_1708_, v___x_1709_);
return v___x_1710_;
}
else
{
lean_object* v_head_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; uint32_t v___x_1716_; lean_object* v___x_1717_; 
v_head_1711_ = lean_ctor_get(v_x_1702_, 0);
v___x_1712_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1713_ = lean_expr_dbg_to_string(v_head_1711_);
v___x_1714_ = lean_string_append(v___x_1712_, v___x_1713_);
lean_dec_ref(v___x_1713_);
v___x_1715_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v___x_1714_, v_tail_1704_);
v___x_1716_ = 93;
v___x_1717_ = lean_string_push(v___x_1715_, v___x_1716_);
return v___x_1717_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object* v_x_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v_x_1718_);
lean_dec(v_x_1718_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object* v_ctx_1726_){
_start:
{
switch(lean_obj_tag(v_ctx_1726_))
{
case 0:
{
lean_object* v___x_1727_; 
lean_dec_ref_known(v_ctx_1726_, 1);
v___x_1727_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__1));
return v___x_1727_;
}
case 1:
{
lean_object* v_parentDecl_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1741_; 
v_parentDecl_1728_ = lean_ctor_get(v_ctx_1726_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_ctx_1726_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1730_ = v_ctx_1726_;
v_isShared_1731_ = v_isSharedCheck_1741_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_parentDecl_1728_);
lean_dec(v_ctx_1726_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1741_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; uint8_t v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1732_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__2));
v___x_1733_ = 1;
v___x_1734_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_parentDecl_1728_, v___x_1733_);
v___x_1735_ = lean_string_append(v___x_1732_, v___x_1734_);
lean_dec_ref(v___x_1734_);
v___x_1736_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1737_ = lean_string_append(v___x_1735_, v___x_1736_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set_tag(v___x_1730_, 3);
lean_ctor_set(v___x_1730_, 0, v___x_1737_);
v___x_1739_ = v___x_1730_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
default: 
{
lean_object* v_autoImplicits_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1757_; 
v_autoImplicits_1742_ = lean_ctor_get(v_ctx_1726_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_ctx_1726_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1744_ = v_ctx_1726_;
v_isShared_1745_ = v_isSharedCheck_1757_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_autoImplicits_1742_);
lean_dec(v_ctx_1726_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1757_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1746_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__3));
v___x_1747_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__4));
v___x_1748_ = lean_array_to_list(v_autoImplicits_1742_);
v___x_1749_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v___x_1748_);
lean_dec(v___x_1748_);
v___x_1750_ = lean_string_append(v___x_1747_, v___x_1749_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = lean_string_append(v___x_1746_, v___x_1750_);
lean_dec_ref(v___x_1750_);
v___x_1752_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1753_ = lean_string_append(v___x_1751_, v___x_1752_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set_tag(v___x_1744_, 3);
lean_ctor_set(v___x_1744_, 0, v___x_1753_);
v___x_1755_ = v___x_1744_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(3, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format(lean_object* v_tree_1767_, lean_object* v_ctx_x3f_1768_){
_start:
{
switch(lean_obj_tag(v_tree_1767_))
{
case 0:
{
lean_object* v_i_1770_; lean_object* v_t_1771_; lean_object* v___x_1772_; 
v_i_1770_ = lean_ctor_get(v_tree_1767_, 0);
lean_inc_ref(v_i_1770_);
v_t_1771_ = lean_ctor_get(v_tree_1767_, 1);
lean_inc_ref(v_t_1771_);
lean_dec_ref_known(v_tree_1767_, 2);
v___x_1772_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1770_, v_ctx_x3f_1768_);
v_tree_1767_ = v_t_1771_;
v_ctx_x3f_1768_ = v___x_1772_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_ctx_x3f_1768_) == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_dec_ref_known(v_tree_1767_, 2);
v___x_1774_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__1));
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
return v___x_1775_;
}
else
{
lean_object* v_i_1776_; lean_object* v_children_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1827_; 
v_i_1776_ = lean_ctor_get(v_tree_1767_, 0);
v_children_1777_ = lean_ctor_get(v_tree_1767_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_tree_1767_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1779_ = v_tree_1767_;
v_isShared_1780_ = v_isSharedCheck_1827_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_children_1777_);
lean_inc(v_i_1776_);
lean_dec(v_tree_1767_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1827_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v_val_1781_; lean_object* v___x_1782_; 
v_val_1781_ = lean_ctor_get(v_ctx_x3f_1768_, 0);
lean_inc_ref(v_i_1776_);
lean_inc(v_val_1781_);
v___x_1782_ = l_Lean_Elab_Info_format(v_val_1781_, v_i_1776_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1826_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1826_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1826_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v_size_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v_size_1787_ = lean_ctor_get(v_children_1777_, 2);
v___x_1788_ = lean_unsigned_to_nat(0u);
v___x_1789_ = lean_nat_dec_eq(v_size_1787_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_del_object(v___x_1785_);
v___x_1790_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_1768_, v_i_1776_);
lean_dec_ref(v_i_1776_);
v___x_1791_ = l_Lean_PersistentArray_toList___redArg(v_children_1777_);
lean_dec_ref(v_children_1777_);
v___x_1792_ = lean_box(0);
v___x_1793_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1790_, v___x_1791_, v___x_1792_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1809_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1796_ = v___x_1793_;
v_isShared_1797_ = v_isSharedCheck_1809_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1793_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1809_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1798_; lean_object* v___x_1800_; 
v___x_1798_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1780_ == 0)
{
lean_ctor_set_tag(v___x_1779_, 5);
lean_ctor_set(v___x_1779_, 1, v_a_1783_);
lean_ctor_set(v___x_1779_, 0, v___x_1798_);
v___x_1800_ = v___x_1779_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1798_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_a_1783_);
v___x_1800_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1801_ = lean_box(1);
v___x_1802_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1801_, v_a_1794_);
v___x_1803_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1800_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = l_Std_Format_nestD(v___x_1803_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v___x_1804_);
v___x_1806_ = v___x_1796_;
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
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
lean_dec(v_a_1783_);
lean_del_object(v___x_1779_);
v_a_1810_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1793_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1793_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1820_; 
lean_dec_ref(v_children_1777_);
lean_dec_ref_known(v_ctx_x3f_1768_, 1);
lean_dec_ref(v_i_1776_);
v___x_1818_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1780_ == 0)
{
lean_ctor_set_tag(v___x_1779_, 5);
lean_ctor_set(v___x_1779_, 1, v_a_1783_);
lean_ctor_set(v___x_1779_, 0, v___x_1818_);
v___x_1820_ = v___x_1779_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v_a_1783_);
v___x_1820_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1821_ = l_Std_Format_nestD(v___x_1820_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1821_);
v___x_1823_ = v___x_1785_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
}
else
{
lean_del_object(v___x_1779_);
lean_dec_ref(v_children_1777_);
lean_dec_ref_known(v_ctx_x3f_1768_, 1);
lean_dec_ref(v_i_1776_);
return v___x_1782_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1841_; 
lean_dec(v_ctx_x3f_1768_);
v_mvarId_1828_ = lean_ctor_get(v_tree_1767_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v_tree_1767_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1830_ = v_tree_1767_;
v_isShared_1831_ = v_isSharedCheck_1841_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_mvarId_1828_);
lean_dec(v_tree_1767_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1841_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1832_; uint8_t v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1836_; 
v___x_1832_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__5));
v___x_1833_ = 1;
v___x_1834_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_1828_, v___x_1833_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set_tag(v___x_1830_, 3);
lean_ctor_set(v___x_1830_, 0, v___x_1834_);
v___x_1836_ = v___x_1830_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1832_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = l_Std_Format_nestD(v___x_1837_);
v___x_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
return v___x_1839_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object* v___x_1842_, lean_object* v_x_1843_, lean_object* v_x_1844_){
_start:
{
if (lean_obj_tag(v_x_1843_) == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
lean_dec(v___x_1842_);
v___x_1846_ = l_List_reverse___redArg(v_x_1844_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
return v___x_1847_;
}
else
{
lean_object* v_head_1848_; lean_object* v_tail_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1867_; 
v_head_1848_ = lean_ctor_get(v_x_1843_, 0);
v_tail_1849_ = lean_ctor_get(v_x_1843_, 1);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_x_1843_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1851_ = v_x_1843_;
v_isShared_1852_ = v_isSharedCheck_1867_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_tail_1849_);
lean_inc(v_head_1848_);
lean_dec(v_x_1843_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1867_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; 
lean_inc(v___x_1842_);
v___x_1853_ = l_Lean_Elab_InfoTree_format(v_head_1848_, v___x_1842_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1856_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref_known(v___x_1853_, 1);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 1, v_x_1844_);
lean_ctor_set(v___x_1851_, 0, v_a_1854_);
v___x_1856_ = v___x_1851_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1854_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_x_1844_);
v___x_1856_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
v_x_1843_ = v_tail_1849_;
v_x_1844_ = v___x_1856_;
goto _start;
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_del_object(v___x_1851_);
lean_dec(v_tail_1849_);
lean_dec(v_x_1844_);
lean_dec(v___x_1842_);
v_a_1859_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1853_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1853_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object* v___x_1868_, lean_object* v_x_1869_, lean_object* v_x_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1868_, v_x_1869_, v_x_1870_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object* v_tree_1873_, lean_object* v_ctx_x3f_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_Elab_InfoTree_format(v_tree_1873_, v_ctx_x3f_1874_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object* v_f_1877_, lean_object* v_s_1878_){
_start:
{
uint8_t v_enabled_1879_; lean_object* v_assignment_1880_; lean_object* v_lazyAssignment_1881_; lean_object* v_trees_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1890_; 
v_enabled_1879_ = lean_ctor_get_uint8(v_s_1878_, sizeof(void*)*3);
v_assignment_1880_ = lean_ctor_get(v_s_1878_, 0);
v_lazyAssignment_1881_ = lean_ctor_get(v_s_1878_, 1);
v_trees_1882_ = lean_ctor_get(v_s_1878_, 2);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_s_1878_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1884_ = v_s_1878_;
v_isShared_1885_ = v_isSharedCheck_1890_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_trees_1882_);
lean_inc(v_lazyAssignment_1881_);
lean_inc(v_assignment_1880_);
lean_dec(v_s_1878_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1890_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1886_ = lean_apply_1(v_f_1877_, v_trees_1882_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 2, v___x_1886_);
v___x_1888_ = v___x_1884_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_assignment_1880_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_lazyAssignment_1881_);
lean_ctor_set(v_reuseFailAlloc_1889_, 2, v___x_1886_);
lean_ctor_set_uint8(v_reuseFailAlloc_1889_, sizeof(void*)*3, v_enabled_1879_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object* v_inst_1891_, lean_object* v_f_1892_){
_start:
{
lean_object* v_modifyInfoState_1893_; lean_object* v___f_1894_; lean_object* v___x_1895_; 
v_modifyInfoState_1893_ = lean_ctor_get(v_inst_1891_, 1);
lean_inc(v_modifyInfoState_1893_);
lean_dec_ref(v_inst_1891_);
v___f_1894_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1894_, 0, v_f_1892_);
v___x_1895_ = lean_apply_1(v_modifyInfoState_1893_, v___f_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object* v_m_1896_, lean_object* v_inst_1897_, lean_object* v_f_1898_){
_start:
{
lean_object* v_modifyInfoState_1899_; lean_object* v___f_1900_; lean_object* v___x_1901_; 
v_modifyInfoState_1899_ = lean_ctor_get(v_inst_1897_, 1);
lean_inc(v_modifyInfoState_1899_);
lean_dec_ref(v_inst_1897_);
v___f_1900_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1900_, 0, v_f_1898_);
v___x_1901_ = lean_apply_1(v_modifyInfoState_1899_, v___f_1900_);
return v___x_1901_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = lean_unsigned_to_nat(32u);
v___x_1903_ = lean_mk_empty_array_with_capacity(v___x_1902_);
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
return v___x_1904_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1905_ = ((size_t)5ULL);
v___x_1906_ = lean_unsigned_to_nat(0u);
v___x_1907_ = lean_unsigned_to_nat(32u);
v___x_1908_ = lean_mk_empty_array_with_capacity(v___x_1907_);
v___x_1909_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0);
v___x_1910_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
lean_ctor_set(v___x_1910_, 1, v___x_1908_);
lean_ctor_set(v___x_1910_, 2, v___x_1906_);
lean_ctor_set(v___x_1910_, 3, v___x_1906_);
lean_ctor_set_usize(v___x_1910_, 4, v___x_1905_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object* v_s_1911_){
_start:
{
uint8_t v_enabled_1912_; lean_object* v_assignment_1913_; lean_object* v_lazyAssignment_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1922_; 
v_enabled_1912_ = lean_ctor_get_uint8(v_s_1911_, sizeof(void*)*3);
v_assignment_1913_ = lean_ctor_get(v_s_1911_, 0);
v_lazyAssignment_1914_ = lean_ctor_get(v_s_1911_, 1);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_s_1911_);
if (v_isSharedCheck_1922_ == 0)
{
lean_object* v_unused_1923_; 
v_unused_1923_ = lean_ctor_get(v_s_1911_, 2);
lean_dec(v_unused_1923_);
v___x_1916_ = v_s_1911_;
v_isShared_1917_ = v_isSharedCheck_1922_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_lazyAssignment_1914_);
lean_inc(v_assignment_1913_);
lean_dec(v_s_1911_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1922_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1918_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 2, v___x_1918_);
v___x_1920_ = v___x_1916_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_assignment_1913_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_lazyAssignment_1914_);
lean_ctor_set(v_reuseFailAlloc_1921_, 2, v___x_1918_);
lean_ctor_set_uint8(v_reuseFailAlloc_1921_, sizeof(void*)*3, v_enabled_1912_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object* v_toPure_1924_, lean_object* v_trees_1925_, lean_object* v_____r_1926_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_apply_2(v_toPure_1924_, lean_box(0), v_trees_1925_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object* v_toPure_1928_, lean_object* v_modifyInfoState_1929_, lean_object* v___f_1930_, lean_object* v_toBind_1931_, lean_object* v_____do__lift_1932_){
_start:
{
lean_object* v_trees_1933_; lean_object* v___f_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v_trees_1933_ = lean_ctor_get(v_____do__lift_1932_, 2);
lean_inc_ref(v_trees_1933_);
lean_dec_ref(v_____do__lift_1932_);
v___f_1934_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1934_, 0, v_toPure_1928_);
lean_closure_set(v___f_1934_, 1, v_trees_1933_);
v___x_1935_ = lean_apply_1(v_modifyInfoState_1929_, v___f_1930_);
v___x_1936_ = lean_apply_4(v_toBind_1931_, lean_box(0), lean_box(0), v___x_1935_, v___f_1934_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object* v_inst_1938_, lean_object* v_inst_1939_){
_start:
{
lean_object* v_toApplicative_1940_; lean_object* v_toBind_1941_; lean_object* v_getInfoState_1942_; lean_object* v_modifyInfoState_1943_; lean_object* v_toPure_1944_; lean_object* v___f_1945_; lean_object* v___f_1946_; lean_object* v___x_1947_; 
v_toApplicative_1940_ = lean_ctor_get(v_inst_1938_, 0);
lean_inc_ref(v_toApplicative_1940_);
v_toBind_1941_ = lean_ctor_get(v_inst_1938_, 1);
lean_inc_n(v_toBind_1941_, 2);
lean_dec_ref(v_inst_1938_);
v_getInfoState_1942_ = lean_ctor_get(v_inst_1939_, 0);
lean_inc(v_getInfoState_1942_);
v_modifyInfoState_1943_ = lean_ctor_get(v_inst_1939_, 1);
lean_inc(v_modifyInfoState_1943_);
lean_dec_ref(v_inst_1939_);
v_toPure_1944_ = lean_ctor_get(v_toApplicative_1940_, 1);
lean_inc(v_toPure_1944_);
lean_dec_ref(v_toApplicative_1940_);
v___f_1945_ = ((lean_object*)(l_Lean_Elab_getResetInfoTrees___redArg___closed__0));
v___f_1946_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1946_, 0, v_toPure_1944_);
lean_closure_set(v___f_1946_, 1, v_modifyInfoState_1943_);
lean_closure_set(v___f_1946_, 2, v___f_1945_);
lean_closure_set(v___f_1946_, 3, v_toBind_1941_);
v___x_1947_ = lean_apply_4(v_toBind_1941_, lean_box(0), lean_box(0), v_getInfoState_1942_, v___f_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object* v_m_1948_, lean_object* v_inst_1949_, lean_object* v_inst_1950_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_1949_, v_inst_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object* v_t_1952_, lean_object* v_s_1953_){
_start:
{
uint8_t v_enabled_1954_; lean_object* v_assignment_1955_; lean_object* v_lazyAssignment_1956_; lean_object* v_trees_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1965_; 
v_enabled_1954_ = lean_ctor_get_uint8(v_s_1953_, sizeof(void*)*3);
v_assignment_1955_ = lean_ctor_get(v_s_1953_, 0);
v_lazyAssignment_1956_ = lean_ctor_get(v_s_1953_, 1);
v_trees_1957_ = lean_ctor_get(v_s_1953_, 2);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_s_1953_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1959_ = v_s_1953_;
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_trees_1957_);
lean_inc(v_lazyAssignment_1956_);
lean_inc(v_assignment_1955_);
lean_dec(v_s_1953_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1961_ = l_Lean_PersistentArray_push___redArg(v_trees_1957_, v_t_1952_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 2, v___x_1961_);
v___x_1963_ = v___x_1959_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_assignment_1955_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_lazyAssignment_1956_);
lean_ctor_set(v_reuseFailAlloc_1964_, 2, v___x_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_1964_, sizeof(void*)*3, v_enabled_1954_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object* v_toApplicative_1966_, lean_object* v_modifyInfoState_1967_, lean_object* v___f_1968_, lean_object* v_____do__lift_1969_){
_start:
{
uint8_t v_enabled_1970_; 
v_enabled_1970_ = lean_ctor_get_uint8(v_____do__lift_1969_, sizeof(void*)*3);
if (v_enabled_1970_ == 0)
{
lean_object* v_toPure_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_dec_ref(v___f_1968_);
lean_dec(v_modifyInfoState_1967_);
v_toPure_1971_ = lean_ctor_get(v_toApplicative_1966_, 1);
lean_inc(v_toPure_1971_);
lean_dec_ref(v_toApplicative_1966_);
v___x_1972_ = lean_box(0);
v___x_1973_ = lean_apply_2(v_toPure_1971_, lean_box(0), v___x_1972_);
return v___x_1973_;
}
else
{
lean_object* v___x_1974_; 
lean_dec_ref(v_toApplicative_1966_);
v___x_1974_ = lean_apply_1(v_modifyInfoState_1967_, v___f_1968_);
return v___x_1974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object* v_toApplicative_1975_, lean_object* v_modifyInfoState_1976_, lean_object* v___f_1977_, lean_object* v_____do__lift_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_Elab_pushInfoTree___redArg___lam__1(v_toApplicative_1975_, v_modifyInfoState_1976_, v___f_1977_, v_____do__lift_1978_);
lean_dec_ref(v_____do__lift_1978_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object* v_inst_1980_, lean_object* v_inst_1981_, lean_object* v_t_1982_){
_start:
{
lean_object* v_toApplicative_1983_; lean_object* v_toBind_1984_; lean_object* v_getInfoState_1985_; lean_object* v_modifyInfoState_1986_; lean_object* v___f_1987_; lean_object* v___f_1988_; lean_object* v___x_1989_; 
v_toApplicative_1983_ = lean_ctor_get(v_inst_1980_, 0);
lean_inc_ref(v_toApplicative_1983_);
v_toBind_1984_ = lean_ctor_get(v_inst_1980_, 1);
lean_inc(v_toBind_1984_);
lean_dec_ref(v_inst_1980_);
v_getInfoState_1985_ = lean_ctor_get(v_inst_1981_, 0);
lean_inc(v_getInfoState_1985_);
v_modifyInfoState_1986_ = lean_ctor_get(v_inst_1981_, 1);
lean_inc(v_modifyInfoState_1986_);
lean_dec_ref(v_inst_1981_);
v___f_1987_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1987_, 0, v_t_1982_);
v___f_1988_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1988_, 0, v_toApplicative_1983_);
lean_closure_set(v___f_1988_, 1, v_modifyInfoState_1986_);
lean_closure_set(v___f_1988_, 2, v___f_1987_);
v___x_1989_ = lean_apply_4(v_toBind_1984_, lean_box(0), lean_box(0), v_getInfoState_1985_, v___f_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object* v_m_1990_, lean_object* v_inst_1991_, lean_object* v_inst_1992_, lean_object* v_t_1993_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_1991_, v_inst_1992_, v_t_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object* v_toApplicative_1995_, lean_object* v_t_1996_, lean_object* v_inst_1997_, lean_object* v_inst_1998_, lean_object* v_____do__lift_1999_){
_start:
{
uint8_t v_enabled_2000_; 
v_enabled_2000_ = lean_ctor_get_uint8(v_____do__lift_1999_, sizeof(void*)*3);
if (v_enabled_2000_ == 0)
{
lean_object* v_toPure_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
lean_dec_ref(v_inst_1998_);
lean_dec_ref(v_inst_1997_);
lean_dec_ref(v_t_1996_);
v_toPure_2001_ = lean_ctor_get(v_toApplicative_1995_, 1);
lean_inc(v_toPure_2001_);
lean_dec_ref(v_toApplicative_1995_);
v___x_2002_ = lean_box(0);
v___x_2003_ = lean_apply_2(v_toPure_2001_, lean_box(0), v___x_2002_);
return v___x_2003_;
}
else
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_dec_ref(v_toApplicative_1995_);
v___x_2004_ = lean_unsigned_to_nat(32u);
v___x_2005_ = lean_mk_empty_array_with_capacity(v___x_2004_);
lean_dec_ref(v___x_2005_);
v___x_2006_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2007_, 0, v_t_1996_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v___x_2008_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_1997_, v_inst_1998_, v___x_2007_);
return v___x_2008_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object* v_toApplicative_2009_, lean_object* v_t_2010_, lean_object* v_inst_2011_, lean_object* v_inst_2012_, lean_object* v_____do__lift_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_Elab_pushInfoLeaf___redArg___lam__0(v_toApplicative_2009_, v_t_2010_, v_inst_2011_, v_inst_2012_, v_____do__lift_2013_);
lean_dec_ref(v_____do__lift_2013_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v_t_2017_){
_start:
{
lean_object* v_toApplicative_2018_; lean_object* v_toBind_2019_; lean_object* v_getInfoState_2020_; lean_object* v___f_2021_; lean_object* v___x_2022_; 
v_toApplicative_2018_ = lean_ctor_get(v_inst_2015_, 0);
lean_inc_ref(v_toApplicative_2018_);
v_toBind_2019_ = lean_ctor_get(v_inst_2015_, 1);
lean_inc(v_toBind_2019_);
v_getInfoState_2020_ = lean_ctor_get(v_inst_2016_, 0);
lean_inc(v_getInfoState_2020_);
v___f_2021_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2021_, 0, v_toApplicative_2018_);
lean_closure_set(v___f_2021_, 1, v_t_2017_);
lean_closure_set(v___f_2021_, 2, v_inst_2015_);
lean_closure_set(v___f_2021_, 3, v_inst_2016_);
v___x_2022_ = lean_apply_4(v_toBind_2019_, lean_box(0), lean_box(0), v_getInfoState_2020_, v___f_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object* v_m_2023_, lean_object* v_inst_2024_, lean_object* v_inst_2025_, lean_object* v_t_2026_){
_start:
{
lean_object* v___x_2027_; 
v___x_2027_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2024_, v_inst_2025_, v_t_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object* v_inst_2028_, lean_object* v_inst_2029_, lean_object* v_info_2030_){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2031_, 0, v_info_2030_);
v___x_2032_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2028_, v_inst_2029_, v___x_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object* v_m_2033_, lean_object* v_inst_2034_, lean_object* v_inst_2035_, lean_object* v_info_2036_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_2034_, v_inst_2035_, v_info_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object* v_stx_2038_, lean_object* v_expectedType_x3f_2039_, lean_object* v_inst_2040_, lean_object* v_inst_2041_, lean_object* v_____do__lift_2042_){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2043_ = lean_box(0);
v___x_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
lean_ctor_set(v___x_2044_, 1, v_stx_2038_);
v___x_2045_ = l_Lean_LocalContext_empty;
v___x_2046_ = 0;
v___x_2047_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2047_, 0, v___x_2044_);
lean_ctor_set(v___x_2047_, 1, v___x_2045_);
lean_ctor_set(v___x_2047_, 2, v_expectedType_x3f_2039_);
lean_ctor_set(v___x_2047_, 3, v_____do__lift_2042_);
lean_ctor_set_uint8(v___x_2047_, sizeof(void*)*4, v___x_2046_);
lean_ctor_set_uint8(v___x_2047_, sizeof(void*)*4 + 1, v___x_2046_);
v___x_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
v___x_2049_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2040_, v_inst_2041_, v___x_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object* v_inst_2050_, lean_object* v_inst_2051_, lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_stx_2054_, lean_object* v_n_2055_, lean_object* v_expectedType_x3f_2056_){
_start:
{
lean_object* v_toBind_2057_; lean_object* v___f_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v_toBind_2057_ = lean_ctor_get(v_inst_2050_, 1);
lean_inc(v_toBind_2057_);
lean_inc_ref(v_inst_2050_);
v___f_2058_ = lean_alloc_closure((void*)(l_Lean_Elab_addConstInfo___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2058_, 0, v_stx_2054_);
lean_closure_set(v___f_2058_, 1, v_expectedType_x3f_2056_);
lean_closure_set(v___f_2058_, 2, v_inst_2050_);
lean_closure_set(v___f_2058_, 3, v_inst_2051_);
v___x_2059_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_2050_, v_inst_2052_, v_inst_2053_, v_n_2055_);
v___x_2060_ = lean_apply_4(v_toBind_2057_, lean_box(0), lean_box(0), v___x_2059_, v___f_2058_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object* v_m_2061_, lean_object* v_inst_2062_, lean_object* v_inst_2063_, lean_object* v_inst_2064_, lean_object* v_inst_2065_, lean_object* v_stx_2066_, lean_object* v_n_2067_, lean_object* v_expectedType_x3f_2068_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_Elab_addConstInfo___redArg(v_inst_2062_, v_inst_2063_, v_inst_2064_, v_inst_2065_, v_stx_2066_, v_n_2067_, v_expectedType_x3f_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___x_2073_; lean_object* v_infoState_2074_; uint8_t v_enabled_2075_; 
v___x_2073_ = lean_st_ref_get(v___y_2071_);
v_infoState_2074_ = lean_ctor_get(v___x_2073_, 7);
lean_inc_ref(v_infoState_2074_);
lean_dec(v___x_2073_);
v_enabled_2075_ = lean_ctor_get_uint8(v_infoState_2074_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2074_);
if (v_enabled_2075_ == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_dec_ref(v_t_2070_);
v___x_2076_ = lean_box(0);
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
return v___x_2077_;
}
else
{
lean_object* v___x_2078_; lean_object* v_infoState_2079_; lean_object* v_env_2080_; lean_object* v_nextMacroScope_2081_; lean_object* v_ngen_2082_; lean_object* v_auxDeclNGen_2083_; lean_object* v_traceState_2084_; lean_object* v_cache_2085_; lean_object* v_messages_2086_; lean_object* v_snapshotTasks_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2109_; 
v___x_2078_ = lean_st_ref_take(v___y_2071_);
v_infoState_2079_ = lean_ctor_get(v___x_2078_, 7);
v_env_2080_ = lean_ctor_get(v___x_2078_, 0);
v_nextMacroScope_2081_ = lean_ctor_get(v___x_2078_, 1);
v_ngen_2082_ = lean_ctor_get(v___x_2078_, 2);
v_auxDeclNGen_2083_ = lean_ctor_get(v___x_2078_, 3);
v_traceState_2084_ = lean_ctor_get(v___x_2078_, 4);
v_cache_2085_ = lean_ctor_get(v___x_2078_, 5);
v_messages_2086_ = lean_ctor_get(v___x_2078_, 6);
v_snapshotTasks_2087_ = lean_ctor_get(v___x_2078_, 8);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2089_ = v___x_2078_;
v_isShared_2090_ = v_isSharedCheck_2109_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_snapshotTasks_2087_);
lean_inc(v_infoState_2079_);
lean_inc(v_messages_2086_);
lean_inc(v_cache_2085_);
lean_inc(v_traceState_2084_);
lean_inc(v_auxDeclNGen_2083_);
lean_inc(v_ngen_2082_);
lean_inc(v_nextMacroScope_2081_);
lean_inc(v_env_2080_);
lean_dec(v___x_2078_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2109_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
uint8_t v_enabled_2091_; lean_object* v_assignment_2092_; lean_object* v_lazyAssignment_2093_; lean_object* v_trees_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2108_; 
v_enabled_2091_ = lean_ctor_get_uint8(v_infoState_2079_, sizeof(void*)*3);
v_assignment_2092_ = lean_ctor_get(v_infoState_2079_, 0);
v_lazyAssignment_2093_ = lean_ctor_get(v_infoState_2079_, 1);
v_trees_2094_ = lean_ctor_get(v_infoState_2079_, 2);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_infoState_2079_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2096_ = v_infoState_2079_;
v_isShared_2097_ = v_isSharedCheck_2108_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_trees_2094_);
lean_inc(v_lazyAssignment_2093_);
lean_inc(v_assignment_2092_);
lean_dec(v_infoState_2079_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2108_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2098_ = l_Lean_PersistentArray_push___redArg(v_trees_2094_, v_t_2070_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 2, v___x_2098_);
v___x_2100_ = v___x_2096_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_assignment_2092_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_lazyAssignment_2093_);
lean_ctor_set(v_reuseFailAlloc_2107_, 2, v___x_2098_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*3, v_enabled_2091_);
v___x_2100_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2102_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 7, v___x_2100_);
v___x_2102_ = v___x_2089_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_env_2080_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_nextMacroScope_2081_);
lean_ctor_set(v_reuseFailAlloc_2106_, 2, v_ngen_2082_);
lean_ctor_set(v_reuseFailAlloc_2106_, 3, v_auxDeclNGen_2083_);
lean_ctor_set(v_reuseFailAlloc_2106_, 4, v_traceState_2084_);
lean_ctor_set(v_reuseFailAlloc_2106_, 5, v_cache_2085_);
lean_ctor_set(v_reuseFailAlloc_2106_, 6, v_messages_2086_);
lean_ctor_set(v_reuseFailAlloc_2106_, 7, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2106_, 8, v_snapshotTasks_2087_);
v___x_2102_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2103_ = lean_st_ref_set(v___y_2071_, v___x_2102_);
v___x_2104_ = lean_box(0);
v___x_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
return v___x_2105_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2110_, v___y_2111_);
lean_dec(v___y_2111_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object* v_t_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___x_2118_; lean_object* v_infoState_2119_; uint8_t v_enabled_2120_; 
v___x_2118_ = lean_st_ref_get(v___y_2116_);
v_infoState_2119_ = lean_ctor_get(v___x_2118_, 7);
lean_inc_ref(v_infoState_2119_);
lean_dec(v___x_2118_);
v_enabled_2120_ = lean_ctor_get_uint8(v_infoState_2119_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2119_);
if (v_enabled_2120_ == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
lean_dec_ref(v_t_2114_);
v___x_2121_ = lean_box(0);
v___x_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
return v___x_2122_;
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2123_ = lean_unsigned_to_nat(32u);
v___x_2124_ = lean_mk_empty_array_with_capacity(v___x_2123_);
lean_dec_ref(v___x_2124_);
v___x_2125_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2126_, 0, v_t_2114_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v___x_2126_, v___y_2116_);
return v___x_2127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object* v_t_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
return v_res_2132_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2133_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
return v___x_2135_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2136_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2137_ = lean_unsigned_to_nat(0u);
v___x_2138_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2137_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
lean_ctor_set(v___x_2138_, 2, v___x_2137_);
lean_ctor_set(v___x_2138_, 3, v___x_2137_);
lean_ctor_set(v___x_2138_, 4, v___x_2136_);
lean_ctor_set(v___x_2138_, 5, v___x_2136_);
lean_ctor_set(v___x_2138_, 6, v___x_2136_);
lean_ctor_set(v___x_2138_, 7, v___x_2136_);
lean_ctor_set(v___x_2138_, 8, v___x_2136_);
lean_ctor_set(v___x_2138_, 9, v___x_2136_);
return v___x_2138_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2139_ = lean_box(1);
v___x_2140_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_2141_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
lean_ctor_set(v___x_2142_, 1, v___x_2140_);
lean_ctor_set(v___x_2142_, 2, v___x_2139_);
return v___x_2142_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_2145_ = l_Lean_stringToMessageData(v___x_2144_);
return v___x_2145_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2147_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_2148_ = l_Lean_stringToMessageData(v___x_2147_);
return v___x_2148_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_2151_ = l_Lean_stringToMessageData(v___x_2150_);
return v___x_2151_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_2154_ = l_Lean_stringToMessageData(v___x_2153_);
return v___x_2154_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_2157_ = l_Lean_stringToMessageData(v___x_2156_);
return v___x_2157_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_2160_ = l_Lean_stringToMessageData(v___x_2159_);
return v___x_2160_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_2163_ = l_Lean_stringToMessageData(v___x_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_2164_, lean_object* v_declHint_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v___x_2168_; lean_object* v_env_2169_; uint8_t v___y_2171_; uint8_t v___x_2227_; uint8_t v___x_2228_; 
v___x_2168_ = lean_st_ref_get(v___y_2166_);
v_env_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc_ref(v_env_2169_);
lean_dec(v___x_2168_);
v___x_2227_ = l_Lean_Name_isAnonymous(v_declHint_2165_);
v___x_2228_ = lean_bool_not(v___x_2227_);
if (v___x_2228_ == 0)
{
v___y_2171_ = v___x_2228_;
goto v___jp_2170_;
}
else
{
uint8_t v_isExporting_2229_; 
v_isExporting_2229_ = lean_ctor_get_uint8(v_env_2169_, sizeof(void*)*8);
v___y_2171_ = v_isExporting_2229_;
goto v___jp_2170_;
}
v___jp_2170_:
{
if (v___y_2171_ == 0)
{
lean_object* v___x_2172_; 
lean_dec_ref(v_env_2169_);
lean_dec(v_declHint_2165_);
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v_msg_2164_);
return v___x_2172_;
}
else
{
uint8_t v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2173_ = 0;
lean_inc_ref(v_env_2169_);
v___x_2174_ = l_Lean_Environment_setExporting(v_env_2169_, v___x_2173_);
lean_inc(v_declHint_2165_);
lean_inc_ref(v___x_2174_);
v___x_2175_ = l_Lean_Environment_contains(v___x_2174_, v_declHint_2165_, v___y_2171_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; 
lean_dec_ref(v___x_2174_);
lean_dec_ref(v_env_2169_);
lean_dec(v_declHint_2165_);
v___x_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2176_, 0, v_msg_2164_);
return v___x_2176_;
}
else
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v_c_2182_; lean_object* v___x_2183_; 
v___x_2177_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_2178_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_2179_ = l_Lean_Options_empty;
v___x_2180_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2174_);
lean_ctor_set(v___x_2180_, 1, v___x_2177_);
lean_ctor_set(v___x_2180_, 2, v___x_2178_);
lean_ctor_set(v___x_2180_, 3, v___x_2179_);
lean_inc(v_declHint_2165_);
v___x_2181_ = l_Lean_MessageData_ofConstName(v_declHint_2165_, v___x_2173_);
v_c_2182_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2182_, 0, v___x_2180_);
lean_ctor_set(v_c_2182_, 1, v___x_2181_);
v___x_2183_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2169_, v_declHint_2165_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_dec_ref(v_env_2169_);
lean_dec(v_declHint_2165_);
v___x_2184_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_2185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
lean_ctor_set(v___x_2185_, 1, v_c_2182_);
v___x_2186_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_2187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2185_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
v___x_2188_ = l_Lean_MessageData_note(v___x_2187_);
v___x_2189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2189_, 0, v_msg_2164_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
return v___x_2190_;
}
else
{
lean_object* v_val_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2226_; 
v_val_2191_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2193_ = v___x_2183_;
v_isShared_2194_ = v_isSharedCheck_2226_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_val_2191_);
lean_dec(v___x_2183_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2226_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v_mod_2198_; uint8_t v___x_2199_; 
v___x_2195_ = lean_box(0);
v___x_2196_ = l_Lean_Environment_header(v_env_2169_);
lean_dec_ref(v_env_2169_);
v___x_2197_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2196_);
v_mod_2198_ = lean_array_get(v___x_2195_, v___x_2197_, v_val_2191_);
lean_dec(v_val_2191_);
lean_dec_ref(v___x_2197_);
v___x_2199_ = l_Lean_isPrivateName(v_declHint_2165_);
lean_dec(v_declHint_2165_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2211_; 
v___x_2200_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_2201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
lean_ctor_set(v___x_2201_, 1, v_c_2182_);
v___x_2202_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_2203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2201_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = l_Lean_MessageData_ofName(v_mod_2198_);
v___x_2205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2203_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_2207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = l_Lean_MessageData_note(v___x_2207_);
v___x_2209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2209_, 0, v_msg_2164_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set_tag(v___x_2193_, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2209_);
v___x_2211_ = v___x_2193_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2213_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_2214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
lean_ctor_set(v___x_2214_, 1, v_c_2182_);
v___x_2215_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_2216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2214_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = l_Lean_MessageData_ofName(v_mod_2198_);
v___x_2218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2216_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
v___x_2219_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_2220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2218_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v___x_2221_ = l_Lean_MessageData_note(v___x_2220_);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v_msg_2164_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set_tag(v___x_2193_, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2222_);
v___x_2224_ = v___x_2193_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_2230_, lean_object* v_declHint_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2230_, v_declHint_2231_, v___y_2232_);
lean_dec(v___y_2232_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_2235_, lean_object* v_declHint_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v___x_2240_; lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2250_; 
v___x_2240_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2235_, v_declHint_2236_, v___y_2238_);
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2250_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2250_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2245_ = l_Lean_unknownIdentifierMessageTag;
v___x_2246_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
lean_ctor_set(v___x_2246_, 1, v_a_2241_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v___x_2246_);
v___x_2248_ = v___x_2243_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_2251_, lean_object* v_declHint_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2251_, v_declHint_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object* v_msgData_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v___x_2261_; lean_object* v_env_2262_; lean_object* v_options_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2261_ = lean_st_ref_get(v___y_2259_);
v_env_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc_ref(v_env_2262_);
lean_dec(v___x_2261_);
v_options_2263_ = lean_ctor_get(v___y_2258_, 2);
v___x_2264_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_2265_ = lean_unsigned_to_nat(32u);
v___x_2266_ = lean_mk_empty_array_with_capacity(v___x_2265_);
lean_dec_ref(v___x_2266_);
v___x_2267_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
lean_inc_ref(v_options_2263_);
v___x_2268_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2268_, 0, v_env_2262_);
lean_ctor_set(v___x_2268_, 1, v___x_2264_);
lean_ctor_set(v___x_2268_, 2, v___x_2267_);
lean_ctor_set(v___x_2268_, 3, v_options_2263_);
v___x_2269_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
lean_ctor_set(v___x_2269_, 1, v_msgData_2257_);
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object* v_msgData_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_2271_, v___y_2272_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v_ref_2280_; lean_object* v___x_2281_; lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2290_; 
v_ref_2280_ = lean_ctor_get(v___y_2277_, 5);
v___x_2281_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_2276_, v___y_2277_, v___y_2278_);
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2284_ = v___x_2281_;
v_isShared_2285_ = v_isSharedCheck_2290_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2281_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2290_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v___x_2288_; 
lean_inc(v_ref_2280_);
v___x_2286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2286_, 0, v_ref_2280_);
lean_ctor_set(v___x_2286_, 1, v_a_2282_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set_tag(v___x_2284_, 1);
lean_ctor_set(v___x_2284_, 0, v___x_2286_);
v___x_2288_ = v___x_2284_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_2296_, lean_object* v_msg_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v_fileName_2301_; lean_object* v_fileMap_2302_; lean_object* v_options_2303_; lean_object* v_currRecDepth_2304_; lean_object* v_maxRecDepth_2305_; lean_object* v_ref_2306_; lean_object* v_currNamespace_2307_; lean_object* v_openDecls_2308_; lean_object* v_initHeartbeats_2309_; lean_object* v_maxHeartbeats_2310_; lean_object* v_quotContext_2311_; lean_object* v_currMacroScope_2312_; uint8_t v_diag_2313_; lean_object* v_cancelTk_x3f_2314_; uint8_t v_suppressElabErrors_2315_; lean_object* v_inheritedTraceOptions_2316_; lean_object* v_ref_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v_fileName_2301_ = lean_ctor_get(v___y_2298_, 0);
v_fileMap_2302_ = lean_ctor_get(v___y_2298_, 1);
v_options_2303_ = lean_ctor_get(v___y_2298_, 2);
v_currRecDepth_2304_ = lean_ctor_get(v___y_2298_, 3);
v_maxRecDepth_2305_ = lean_ctor_get(v___y_2298_, 4);
v_ref_2306_ = lean_ctor_get(v___y_2298_, 5);
v_currNamespace_2307_ = lean_ctor_get(v___y_2298_, 6);
v_openDecls_2308_ = lean_ctor_get(v___y_2298_, 7);
v_initHeartbeats_2309_ = lean_ctor_get(v___y_2298_, 8);
v_maxHeartbeats_2310_ = lean_ctor_get(v___y_2298_, 9);
v_quotContext_2311_ = lean_ctor_get(v___y_2298_, 10);
v_currMacroScope_2312_ = lean_ctor_get(v___y_2298_, 11);
v_diag_2313_ = lean_ctor_get_uint8(v___y_2298_, sizeof(void*)*14);
v_cancelTk_x3f_2314_ = lean_ctor_get(v___y_2298_, 12);
v_suppressElabErrors_2315_ = lean_ctor_get_uint8(v___y_2298_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2316_ = lean_ctor_get(v___y_2298_, 13);
v_ref_2317_ = l_Lean_replaceRef(v_ref_2296_, v_ref_2306_);
lean_inc_ref(v_inheritedTraceOptions_2316_);
lean_inc(v_cancelTk_x3f_2314_);
lean_inc(v_currMacroScope_2312_);
lean_inc(v_quotContext_2311_);
lean_inc(v_maxHeartbeats_2310_);
lean_inc(v_initHeartbeats_2309_);
lean_inc(v_openDecls_2308_);
lean_inc(v_currNamespace_2307_);
lean_inc(v_maxRecDepth_2305_);
lean_inc(v_currRecDepth_2304_);
lean_inc_ref(v_options_2303_);
lean_inc_ref(v_fileMap_2302_);
lean_inc_ref(v_fileName_2301_);
v___x_2318_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2318_, 0, v_fileName_2301_);
lean_ctor_set(v___x_2318_, 1, v_fileMap_2302_);
lean_ctor_set(v___x_2318_, 2, v_options_2303_);
lean_ctor_set(v___x_2318_, 3, v_currRecDepth_2304_);
lean_ctor_set(v___x_2318_, 4, v_maxRecDepth_2305_);
lean_ctor_set(v___x_2318_, 5, v_ref_2317_);
lean_ctor_set(v___x_2318_, 6, v_currNamespace_2307_);
lean_ctor_set(v___x_2318_, 7, v_openDecls_2308_);
lean_ctor_set(v___x_2318_, 8, v_initHeartbeats_2309_);
lean_ctor_set(v___x_2318_, 9, v_maxHeartbeats_2310_);
lean_ctor_set(v___x_2318_, 10, v_quotContext_2311_);
lean_ctor_set(v___x_2318_, 11, v_currMacroScope_2312_);
lean_ctor_set(v___x_2318_, 12, v_cancelTk_x3f_2314_);
lean_ctor_set(v___x_2318_, 13, v_inheritedTraceOptions_2316_);
lean_ctor_set_uint8(v___x_2318_, sizeof(void*)*14, v_diag_2313_);
lean_ctor_set_uint8(v___x_2318_, sizeof(void*)*14 + 1, v_suppressElabErrors_2315_);
v___x_2319_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2297_, v___x_2318_, v___y_2299_);
lean_dec_ref_known(v___x_2318_, 14);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_2320_, lean_object* v_msg_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2320_, v_msg_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v_ref_2320_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_2326_, lean_object* v_msg_2327_, lean_object* v_declHint_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v___x_2332_; lean_object* v_a_2333_; lean_object* v___x_2334_; 
v___x_2332_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2327_, v_declHint_2328_, v___y_2329_, v___y_2330_);
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref(v___x_2332_);
v___x_2334_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2326_, v_a_2333_, v___y_2329_, v___y_2330_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2335_, lean_object* v_msg_2336_, lean_object* v_declHint_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2335_, v_msg_2336_, v_declHint_2337_, v___y_2338_, v___y_2339_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v_ref_2335_);
return v_res_2341_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_2344_ = l_Lean_stringToMessageData(v___x_2343_);
return v___x_2344_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2));
v___x_2347_ = l_Lean_stringToMessageData(v___x_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_2348_, lean_object* v_constName_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v___x_2353_; uint8_t v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2353_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_2354_ = 0;
lean_inc(v_constName_2349_);
v___x_2355_ = l_Lean_MessageData_ofConstName(v_constName_2349_, v___x_2354_);
v___x_2356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2353_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
v___x_2357_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_2358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2356_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2348_, v___x_2358_, v_constName_2349_, v___y_2350_, v___y_2351_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2360_, lean_object* v_constName_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2360_, v_constName_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v_ref_2360_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_ref_2370_; lean_object* v___x_2371_; 
v_ref_2370_ = lean_ctor_get(v___y_2367_, 5);
v___x_2371_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2370_, v_constName_2366_, v___y_2367_, v___y_2368_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object* v_constName_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; lean_object* v_env_2382_; uint8_t v___x_2383_; lean_object* v___x_2384_; 
v___x_2381_ = lean_st_ref_get(v___y_2379_);
v_env_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc_ref(v_env_2382_);
lean_dec(v___x_2381_);
v___x_2383_ = 0;
lean_inc(v_constName_2377_);
v___x_2384_ = l_Lean_Environment_findConstVal_x3f(v_env_2382_, v_constName_2377_, v___x_2383_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2377_, v___y_2378_, v___y_2379_);
return v___x_2385_;
}
else
{
lean_object* v_val_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec(v_constName_2377_);
v_val_2386_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2384_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_val_2386_);
lean_dec(v___x_2384_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
lean_ctor_set_tag(v___x_2388_, 0);
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_val_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object* v_a_2399_, lean_object* v_a_2400_){
_start:
{
if (lean_obj_tag(v_a_2399_) == 0)
{
lean_object* v___x_2401_; 
v___x_2401_ = l_List_reverse___redArg(v_a_2400_);
return v___x_2401_;
}
else
{
lean_object* v_head_2402_; lean_object* v_tail_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2412_; 
v_head_2402_ = lean_ctor_get(v_a_2399_, 0);
v_tail_2403_ = lean_ctor_get(v_a_2399_, 1);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_a_2399_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2405_ = v_a_2399_;
v_isShared_2406_ = v_isSharedCheck_2412_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_tail_2403_);
lean_inc(v_head_2402_);
lean_dec(v_a_2399_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2412_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2407_ = l_Lean_mkLevelParam(v_head_2402_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 1, v_a_2400_);
lean_ctor_set(v___x_2405_, 0, v___x_2407_);
v___x_2409_ = v___x_2405_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v_a_2400_);
v___x_2409_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
v_a_2399_ = v_tail_2403_;
v_a_2400_ = v___x_2409_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object* v_constName_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v___x_2417_; 
lean_inc(v_constName_2413_);
v___x_2417_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2429_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2429_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2429_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v_levelParams_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2427_; 
v_levelParams_2422_ = lean_ctor_get(v_a_2418_, 1);
lean_inc(v_levelParams_2422_);
lean_dec(v_a_2418_);
v___x_2423_ = lean_box(0);
v___x_2424_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_2422_, v___x_2423_);
v___x_2425_ = l_Lean_mkConst(v_constName_2413_, v___x_2424_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2425_);
v___x_2427_ = v___x_2420_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec(v_constName_2413_);
v_a_2430_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2417_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2417_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object* v_constName_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object* v_stx_2443_, lean_object* v_n_2444_, lean_object* v_expectedType_x3f_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_2444_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2449_, 1);
v___x_2451_ = lean_box(0);
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
lean_ctor_set(v___x_2452_, 1, v_stx_2443_);
v___x_2453_ = l_Lean_LocalContext_empty;
v___x_2454_ = 0;
v___x_2455_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2455_, 0, v___x_2452_);
lean_ctor_set(v___x_2455_, 1, v___x_2453_);
lean_ctor_set(v___x_2455_, 2, v_expectedType_x3f_2445_);
lean_ctor_set(v___x_2455_, 3, v_a_2450_);
lean_ctor_set_uint8(v___x_2455_, sizeof(void*)*4, v___x_2454_);
lean_ctor_set_uint8(v___x_2455_, sizeof(void*)*4 + 1, v___x_2454_);
v___x_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
v___x_2457_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_2456_, v___y_2446_, v___y_2447_);
return v___x_2457_;
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
lean_dec(v_expectedType_x3f_2445_);
lean_dec(v_stx_2443_);
v_a_2458_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2449_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2449_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object* v_stx_2466_, lean_object* v_n_2467_, lean_object* v_expectedType_x3f_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_2466_, v_n_2467_, v_expectedType_x3f_2468_, v___y_2469_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object* v_id_2473_, lean_object* v_expectedType_x3f_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v___x_2478_; 
lean_inc(v_id_2473_);
v___x_2478_ = l_Lean_realizeGlobalConstNoOverload(v_id_2473_, v_a_2475_, v_a_2476_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2506_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2481_ = v___x_2478_;
v_isShared_2482_ = v_isSharedCheck_2506_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2506_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2483_; lean_object* v_infoState_2484_; uint8_t v_enabled_2485_; 
v___x_2483_ = lean_st_ref_get(v_a_2476_);
v_infoState_2484_ = lean_ctor_get(v___x_2483_, 7);
lean_inc_ref(v_infoState_2484_);
lean_dec(v___x_2483_);
v_enabled_2485_ = lean_ctor_get_uint8(v_infoState_2484_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2484_);
if (v_enabled_2485_ == 0)
{
lean_object* v___x_2487_; 
lean_dec(v_expectedType_x3f_2474_);
lean_dec(v_id_2473_);
if (v_isShared_2482_ == 0)
{
v___x_2487_ = v___x_2481_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2479_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
else
{
lean_object* v___x_2489_; 
lean_del_object(v___x_2481_);
lean_inc(v_a_2479_);
v___x_2489_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2473_, v_a_2479_, v_expectedType_x3f_2474_, v_a_2475_, v_a_2476_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2496_ == 0)
{
lean_object* v_unused_2497_; 
v_unused_2497_ = lean_ctor_get(v___x_2489_, 0);
lean_dec(v_unused_2497_);
v___x_2491_ = v___x_2489_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_dec(v___x_2489_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 0, v_a_2479_);
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2479_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
lean_dec(v_a_2479_);
v_a_2498_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2489_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2489_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2474_);
lean_dec(v_id_2473_);
return v___x_2478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object* v_id_2507_, lean_object* v_expectedType_x3f_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_2507_, v_expectedType_x3f_2508_, v_a_2509_, v_a_2510_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object* v_t_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2513_, v___y_2515_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_2518_, v___y_2519_, v___y_2520_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2523_, lean_object* v_constName_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2524_, v___y_2525_, v___y_2526_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2529_, lean_object* v_constName_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2529_, v_constName_2530_, v___y_2531_, v___y_2532_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2535_, lean_object* v_ref_2536_, lean_object* v_constName_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2536_, v_constName_2537_, v___y_2538_, v___y_2539_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2542_, lean_object* v_ref_2543_, lean_object* v_constName_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_2542_, v_ref_2543_, v_constName_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v_ref_2543_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2549_, lean_object* v_ref_2550_, lean_object* v_msg_2551_, lean_object* v_declHint_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2550_, v_msg_2551_, v_declHint_2552_, v___y_2553_, v___y_2554_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2557_, lean_object* v_ref_2558_, lean_object* v_msg_2559_, lean_object* v_declHint_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_2557_, v_ref_2558_, v_msg_2559_, v_declHint_2560_, v___y_2561_, v___y_2562_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v_ref_2558_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_2565_, lean_object* v_declHint_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2565_, v_declHint_2566_, v___y_2568_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2571_, lean_object* v_declHint_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2571_, v_declHint_2572_, v___y_2573_, v___y_2574_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_2577_, lean_object* v_ref_2578_, lean_object* v_msg_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2578_, v_msg_2579_, v___y_2580_, v___y_2581_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2584_, lean_object* v_ref_2585_, lean_object* v_msg_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_2584_, v_ref_2585_, v_msg_2586_, v___y_2587_, v___y_2588_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v_ref_2585_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_2591_, lean_object* v_msg_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v___x_2596_; 
v___x_2596_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2592_, v___y_2593_, v___y_2594_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_2597_, lean_object* v_msg_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_2597_, v_msg_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object* v_id_2603_, lean_object* v_expectedType_x3f_2604_, lean_object* v_as_x27_2605_, lean_object* v_b_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
if (lean_obj_tag(v_as_x27_2605_) == 0)
{
lean_object* v___x_2610_; 
lean_dec(v_expectedType_x3f_2604_);
lean_dec(v_id_2603_);
v___x_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2610_, 0, v_b_2606_);
return v___x_2610_;
}
else
{
lean_object* v_head_2611_; lean_object* v_tail_2612_; lean_object* v___x_2613_; 
v_head_2611_ = lean_ctor_get(v_as_x27_2605_, 0);
v_tail_2612_ = lean_ctor_get(v_as_x27_2605_, 1);
lean_inc(v_expectedType_x3f_2604_);
lean_inc(v_head_2611_);
lean_inc(v_id_2603_);
v___x_2613_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2603_, v_head_2611_, v_expectedType_x3f_2604_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v___x_2614_; 
lean_dec_ref_known(v___x_2613_, 1);
v___x_2614_ = lean_box(0);
v_as_x27_2605_ = v_tail_2612_;
v_b_2606_ = v___x_2614_;
goto _start;
}
else
{
lean_dec(v_expectedType_x3f_2604_);
lean_dec(v_id_2603_);
return v___x_2613_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object* v_id_2616_, lean_object* v_expectedType_x3f_2617_, lean_object* v_as_x27_2618_, lean_object* v_b_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2616_, v_expectedType_x3f_2617_, v_as_x27_2618_, v_b_2619_, v___y_2620_, v___y_2621_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v_as_x27_2618_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object* v_id_2624_, lean_object* v_expectedType_x3f_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_){
_start:
{
lean_object* v___x_2629_; 
lean_inc(v_id_2624_);
v___x_2629_ = l_Lean_realizeGlobalConst(v_id_2624_, v_a_2626_, v_a_2627_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2658_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2632_ = v___x_2629_;
v_isShared_2633_ = v_isSharedCheck_2658_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2629_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2658_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2634_; lean_object* v_infoState_2635_; uint8_t v_enabled_2636_; 
v___x_2634_ = lean_st_ref_get(v_a_2627_);
v_infoState_2635_ = lean_ctor_get(v___x_2634_, 7);
lean_inc_ref(v_infoState_2635_);
lean_dec(v___x_2634_);
v_enabled_2636_ = lean_ctor_get_uint8(v_infoState_2635_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2635_);
if (v_enabled_2636_ == 0)
{
lean_object* v___x_2638_; 
lean_dec(v_expectedType_x3f_2625_);
lean_dec(v_id_2624_);
if (v_isShared_2633_ == 0)
{
v___x_2638_ = v___x_2632_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2630_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
else
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
lean_del_object(v___x_2632_);
v___x_2640_ = lean_box(0);
v___x_2641_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2624_, v_expectedType_x3f_2625_, v_a_2630_, v___x_2640_, v_a_2626_, v_a_2627_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2648_ == 0)
{
lean_object* v_unused_2649_; 
v_unused_2649_ = lean_ctor_get(v___x_2641_, 0);
lean_dec(v_unused_2649_);
v___x_2643_ = v___x_2641_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_dec(v___x_2641_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v_a_2630_);
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2630_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_dec(v_a_2630_);
v_a_2650_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2641_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2641_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2625_);
lean_dec(v_id_2624_);
return v___x_2629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object* v_id_2659_, lean_object* v_expectedType_x3f_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_2659_, v_expectedType_x3f_2660_, v_a_2661_, v_a_2662_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object* v_id_2665_, lean_object* v_expectedType_x3f_2666_, lean_object* v_as_2667_, lean_object* v_as_x27_2668_, lean_object* v_b_2669_, lean_object* v_a_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2665_, v_expectedType_x3f_2666_, v_as_x27_2668_, v_b_2669_, v___y_2671_, v___y_2672_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object* v_id_2675_, lean_object* v_expectedType_x3f_2676_, lean_object* v_as_2677_, lean_object* v_as_x27_2678_, lean_object* v_b_2679_, lean_object* v_a_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_2675_, v_expectedType_x3f_2676_, v_as_2677_, v_as_x27_2678_, v_b_2679_, v_a_2680_, v___y_2681_, v___y_2682_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v_as_x27_2678_);
lean_dec(v_as_2677_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object* v_ref_2685_, lean_object* v_as_x27_2686_, lean_object* v_b_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
if (lean_obj_tag(v_as_x27_2686_) == 0)
{
lean_object* v___x_2691_; 
lean_dec(v_ref_2685_);
v___x_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2691_, 0, v_b_2687_);
return v___x_2691_;
}
else
{
lean_object* v_head_2692_; lean_object* v_tail_2693_; lean_object* v_fst_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v_head_2692_ = lean_ctor_get(v_as_x27_2686_, 0);
v_tail_2693_ = lean_ctor_get(v_as_x27_2686_, 1);
v_fst_2694_ = lean_ctor_get(v_head_2692_, 0);
v___x_2695_ = lean_box(0);
lean_inc(v_fst_2694_);
lean_inc(v_ref_2685_);
v___x_2696_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_2685_, v_fst_2694_, v___x_2695_, v___y_2688_, v___y_2689_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v___x_2697_; 
lean_dec_ref_known(v___x_2696_, 1);
v___x_2697_ = lean_box(0);
v_as_x27_2686_ = v_tail_2693_;
v_b_2687_ = v___x_2697_;
goto _start;
}
else
{
lean_dec(v_ref_2685_);
return v___x_2696_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object* v_ref_2699_, lean_object* v_as_x27_2700_, lean_object* v_b_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2699_, v_as_x27_2700_, v_b_2701_, v___y_2702_, v___y_2703_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v_as_x27_2700_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object* v_ref_2706_, lean_object* v_id_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lean_realizeGlobalName(v_id_2707_, v_a_2708_, v_a_2709_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2740_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2714_ = v___x_2711_;
v_isShared_2715_ = v_isSharedCheck_2740_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2711_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2740_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2716_; lean_object* v_infoState_2717_; uint8_t v_enabled_2718_; 
v___x_2716_ = lean_st_ref_get(v_a_2709_);
v_infoState_2717_ = lean_ctor_get(v___x_2716_, 7);
lean_inc_ref(v_infoState_2717_);
lean_dec(v___x_2716_);
v_enabled_2718_ = lean_ctor_get_uint8(v_infoState_2717_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2717_);
if (v_enabled_2718_ == 0)
{
lean_object* v___x_2720_; 
lean_dec(v_ref_2706_);
if (v_isShared_2715_ == 0)
{
v___x_2720_ = v___x_2714_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2712_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
else
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
lean_del_object(v___x_2714_);
v___x_2722_ = lean_box(0);
v___x_2723_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2706_, v_a_2712_, v___x_2722_, v_a_2708_, v_a_2709_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2730_ == 0)
{
lean_object* v_unused_2731_; 
v_unused_2731_ = lean_ctor_get(v___x_2723_, 0);
lean_dec(v_unused_2731_);
v___x_2725_ = v___x_2723_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_dec(v___x_2723_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 0, v_a_2712_);
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2712_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
lean_dec(v_a_2712_);
v_a_2732_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2723_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2723_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
}
}
else
{
lean_dec(v_ref_2706_);
return v___x_2711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object* v_ref_2741_, lean_object* v_id_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_2741_, v_id_2742_, v_a_2743_, v_a_2744_);
lean_dec(v_a_2744_);
lean_dec_ref(v_a_2743_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object* v_ref_2747_, lean_object* v_as_2748_, lean_object* v_as_x27_2749_, lean_object* v_b_2750_, lean_object* v_a_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2747_, v_as_x27_2749_, v_b_2750_, v___y_2752_, v___y_2753_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object* v_ref_2756_, lean_object* v_as_2757_, lean_object* v_as_x27_2758_, lean_object* v_b_2759_, lean_object* v_a_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_2756_, v_as_2757_, v_as_x27_2758_, v_b_2759_, v_a_2760_, v___y_2761_, v___y_2762_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v_as_x27_2758_);
lean_dec(v_as_2757_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object* v_self_2765_){
_start:
{
lean_object* v_fst_2766_; 
v_fst_2766_ = lean_ctor_get(v_self_2765_, 0);
lean_inc(v_fst_2766_);
return v_fst_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object* v_self_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_2767_);
lean_dec_ref(v_self_2767_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object* v_info_2769_, lean_object* v_treesSaved_2770_, lean_object* v_s_2771_){
_start:
{
if (lean_obj_tag(v_info_2769_) == 0)
{
uint8_t v_enabled_2772_; lean_object* v_assignment_2773_; lean_object* v_lazyAssignment_2774_; lean_object* v_trees_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2785_; 
v_enabled_2772_ = lean_ctor_get_uint8(v_s_2771_, sizeof(void*)*3);
v_assignment_2773_ = lean_ctor_get(v_s_2771_, 0);
v_lazyAssignment_2774_ = lean_ctor_get(v_s_2771_, 1);
v_trees_2775_ = lean_ctor_get(v_s_2771_, 2);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_s_2771_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2777_ = v_s_2771_;
v_isShared_2778_ = v_isSharedCheck_2785_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_trees_2775_);
lean_inc(v_lazyAssignment_2774_);
lean_inc(v_assignment_2773_);
lean_dec(v_s_2771_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2785_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v_val_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2783_; 
v_val_2779_ = lean_ctor_get(v_info_2769_, 0);
lean_inc(v_val_2779_);
lean_dec_ref_known(v_info_2769_, 1);
v___x_2780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2780_, 0, v_val_2779_);
lean_ctor_set(v___x_2780_, 1, v_trees_2775_);
v___x_2781_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2770_, v___x_2780_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 2, v___x_2781_);
v___x_2783_ = v___x_2777_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_assignment_2773_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v_lazyAssignment_2774_);
lean_ctor_set(v_reuseFailAlloc_2784_, 2, v___x_2781_);
lean_ctor_set_uint8(v_reuseFailAlloc_2784_, sizeof(void*)*3, v_enabled_2772_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
else
{
uint8_t v_enabled_2786_; lean_object* v_assignment_2787_; lean_object* v_lazyAssignment_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2804_; 
v_enabled_2786_ = lean_ctor_get_uint8(v_s_2771_, sizeof(void*)*3);
v_assignment_2787_ = lean_ctor_get(v_s_2771_, 0);
v_lazyAssignment_2788_ = lean_ctor_get(v_s_2771_, 1);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_s_2771_);
if (v_isSharedCheck_2804_ == 0)
{
lean_object* v_unused_2805_; 
v_unused_2805_ = lean_ctor_get(v_s_2771_, 2);
lean_dec(v_unused_2805_);
v___x_2790_ = v_s_2771_;
v_isShared_2791_ = v_isSharedCheck_2804_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_lazyAssignment_2788_);
lean_inc(v_assignment_2787_);
lean_dec(v_s_2771_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2804_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v_val_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2803_; 
v_val_2792_ = lean_ctor_get(v_info_2769_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v_info_2769_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2794_ = v_info_2769_;
v_isShared_2795_ = v_isSharedCheck_2803_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_val_2792_);
lean_dec(v_info_2769_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2803_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
lean_ctor_set_tag(v___x_2794_, 2);
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_val_2792_);
v___x_2797_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_object* v___x_2798_; lean_object* v___x_2800_; 
v___x_2798_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2770_, v___x_2797_);
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 2, v___x_2798_);
v___x_2800_ = v___x_2790_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_assignment_2787_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_lazyAssignment_2788_);
lean_ctor_set(v_reuseFailAlloc_2801_, 2, v___x_2798_);
lean_ctor_set_uint8(v_reuseFailAlloc_2801_, sizeof(void*)*3, v_enabled_2786_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object* v_treesSaved_2806_, lean_object* v_modifyInfoState_2807_, lean_object* v_info_2808_){
_start:
{
lean_object* v___f_2809_; lean_object* v___x_2810_; 
v___f_2809_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2809_, 0, v_info_2808_);
lean_closure_set(v___f_2809_, 1, v_treesSaved_2806_);
v___x_2810_ = lean_apply_1(v_modifyInfoState_2807_, v___f_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object* v___f_2811_, lean_object* v_info_2812_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = lean_apply_1(v___f_2811_, v_info_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object* v_toPure_2814_, lean_object* v_toBind_2815_, lean_object* v___f_2816_, lean_object* v_____do__lift_2817_){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2818_, 0, v_____do__lift_2817_);
v___x_2819_ = lean_apply_2(v_toPure_2814_, lean_box(0), v___x_2818_);
v___x_2820_ = lean_apply_4(v_toBind_2815_, lean_box(0), lean_box(0), v___x_2819_, v___f_2816_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object* v_toBind_2821_, lean_object* v_mkInfoOnError_2822_, lean_object* v___f_2823_, lean_object* v_mkInfo_2824_, lean_object* v___f_2825_, lean_object* v_a_x3f_2826_){
_start:
{
if (lean_obj_tag(v_a_x3f_2826_) == 0)
{
lean_object* v___x_2827_; 
lean_dec(v___f_2825_);
lean_dec(v_mkInfo_2824_);
v___x_2827_ = lean_apply_4(v_toBind_2821_, lean_box(0), lean_box(0), v_mkInfoOnError_2822_, v___f_2823_);
return v___x_2827_;
}
else
{
lean_object* v_val_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
lean_dec(v___f_2823_);
lean_dec(v_mkInfoOnError_2822_);
v_val_2828_ = lean_ctor_get(v_a_x3f_2826_, 0);
lean_inc(v_val_2828_);
lean_dec_ref_known(v_a_x3f_2826_, 1);
v___x_2829_ = lean_apply_1(v_mkInfo_2824_, v_val_2828_);
v___x_2830_ = lean_apply_4(v_toBind_2821_, lean_box(0), lean_box(0), v___x_2829_, v___f_2825_);
return v___x_2830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object* v_toApplicative_2831_, lean_object* v_modifyInfoState_2832_, lean_object* v_toBind_2833_, lean_object* v_mkInfoOnError_2834_, lean_object* v_mkInfo_2835_, lean_object* v_inst_2836_, lean_object* v_x_2837_, lean_object* v___f_2838_, lean_object* v_treesSaved_2839_){
_start:
{
lean_object* v_toFunctor_2840_; lean_object* v_toPure_2841_; lean_object* v_map_2842_; lean_object* v___f_2843_; lean_object* v___f_2844_; lean_object* v___f_2845_; lean_object* v___f_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v_toFunctor_2840_ = lean_ctor_get(v_toApplicative_2831_, 0);
lean_inc_ref(v_toFunctor_2840_);
v_toPure_2841_ = lean_ctor_get(v_toApplicative_2831_, 1);
lean_inc(v_toPure_2841_);
lean_dec_ref(v_toApplicative_2831_);
v_map_2842_ = lean_ctor_get(v_toFunctor_2840_, 0);
lean_inc(v_map_2842_);
lean_dec_ref(v_toFunctor_2840_);
v___f_2843_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2843_, 0, v_treesSaved_2839_);
lean_closure_set(v___f_2843_, 1, v_modifyInfoState_2832_);
v___f_2844_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2844_, 0, v___f_2843_);
lean_inc_ref(v___f_2844_);
lean_inc(v_toBind_2833_);
v___f_2845_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_2845_, 0, v_toPure_2841_);
lean_closure_set(v___f_2845_, 1, v_toBind_2833_);
lean_closure_set(v___f_2845_, 2, v___f_2844_);
v___f_2846_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__6), 6, 5);
lean_closure_set(v___f_2846_, 0, v_toBind_2833_);
lean_closure_set(v___f_2846_, 1, v_mkInfoOnError_2834_);
lean_closure_set(v___f_2846_, 2, v___f_2845_);
lean_closure_set(v___f_2846_, 3, v_mkInfo_2835_);
lean_closure_set(v___f_2846_, 4, v___f_2844_);
v___x_2847_ = lean_apply_4(v_inst_2836_, lean_box(0), lean_box(0), v_x_2837_, v___f_2846_);
v___x_2848_ = lean_apply_4(v_map_2842_, lean_box(0), lean_box(0), v___f_2838_, v___x_2847_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object* v_x_2849_, lean_object* v_inst_2850_, lean_object* v_inst_2851_, lean_object* v_toBind_2852_, lean_object* v___f_2853_, lean_object* v_____do__lift_2854_){
_start:
{
uint8_t v_enabled_2855_; 
v_enabled_2855_ = lean_ctor_get_uint8(v_____do__lift_2854_, sizeof(void*)*3);
if (v_enabled_2855_ == 0)
{
lean_dec(v___f_2853_);
lean_dec(v_toBind_2852_);
lean_dec_ref(v_inst_2851_);
lean_dec_ref(v_inst_2850_);
lean_inc(v_x_2849_);
return v_x_2849_;
}
else
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2850_, v_inst_2851_);
v___x_2857_ = lean_apply_4(v_toBind_2852_, lean_box(0), lean_box(0), v___x_2856_, v___f_2853_);
return v___x_2857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object* v_x_2858_, lean_object* v_inst_2859_, lean_object* v_inst_2860_, lean_object* v_toBind_2861_, lean_object* v___f_2862_, lean_object* v_____do__lift_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__7(v_x_2858_, v_inst_2859_, v_inst_2860_, v_toBind_2861_, v___f_2862_, v_____do__lift_2863_);
lean_dec_ref(v_____do__lift_2863_);
lean_dec(v_x_2858_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object* v_inst_2866_, lean_object* v_inst_2867_, lean_object* v_inst_2868_, lean_object* v_x_2869_, lean_object* v_mkInfo_2870_, lean_object* v_mkInfoOnError_2871_){
_start:
{
lean_object* v_toApplicative_2872_; lean_object* v_toBind_2873_; lean_object* v_getInfoState_2874_; lean_object* v_modifyInfoState_2875_; lean_object* v___f_2876_; lean_object* v___f_2877_; lean_object* v___f_2878_; lean_object* v___x_2879_; 
v_toApplicative_2872_ = lean_ctor_get(v_inst_2866_, 0);
v_toBind_2873_ = lean_ctor_get(v_inst_2866_, 1);
lean_inc_n(v_toBind_2873_, 3);
v_getInfoState_2874_ = lean_ctor_get(v_inst_2867_, 0);
lean_inc(v_getInfoState_2874_);
v_modifyInfoState_2875_ = lean_ctor_get(v_inst_2867_, 1);
v___f_2876_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2869_);
lean_inc(v_modifyInfoState_2875_);
lean_inc_ref(v_toApplicative_2872_);
v___f_2877_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__5), 9, 8);
lean_closure_set(v___f_2877_, 0, v_toApplicative_2872_);
lean_closure_set(v___f_2877_, 1, v_modifyInfoState_2875_);
lean_closure_set(v___f_2877_, 2, v_toBind_2873_);
lean_closure_set(v___f_2877_, 3, v_mkInfoOnError_2871_);
lean_closure_set(v___f_2877_, 4, v_mkInfo_2870_);
lean_closure_set(v___f_2877_, 5, v_inst_2868_);
lean_closure_set(v___f_2877_, 6, v_x_2869_);
lean_closure_set(v___f_2877_, 7, v___f_2876_);
v___f_2878_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2878_, 0, v_x_2869_);
lean_closure_set(v___f_2878_, 1, v_inst_2866_);
lean_closure_set(v___f_2878_, 2, v_inst_2867_);
lean_closure_set(v___f_2878_, 3, v_toBind_2873_);
lean_closure_set(v___f_2878_, 4, v___f_2877_);
v___x_2879_ = lean_apply_4(v_toBind_2873_, lean_box(0), lean_box(0), v_getInfoState_2874_, v___f_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* v_m_2880_, lean_object* v_inst_2881_, lean_object* v_inst_2882_, lean_object* v_00_u03b1_2883_, lean_object* v_inst_2884_, lean_object* v_x_2885_, lean_object* v_mkInfo_2886_, lean_object* v_mkInfoOnError_2887_){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Lean_Elab_withInfoContext_x27___redArg(v_inst_2881_, v_inst_2882_, v_inst_2884_, v_x_2885_, v_mkInfo_2886_, v_mkInfoOnError_2887_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object* v_treesSaved_2889_, lean_object* v_tree_2890_, lean_object* v_s_2891_){
_start:
{
uint8_t v_enabled_2892_; lean_object* v_assignment_2893_; lean_object* v_lazyAssignment_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2902_; 
v_enabled_2892_ = lean_ctor_get_uint8(v_s_2891_, sizeof(void*)*3);
v_assignment_2893_ = lean_ctor_get(v_s_2891_, 0);
v_lazyAssignment_2894_ = lean_ctor_get(v_s_2891_, 1);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_s_2891_);
if (v_isSharedCheck_2902_ == 0)
{
lean_object* v_unused_2903_; 
v_unused_2903_ = lean_ctor_get(v_s_2891_, 2);
lean_dec(v_unused_2903_);
v___x_2896_ = v_s_2891_;
v_isShared_2897_ = v_isSharedCheck_2902_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_lazyAssignment_2894_);
lean_inc(v_assignment_2893_);
lean_dec(v_s_2891_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2902_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2898_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2889_, v_tree_2890_);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 2, v___x_2898_);
v___x_2900_ = v___x_2896_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_assignment_2893_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_lazyAssignment_2894_);
lean_ctor_set(v_reuseFailAlloc_2901_, 2, v___x_2898_);
lean_ctor_set_uint8(v_reuseFailAlloc_2901_, sizeof(void*)*3, v_enabled_2892_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object* v_treesSaved_2904_, lean_object* v_modifyInfoState_2905_, lean_object* v_tree_2906_){
_start:
{
lean_object* v___f_2907_; lean_object* v___x_2908_; 
v___f_2907_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2907_, 0, v_treesSaved_2904_);
lean_closure_set(v___f_2907_, 1, v_tree_2906_);
v___x_2908_ = lean_apply_1(v_modifyInfoState_2905_, v___f_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object* v_mkInfoTree_2909_, lean_object* v_toBind_2910_, lean_object* v___f_2911_, lean_object* v_st_2912_){
_start:
{
lean_object* v_trees_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v_trees_2913_ = lean_ctor_get(v_st_2912_, 2);
lean_inc_ref(v_trees_2913_);
lean_dec_ref(v_st_2912_);
v___x_2914_ = lean_apply_1(v_mkInfoTree_2909_, v_trees_2913_);
v___x_2915_ = lean_apply_4(v_toBind_2910_, lean_box(0), lean_box(0), v___x_2914_, v___f_2911_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object* v_toBind_2916_, lean_object* v_getInfoState_2917_, lean_object* v___f_2918_, lean_object* v_x_2919_){
_start:
{
lean_object* v___x_2920_; 
v___x_2920_ = lean_apply_4(v_toBind_2916_, lean_box(0), lean_box(0), v_getInfoState_2917_, v___f_2918_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object* v_toBind_2921_, lean_object* v_getInfoState_2922_, lean_object* v___f_2923_, lean_object* v_x_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(v_toBind_2921_, v_getInfoState_2922_, v___f_2923_, v_x_2924_);
lean_dec(v_x_2924_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object* v_toApplicative_2926_, lean_object* v_modifyInfoState_2927_, lean_object* v_mkInfoTree_2928_, lean_object* v_toBind_2929_, lean_object* v_getInfoState_2930_, lean_object* v_inst_2931_, lean_object* v_x_2932_, lean_object* v___f_2933_, lean_object* v_treesSaved_2934_){
_start:
{
lean_object* v_toFunctor_2935_; lean_object* v_map_2936_; lean_object* v___f_2937_; lean_object* v___f_2938_; lean_object* v___f_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v_toFunctor_2935_ = lean_ctor_get(v_toApplicative_2926_, 0);
lean_inc_ref(v_toFunctor_2935_);
lean_dec_ref(v_toApplicative_2926_);
v_map_2936_ = lean_ctor_get(v_toFunctor_2935_, 0);
lean_inc(v_map_2936_);
lean_dec_ref(v_toFunctor_2935_);
v___f_2937_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2937_, 0, v_treesSaved_2934_);
lean_closure_set(v___f_2937_, 1, v_modifyInfoState_2927_);
lean_inc(v_toBind_2929_);
v___f_2938_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2938_, 0, v_mkInfoTree_2928_);
lean_closure_set(v___f_2938_, 1, v_toBind_2929_);
lean_closure_set(v___f_2938_, 2, v___f_2937_);
v___f_2939_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_2939_, 0, v_toBind_2929_);
lean_closure_set(v___f_2939_, 1, v_getInfoState_2930_);
lean_closure_set(v___f_2939_, 2, v___f_2938_);
v___x_2940_ = lean_apply_4(v_inst_2931_, lean_box(0), lean_box(0), v_x_2932_, v___f_2939_);
v___x_2941_ = lean_apply_4(v_map_2936_, lean_box(0), lean_box(0), v___f_2933_, v___x_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object* v_inst_2942_, lean_object* v_inst_2943_, lean_object* v_inst_2944_, lean_object* v_x_2945_, lean_object* v_mkInfoTree_2946_){
_start:
{
lean_object* v_toApplicative_2947_; lean_object* v_toBind_2948_; lean_object* v_getInfoState_2949_; lean_object* v_modifyInfoState_2950_; lean_object* v___f_2951_; lean_object* v___f_2952_; lean_object* v___f_2953_; lean_object* v___x_2954_; 
v_toApplicative_2947_ = lean_ctor_get(v_inst_2942_, 0);
v_toBind_2948_ = lean_ctor_get(v_inst_2942_, 1);
lean_inc_n(v_toBind_2948_, 3);
v_getInfoState_2949_ = lean_ctor_get(v_inst_2943_, 0);
lean_inc_n(v_getInfoState_2949_, 2);
v_modifyInfoState_2950_ = lean_ctor_get(v_inst_2943_, 1);
v___f_2951_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2945_);
lean_inc(v_modifyInfoState_2950_);
lean_inc_ref(v_toApplicative_2947_);
v___f_2952_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2952_, 0, v_toApplicative_2947_);
lean_closure_set(v___f_2952_, 1, v_modifyInfoState_2950_);
lean_closure_set(v___f_2952_, 2, v_mkInfoTree_2946_);
lean_closure_set(v___f_2952_, 3, v_toBind_2948_);
lean_closure_set(v___f_2952_, 4, v_getInfoState_2949_);
lean_closure_set(v___f_2952_, 5, v_inst_2944_);
lean_closure_set(v___f_2952_, 6, v_x_2945_);
lean_closure_set(v___f_2952_, 7, v___f_2951_);
v___f_2953_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2953_, 0, v_x_2945_);
lean_closure_set(v___f_2953_, 1, v_inst_2942_);
lean_closure_set(v___f_2953_, 2, v_inst_2943_);
lean_closure_set(v___f_2953_, 3, v_toBind_2948_);
lean_closure_set(v___f_2953_, 4, v___f_2952_);
v___x_2954_ = lean_apply_4(v_toBind_2948_, lean_box(0), lean_box(0), v_getInfoState_2949_, v___f_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object* v_m_2955_, lean_object* v_inst_2956_, lean_object* v_inst_2957_, lean_object* v_00_u03b1_2958_, lean_object* v_inst_2959_, lean_object* v_x_2960_, lean_object* v_mkInfoTree_2961_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_2956_, v_inst_2957_, v_inst_2959_, v_x_2960_, v_mkInfoTree_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object* v_trees_2963_, lean_object* v_toPure_2964_, lean_object* v_____do__lift_2965_){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2966_, 0, v_____do__lift_2965_);
lean_ctor_set(v___x_2966_, 1, v_trees_2963_);
v___x_2967_ = lean_apply_2(v_toPure_2964_, lean_box(0), v___x_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object* v_toPure_2968_, lean_object* v_toBind_2969_, lean_object* v_mkInfo_2970_, lean_object* v_trees_2971_){
_start:
{
lean_object* v___f_2972_; lean_object* v___x_2973_; 
v___f_2972_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2972_, 0, v_trees_2971_);
lean_closure_set(v___f_2972_, 1, v_toPure_2968_);
v___x_2973_ = lean_apply_4(v_toBind_2969_, lean_box(0), lean_box(0), v_mkInfo_2970_, v___f_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object* v_inst_2974_, lean_object* v_inst_2975_, lean_object* v_inst_2976_, lean_object* v_x_2977_, lean_object* v_mkInfo_2978_){
_start:
{
lean_object* v_toApplicative_2979_; lean_object* v_toBind_2980_; lean_object* v_toPure_2981_; lean_object* v___f_2982_; lean_object* v___x_2983_; 
v_toApplicative_2979_ = lean_ctor_get(v_inst_2974_, 0);
v_toBind_2980_ = lean_ctor_get(v_inst_2974_, 1);
v_toPure_2981_ = lean_ctor_get(v_toApplicative_2979_, 1);
lean_inc(v_toBind_2980_);
lean_inc(v_toPure_2981_);
v___f_2982_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2982_, 0, v_toPure_2981_);
lean_closure_set(v___f_2982_, 1, v_toBind_2980_);
lean_closure_set(v___f_2982_, 2, v_mkInfo_2978_);
v___x_2983_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_2974_, v_inst_2975_, v_inst_2976_, v_x_2977_, v___f_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object* v_m_2984_, lean_object* v_inst_2985_, lean_object* v_inst_2986_, lean_object* v_00_u03b1_2987_, lean_object* v_inst_2988_, lean_object* v_x_2989_, lean_object* v_mkInfo_2990_){
_start:
{
lean_object* v_toApplicative_2991_; lean_object* v_toBind_2992_; lean_object* v_toPure_2993_; lean_object* v___f_2994_; lean_object* v___x_2995_; 
v_toApplicative_2991_ = lean_ctor_get(v_inst_2985_, 0);
v_toBind_2992_ = lean_ctor_get(v_inst_2985_, 1);
v_toPure_2993_ = lean_ctor_get(v_toApplicative_2991_, 1);
lean_inc(v_toBind_2992_);
lean_inc(v_toPure_2993_);
v___f_2994_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2994_, 0, v_toPure_2993_);
lean_closure_set(v___f_2994_, 1, v_toBind_2992_);
lean_closure_set(v___f_2994_, 2, v_mkInfo_2990_);
v___x_2995_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_2985_, v_inst_2986_, v_inst_2988_, v_x_2989_, v___f_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object* v_treesSaved_2996_, lean_object* v_trees_2997_, lean_object* v_s_2998_){
_start:
{
uint8_t v_enabled_2999_; lean_object* v_assignment_3000_; lean_object* v_lazyAssignment_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3009_; 
v_enabled_2999_ = lean_ctor_get_uint8(v_s_2998_, sizeof(void*)*3);
v_assignment_3000_ = lean_ctor_get(v_s_2998_, 0);
v_lazyAssignment_3001_ = lean_ctor_get(v_s_2998_, 1);
v_isSharedCheck_3009_ = !lean_is_exclusive(v_s_2998_);
if (v_isSharedCheck_3009_ == 0)
{
lean_object* v_unused_3010_; 
v_unused_3010_ = lean_ctor_get(v_s_2998_, 2);
lean_dec(v_unused_3010_);
v___x_3003_ = v_s_2998_;
v_isShared_3004_ = v_isSharedCheck_3009_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_lazyAssignment_3001_);
lean_inc(v_assignment_3000_);
lean_dec(v_s_2998_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3009_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3005_; lean_object* v___x_3007_; 
v___x_3005_ = l_Lean_PersistentArray_append___redArg(v_treesSaved_2996_, v_trees_2997_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 2, v___x_3005_);
v___x_3007_ = v___x_3003_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_assignment_3000_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v_lazyAssignment_3001_);
lean_ctor_set(v_reuseFailAlloc_3008_, 2, v___x_3005_);
lean_ctor_set_uint8(v_reuseFailAlloc_3008_, sizeof(void*)*3, v_enabled_2999_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object* v_treesSaved_3011_, lean_object* v_trees_3012_, lean_object* v_s_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_3011_, v_trees_3012_, v_s_3013_);
lean_dec_ref(v_trees_3012_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object* v_treesSaved_3015_, lean_object* v_modifyInfoState_3016_, lean_object* v_trees_3017_){
_start:
{
lean_object* v___f_3018_; lean_object* v___x_3019_; 
v___f_3018_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3018_, 0, v_treesSaved_3015_);
lean_closure_set(v___f_3018_, 1, v_trees_3017_);
v___x_3019_ = lean_apply_1(v_modifyInfoState_3016_, v___f_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object* v_toPure_3020_, lean_object* v_tree_3021_, lean_object* v_____do__lift_3022_){
_start:
{
if (lean_obj_tag(v_____do__lift_3022_) == 0)
{
lean_object* v___x_3023_; 
v___x_3023_ = lean_apply_2(v_toPure_3020_, lean_box(0), v_tree_3021_);
return v___x_3023_;
}
else
{
lean_object* v_val_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v_val_3024_ = lean_ctor_get(v_____do__lift_3022_, 0);
lean_inc(v_val_3024_);
v___x_3025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3025_, 0, v_val_3024_);
lean_ctor_set(v___x_3025_, 1, v_tree_3021_);
v___x_3026_ = lean_apply_2(v_toPure_3020_, lean_box(0), v___x_3025_);
return v___x_3026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object* v_toPure_3027_, lean_object* v_tree_3028_, lean_object* v_____do__lift_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_3027_, v_tree_3028_, v_____do__lift_3029_);
lean_dec(v_____do__lift_3029_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object* v_assignment_3031_, lean_object* v_toPure_3032_, lean_object* v_toBind_3033_, lean_object* v_ctx_x3f_3034_, lean_object* v_tree_3035_){
_start:
{
lean_object* v_tree_3036_; lean_object* v___f_3037_; lean_object* v___x_3038_; 
v_tree_3036_ = l_Lean_Elab_InfoTree_substitute(v_tree_3035_, v_assignment_3031_);
v___f_3037_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3037_, 0, v_toPure_3032_);
lean_closure_set(v___f_3037_, 1, v_tree_3036_);
v___x_3038_ = lean_apply_4(v_toBind_3033_, lean_box(0), lean_box(0), v_ctx_x3f_3034_, v___f_3037_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object* v_assignment_3039_, lean_object* v_toPure_3040_, lean_object* v_toBind_3041_, lean_object* v_ctx_x3f_3042_, lean_object* v_tree_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(v_assignment_3039_, v_toPure_3040_, v_toBind_3041_, v_ctx_x3f_3042_, v_tree_3043_);
lean_dec_ref(v_assignment_3039_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object* v_toPure_3045_, lean_object* v_toBind_3046_, lean_object* v_ctx_x3f_3047_, lean_object* v_inst_3048_, lean_object* v___f_3049_, lean_object* v_st_3050_){
_start:
{
lean_object* v_assignment_3051_; lean_object* v_trees_3052_; lean_object* v___f_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v_assignment_3051_ = lean_ctor_get(v_st_3050_, 0);
lean_inc_ref(v_assignment_3051_);
v_trees_3052_ = lean_ctor_get(v_st_3050_, 2);
lean_inc_ref(v_trees_3052_);
lean_dec_ref(v_st_3050_);
lean_inc(v_toBind_3046_);
v___f_3053_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_3053_, 0, v_assignment_3051_);
lean_closure_set(v___f_3053_, 1, v_toPure_3045_);
lean_closure_set(v___f_3053_, 2, v_toBind_3046_);
lean_closure_set(v___f_3053_, 3, v_ctx_x3f_3047_);
v___x_3054_ = l_Lean_PersistentArray_mapM___redArg(v_inst_3048_, v___f_3053_, v_trees_3052_);
v___x_3055_ = lean_apply_4(v_toBind_3046_, lean_box(0), lean_box(0), v___x_3054_, v___f_3049_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object* v_toApplicative_3056_, lean_object* v_modifyInfoState_3057_, lean_object* v_toBind_3058_, lean_object* v_ctx_x3f_3059_, lean_object* v_inst_3060_, lean_object* v_getInfoState_3061_, lean_object* v_inst_3062_, lean_object* v_x_3063_, lean_object* v___f_3064_, lean_object* v_treesSaved_3065_){
_start:
{
lean_object* v_toFunctor_3066_; lean_object* v_toPure_3067_; lean_object* v_map_3068_; lean_object* v___f_3069_; lean_object* v___f_3070_; lean_object* v___f_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v_toFunctor_3066_ = lean_ctor_get(v_toApplicative_3056_, 0);
lean_inc_ref(v_toFunctor_3066_);
v_toPure_3067_ = lean_ctor_get(v_toApplicative_3056_, 1);
lean_inc(v_toPure_3067_);
lean_dec_ref(v_toApplicative_3056_);
v_map_3068_ = lean_ctor_get(v_toFunctor_3066_, 0);
lean_inc(v_map_3068_);
lean_dec_ref(v_toFunctor_3066_);
v___f_3069_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3069_, 0, v_treesSaved_3065_);
lean_closure_set(v___f_3069_, 1, v_modifyInfoState_3057_);
lean_inc(v_toBind_3058_);
v___f_3070_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4), 6, 5);
lean_closure_set(v___f_3070_, 0, v_toPure_3067_);
lean_closure_set(v___f_3070_, 1, v_toBind_3058_);
lean_closure_set(v___f_3070_, 2, v_ctx_x3f_3059_);
lean_closure_set(v___f_3070_, 3, v_inst_3060_);
lean_closure_set(v___f_3070_, 4, v___f_3069_);
v___f_3071_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3071_, 0, v_toBind_3058_);
lean_closure_set(v___f_3071_, 1, v_getInfoState_3061_);
lean_closure_set(v___f_3071_, 2, v___f_3070_);
v___x_3072_ = lean_apply_4(v_inst_3062_, lean_box(0), lean_box(0), v_x_3063_, v___f_3071_);
v___x_3073_ = lean_apply_4(v_map_3068_, lean_box(0), lean_box(0), v___f_3064_, v___x_3072_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__5(lean_object* v_inst_3074_, lean_object* v_inst_3075_, lean_object* v_toBind_3076_, lean_object* v___f_3077_, lean_object* v_x_3078_, lean_object* v_____do__lift_3079_){
_start:
{
uint8_t v_enabled_3080_; uint8_t v___x_3081_; 
v_enabled_3080_ = lean_ctor_get_uint8(v_____do__lift_3079_, sizeof(void*)*3);
v___x_3081_ = lean_bool_not(v_enabled_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_3074_, v_inst_3075_);
v___x_3083_ = lean_apply_4(v_toBind_3076_, lean_box(0), lean_box(0), v___x_3082_, v___f_3077_);
return v___x_3083_;
}
else
{
lean_dec(v___f_3077_);
lean_dec(v_toBind_3076_);
lean_dec_ref(v_inst_3075_);
lean_dec_ref(v_inst_3074_);
lean_inc(v_x_3078_);
return v_x_3078_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__5___boxed(lean_object* v_inst_3084_, lean_object* v_inst_3085_, lean_object* v_toBind_3086_, lean_object* v___f_3087_, lean_object* v_x_3088_, lean_object* v_____do__lift_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__5(v_inst_3084_, v_inst_3085_, v_toBind_3086_, v___f_3087_, v_x_3088_, v_____do__lift_3089_);
lean_dec_ref(v_____do__lift_3089_);
lean_dec(v_x_3088_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object* v_inst_3091_, lean_object* v_inst_3092_, lean_object* v_inst_3093_, lean_object* v_x_3094_, lean_object* v_ctx_x3f_3095_){
_start:
{
lean_object* v_toApplicative_3096_; lean_object* v_toBind_3097_; lean_object* v_getInfoState_3098_; lean_object* v_modifyInfoState_3099_; lean_object* v___f_3100_; lean_object* v___f_3101_; lean_object* v___f_3102_; lean_object* v___x_3103_; 
v_toApplicative_3096_ = lean_ctor_get(v_inst_3091_, 0);
v_toBind_3097_ = lean_ctor_get(v_inst_3091_, 1);
lean_inc_n(v_toBind_3097_, 3);
v_getInfoState_3098_ = lean_ctor_get(v_inst_3092_, 0);
lean_inc_n(v_getInfoState_3098_, 2);
v_modifyInfoState_3099_ = lean_ctor_get(v_inst_3092_, 1);
v___f_3100_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3094_);
lean_inc_ref(v_inst_3091_);
lean_inc(v_modifyInfoState_3099_);
lean_inc_ref(v_toApplicative_3096_);
v___f_3101_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6), 10, 9);
lean_closure_set(v___f_3101_, 0, v_toApplicative_3096_);
lean_closure_set(v___f_3101_, 1, v_modifyInfoState_3099_);
lean_closure_set(v___f_3101_, 2, v_toBind_3097_);
lean_closure_set(v___f_3101_, 3, v_ctx_x3f_3095_);
lean_closure_set(v___f_3101_, 4, v_inst_3091_);
lean_closure_set(v___f_3101_, 5, v_getInfoState_3098_);
lean_closure_set(v___f_3101_, 6, v_inst_3093_);
lean_closure_set(v___f_3101_, 7, v_x_3094_);
lean_closure_set(v___f_3101_, 8, v___f_3100_);
v___f_3102_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_3102_, 0, v_inst_3091_);
lean_closure_set(v___f_3102_, 1, v_inst_3092_);
lean_closure_set(v___f_3102_, 2, v_toBind_3097_);
lean_closure_set(v___f_3102_, 3, v___f_3101_);
lean_closure_set(v___f_3102_, 4, v_x_3094_);
v___x_3103_ = lean_apply_4(v_toBind_3097_, lean_box(0), lean_box(0), v_getInfoState_3098_, v___f_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object* v_m_3104_, lean_object* v_inst_3105_, lean_object* v_inst_3106_, lean_object* v_00_u03b1_3107_, lean_object* v_inst_3108_, lean_object* v_x_3109_, lean_object* v_ctx_x3f_3110_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3105_, v_inst_3106_, v_inst_3108_, v_x_3109_, v_ctx_x3f_3110_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object* v_toPure_3112_, lean_object* v_____do__lift_3113_){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3114_, 0, v_____do__lift_3113_);
v___x_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
v___x_3116_ = lean_apply_2(v_toPure_3112_, lean_box(0), v___x_3115_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object* v_inst_3117_, lean_object* v_inst_3118_, lean_object* v_inst_3119_, lean_object* v_inst_3120_, lean_object* v_inst_3121_, lean_object* v_inst_3122_, lean_object* v_inst_3123_, lean_object* v_inst_3124_, lean_object* v_inst_3125_, lean_object* v_x_3126_){
_start:
{
lean_object* v_toApplicative_3127_; lean_object* v_toBind_3128_; lean_object* v_toPure_3129_; lean_object* v___x_3130_; lean_object* v___f_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v_toApplicative_3127_ = lean_ctor_get(v_inst_3117_, 0);
v_toBind_3128_ = lean_ctor_get(v_inst_3117_, 1);
v_toPure_3129_ = lean_ctor_get(v_toApplicative_3127_, 1);
lean_inc_ref(v_inst_3117_);
v___x_3130_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_3117_, v_inst_3121_, v_inst_3123_, v_inst_3122_, v_inst_3124_, v_inst_3119_, v_inst_3125_);
lean_inc(v_toPure_3129_);
v___f_3131_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3131_, 0, v_toPure_3129_);
lean_inc(v_toBind_3128_);
v___x_3132_ = lean_apply_4(v_toBind_3128_, lean_box(0), lean_box(0), v___x_3130_, v___f_3131_);
v___x_3133_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3117_, v_inst_3118_, v_inst_3120_, v_x_3126_, v___x_3132_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object* v_m_3134_, lean_object* v_inst_3135_, lean_object* v_inst_3136_, lean_object* v_00_u03b1_3137_, lean_object* v_inst_3138_, lean_object* v_inst_3139_, lean_object* v_inst_3140_, lean_object* v_inst_3141_, lean_object* v_inst_3142_, lean_object* v_inst_3143_, lean_object* v_inst_3144_, lean_object* v_x_3145_){
_start:
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Lean_Elab_withSaveInfoContext___redArg(v_inst_3135_, v_inst_3136_, v_inst_3138_, v_inst_3139_, v_inst_3140_, v_inst_3141_, v_inst_3142_, v_inst_3143_, v_inst_3144_, v_x_3145_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object* v_toPure_3147_, lean_object* v_____x_3148_){
_start:
{
if (lean_obj_tag(v_____x_3148_) == 1)
{
lean_object* v_val_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3158_; 
v_val_3149_ = lean_ctor_get(v_____x_3148_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v_____x_3148_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3151_ = v_____x_3148_;
v_isShared_3152_ = v_isSharedCheck_3158_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_val_3149_);
lean_dec(v_____x_3148_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3158_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3153_; lean_object* v___x_3155_; 
v___x_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3153_, 0, v_val_3149_);
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 0, v___x_3153_);
v___x_3155_ = v___x_3151_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3153_);
v___x_3155_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v___x_3156_; 
v___x_3156_ = lean_apply_2(v_toPure_3147_, lean_box(0), v___x_3155_);
return v___x_3156_;
}
}
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
lean_dec(v_____x_3148_);
v___x_3159_ = lean_box(0);
v___x_3160_ = lean_apply_2(v_toPure_3147_, lean_box(0), v___x_3159_);
return v___x_3160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object* v_inst_3161_, lean_object* v_inst_3162_, lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_x_3165_){
_start:
{
lean_object* v_toApplicative_3166_; lean_object* v_toBind_3167_; lean_object* v_toPure_3168_; lean_object* v___f_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v_toApplicative_3166_ = lean_ctor_get(v_inst_3161_, 0);
v_toBind_3167_ = lean_ctor_get(v_inst_3161_, 1);
v_toPure_3168_ = lean_ctor_get(v_toApplicative_3166_, 1);
lean_inc(v_toPure_3168_);
v___f_3169_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3169_, 0, v_toPure_3168_);
lean_inc(v_toBind_3167_);
v___x_3170_ = lean_apply_4(v_toBind_3167_, lean_box(0), lean_box(0), v_inst_3164_, v___f_3169_);
v___x_3171_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3161_, v_inst_3162_, v_inst_3163_, v_x_3165_, v___x_3170_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object* v_m_3172_, lean_object* v_inst_3173_, lean_object* v_inst_3174_, lean_object* v_00_u03b1_3175_, lean_object* v_inst_3176_, lean_object* v_inst_3177_, lean_object* v_x_3178_){
_start:
{
lean_object* v___x_3179_; 
v___x_3179_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(v_inst_3173_, v_inst_3174_, v_inst_3176_, v_inst_3177_, v_x_3178_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object* v_toPure_3180_, lean_object* v_autoImplicits_3181_){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3182_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3182_, 0, v_autoImplicits_3181_);
v___x_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
v___x_3184_ = lean_apply_2(v_toPure_3180_, lean_box(0), v___x_3183_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object* v_inst_3185_, lean_object* v_inst_3186_, lean_object* v_inst_3187_, lean_object* v_inst_3188_, lean_object* v_x_3189_){
_start:
{
lean_object* v_toApplicative_3190_; lean_object* v_toBind_3191_; lean_object* v_toPure_3192_; lean_object* v___f_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v_toApplicative_3190_ = lean_ctor_get(v_inst_3185_, 0);
v_toBind_3191_ = lean_ctor_get(v_inst_3185_, 1);
v_toPure_3192_ = lean_ctor_get(v_toApplicative_3190_, 1);
lean_inc(v_toPure_3192_);
v___f_3193_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3193_, 0, v_toPure_3192_);
lean_inc(v_toBind_3191_);
v___x_3194_ = lean_apply_4(v_toBind_3191_, lean_box(0), lean_box(0), v_inst_3188_, v___f_3193_);
v___x_3195_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3185_, v_inst_3186_, v_inst_3187_, v_x_3189_, v___x_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object* v_m_3196_, lean_object* v_inst_3197_, lean_object* v_inst_3198_, lean_object* v_00_u03b1_3199_, lean_object* v_inst_3200_, lean_object* v_inst_3201_, lean_object* v_x_3202_){
_start:
{
lean_object* v___x_3203_; 
v___x_3203_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(v_inst_3197_, v_inst_3198_, v_inst_3200_, v_inst_3201_, v_x_3202_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object* v___x_3204_, lean_object* v___x_3205_, lean_object* v_mvarId_3206_, lean_object* v_toPure_3207_, lean_object* v_____do__lift_3208_){
_start:
{
lean_object* v_assignment_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v_assignment_3209_ = lean_ctor_get(v_____do__lift_3208_, 0);
v___x_3210_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_3204_, v___x_3205_, v_assignment_3209_, v_mvarId_3206_);
v___x_3211_ = lean_apply_2(v_toPure_3207_, lean_box(0), v___x_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object* v___x_3212_, lean_object* v___x_3213_, lean_object* v_mvarId_3214_, lean_object* v_toPure_3215_, lean_object* v_____do__lift_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(v___x_3212_, v___x_3213_, v_mvarId_3214_, v_toPure_3215_, v_____do__lift_3216_);
lean_dec_ref(v_____do__lift_3216_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object* v_inst_3220_, lean_object* v_inst_3221_, lean_object* v_mvarId_3222_){
_start:
{
lean_object* v_toApplicative_3223_; lean_object* v_toBind_3224_; lean_object* v_getInfoState_3225_; lean_object* v_toPure_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___f_3229_; lean_object* v___x_3230_; 
v_toApplicative_3223_ = lean_ctor_get(v_inst_3220_, 0);
lean_inc_ref(v_toApplicative_3223_);
v_toBind_3224_ = lean_ctor_get(v_inst_3220_, 1);
lean_inc(v_toBind_3224_);
lean_dec_ref(v_inst_3220_);
v_getInfoState_3225_ = lean_ctor_get(v_inst_3221_, 0);
lean_inc(v_getInfoState_3225_);
lean_dec_ref(v_inst_3221_);
v_toPure_3226_ = lean_ctor_get(v_toApplicative_3223_, 1);
lean_inc(v_toPure_3226_);
lean_dec_ref(v_toApplicative_3223_);
v___x_3227_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3228_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___f_3229_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3229_, 0, v___x_3227_);
lean_closure_set(v___f_3229_, 1, v___x_3228_);
lean_closure_set(v___f_3229_, 2, v_mvarId_3222_);
lean_closure_set(v___f_3229_, 3, v_toPure_3226_);
v___x_3230_ = lean_apply_4(v_toBind_3224_, lean_box(0), lean_box(0), v_getInfoState_3225_, v___f_3229_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* v_m_3231_, lean_object* v_inst_3232_, lean_object* v_inst_3233_, lean_object* v_mvarId_3234_){
_start:
{
lean_object* v___x_3235_; 
v___x_3235_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3232_, v_inst_3233_, v_mvarId_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object* v_mvarId_3236_, lean_object* v_infoTree_3237_, lean_object* v_s_3238_){
_start:
{
uint8_t v_enabled_3239_; lean_object* v_assignment_3240_; lean_object* v_lazyAssignment_3241_; lean_object* v_trees_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3252_; 
v_enabled_3239_ = lean_ctor_get_uint8(v_s_3238_, sizeof(void*)*3);
v_assignment_3240_ = lean_ctor_get(v_s_3238_, 0);
v_lazyAssignment_3241_ = lean_ctor_get(v_s_3238_, 1);
v_trees_3242_ = lean_ctor_get(v_s_3238_, 2);
v_isSharedCheck_3252_ = !lean_is_exclusive(v_s_3238_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3244_ = v_s_3238_;
v_isShared_3245_ = v_isSharedCheck_3252_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_trees_3242_);
lean_inc(v_lazyAssignment_3241_);
lean_inc(v_assignment_3240_);
lean_dec(v_s_3238_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3252_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3250_; 
v___x_3246_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3247_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3248_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3246_, v___x_3247_, v_assignment_3240_, v_mvarId_3236_, v_infoTree_3237_);
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 0, v___x_3248_);
v___x_3250_ = v___x_3244_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
lean_ctor_set(v_reuseFailAlloc_3251_, 1, v_lazyAssignment_3241_);
lean_ctor_set(v_reuseFailAlloc_3251_, 2, v_trees_3242_);
lean_ctor_set_uint8(v_reuseFailAlloc_3251_, sizeof(void*)*3, v_enabled_3239_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3256_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2));
v___x_3257_ = lean_unsigned_to_nat(2u);
v___x_3258_ = lean_unsigned_to_nat(380u);
v___x_3259_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1));
v___x_3260_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0));
v___x_3261_ = l_mkPanicMessageWithDecl(v___x_3260_, v___x_3259_, v___x_3258_, v___x_3257_, v___x_3256_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object* v_inst_3262_, lean_object* v___f_3263_, lean_object* v_inst_3264_, lean_object* v_____do__lift_3265_){
_start:
{
if (lean_obj_tag(v_____do__lift_3265_) == 0)
{
lean_object* v_modifyInfoState_3266_; lean_object* v___x_3267_; 
lean_dec_ref(v_inst_3264_);
v_modifyInfoState_3266_ = lean_ctor_get(v_inst_3262_, 1);
lean_inc(v_modifyInfoState_3266_);
lean_dec_ref(v_inst_3262_);
v___x_3267_ = lean_apply_1(v_modifyInfoState_3266_, v___f_3263_);
return v___x_3267_;
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
lean_dec_ref(v___f_3263_);
lean_dec_ref(v_inst_3262_);
v___x_3268_ = lean_box(0);
v___x_3269_ = l_instInhabitedOfMonad___redArg(v_inst_3264_, v___x_3268_);
v___x_3270_ = lean_obj_once(&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3, &l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3_once, _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3);
v___x_3271_ = l_panic___redArg(v___x_3269_, v___x_3270_);
lean_dec(v___x_3269_);
return v___x_3271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object* v_inst_3272_, lean_object* v___f_3273_, lean_object* v_inst_3274_, lean_object* v_____do__lift_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(v_inst_3272_, v___f_3273_, v_inst_3274_, v_____do__lift_3275_);
lean_dec(v_____do__lift_3275_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object* v_inst_3277_, lean_object* v_inst_3278_, lean_object* v_mvarId_3279_, lean_object* v_infoTree_3280_){
_start:
{
lean_object* v_toBind_3281_; lean_object* v___f_3282_; lean_object* v___f_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v_toBind_3281_ = lean_ctor_get(v_inst_3277_, 1);
lean_inc(v_toBind_3281_);
lean_inc(v_mvarId_3279_);
v___f_3282_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3282_, 0, v_mvarId_3279_);
lean_closure_set(v___f_3282_, 1, v_infoTree_3280_);
lean_inc_ref(v_inst_3277_);
lean_inc_ref(v_inst_3278_);
v___f_3283_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3283_, 0, v_inst_3278_);
lean_closure_set(v___f_3283_, 1, v___f_3282_);
lean_closure_set(v___f_3283_, 2, v_inst_3277_);
v___x_3284_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3277_, v_inst_3278_, v_mvarId_3279_);
v___x_3285_ = lean_apply_4(v_toBind_3281_, lean_box(0), lean_box(0), v___x_3284_, v___f_3283_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* v_m_3286_, lean_object* v_inst_3287_, lean_object* v_inst_3288_, lean_object* v_mvarId_3289_, lean_object* v_infoTree_3290_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l_Lean_Elab_assignInfoHoleId___redArg(v_inst_3287_, v_inst_3288_, v_mvarId_3289_, v_infoTree_3290_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object* v_stx_3292_, lean_object* v_output_3293_, lean_object* v_toPure_3294_, lean_object* v_____do__lift_3295_){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3296_, 0, v_____do__lift_3295_);
lean_ctor_set(v___x_3296_, 1, v_stx_3292_);
lean_ctor_set(v___x_3296_, 2, v_output_3293_);
v___x_3297_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
v___x_3298_ = lean_apply_2(v_toPure_3294_, lean_box(0), v___x_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object* v_inst_3299_, lean_object* v_inst_3300_, lean_object* v_inst_3301_, lean_object* v_inst_3302_, lean_object* v_stx_3303_, lean_object* v_output_3304_, lean_object* v_x_3305_){
_start:
{
lean_object* v_toApplicative_3306_; lean_object* v_toBind_3307_; lean_object* v_toPure_3308_; lean_object* v___f_3309_; lean_object* v_mkInfo_3310_; lean_object* v___f_3311_; lean_object* v___x_3312_; 
v_toApplicative_3306_ = lean_ctor_get(v_inst_3300_, 0);
v_toBind_3307_ = lean_ctor_get(v_inst_3300_, 1);
v_toPure_3308_ = lean_ctor_get(v_toApplicative_3306_, 1);
lean_inc_n(v_toPure_3308_, 2);
v___f_3309_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3309_, 0, v_stx_3303_);
lean_closure_set(v___f_3309_, 1, v_output_3304_);
lean_closure_set(v___f_3309_, 2, v_toPure_3308_);
lean_inc_n(v_toBind_3307_, 2);
v_mkInfo_3310_ = lean_apply_4(v_toBind_3307_, lean_box(0), lean_box(0), v_inst_3302_, v___f_3309_);
v___f_3311_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3311_, 0, v_toPure_3308_);
lean_closure_set(v___f_3311_, 1, v_toBind_3307_);
lean_closure_set(v___f_3311_, 2, v_mkInfo_3310_);
v___x_3312_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3300_, v_inst_3301_, v_inst_3299_, v_x_3305_, v___f_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* v_m_3313_, lean_object* v_00_u03b1_3314_, lean_object* v_inst_3315_, lean_object* v_inst_3316_, lean_object* v_inst_3317_, lean_object* v_inst_3318_, lean_object* v_stx_3319_, lean_object* v_output_3320_, lean_object* v_x_3321_){
_start:
{
lean_object* v___x_3322_; 
v___x_3322_ = l_Lean_Elab_withMacroExpansionInfo___redArg(v_inst_3315_, v_inst_3316_, v_inst_3317_, v_inst_3318_, v_stx_3319_, v_output_3320_, v_x_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object* v_treesSaved_3323_, lean_object* v_mvarId_3324_, lean_object* v_s_3325_){
_start:
{
lean_object* v_trees_3326_; uint8_t v_enabled_3327_; lean_object* v_assignment_3328_; lean_object* v_lazyAssignment_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3349_; 
v_trees_3326_ = lean_ctor_get(v_s_3325_, 2);
v_enabled_3327_ = lean_ctor_get_uint8(v_s_3325_, sizeof(void*)*3);
v_assignment_3328_ = lean_ctor_get(v_s_3325_, 0);
v_lazyAssignment_3329_ = lean_ctor_get(v_s_3325_, 1);
v_isSharedCheck_3349_ = !lean_is_exclusive(v_s_3325_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3331_ = v_s_3325_;
v_isShared_3332_ = v_isSharedCheck_3349_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_trees_3326_);
lean_inc(v_lazyAssignment_3329_);
lean_inc(v_assignment_3328_);
lean_dec(v_s_3325_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3349_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v_size_3333_; lean_object* v___x_3334_; uint8_t v___x_3335_; 
v_size_3333_ = lean_ctor_get(v_trees_3326_, 2);
v___x_3334_ = lean_unsigned_to_nat(0u);
v___x_3335_ = lean_nat_dec_lt(v___x_3334_, v_size_3333_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3337_; 
lean_dec_ref(v_trees_3326_);
lean_dec(v_mvarId_3324_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 2, v_treesSaved_3323_);
v___x_3337_ = v___x_3331_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_assignment_3328_);
lean_ctor_set(v_reuseFailAlloc_3338_, 1, v_lazyAssignment_3329_);
lean_ctor_set(v_reuseFailAlloc_3338_, 2, v_treesSaved_3323_);
lean_ctor_set_uint8(v_reuseFailAlloc_3338_, sizeof(void*)*3, v_enabled_3327_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3347_; 
v___x_3339_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3340_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3341_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_3342_ = lean_unsigned_to_nat(1u);
v___x_3343_ = lean_nat_sub(v_size_3333_, v___x_3342_);
v___x_3344_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3341_, v_trees_3326_, v___x_3343_);
lean_dec(v___x_3343_);
lean_dec_ref(v_trees_3326_);
v___x_3345_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3339_, v___x_3340_, v_assignment_3328_, v_mvarId_3324_, v___x_3344_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 2, v_treesSaved_3323_);
lean_ctor_set(v___x_3331_, 0, v___x_3345_);
v___x_3347_ = v___x_3331_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3345_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v_lazyAssignment_3329_);
lean_ctor_set(v_reuseFailAlloc_3348_, 2, v_treesSaved_3323_);
lean_ctor_set_uint8(v_reuseFailAlloc_3348_, sizeof(void*)*3, v_enabled_3327_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object* v_modifyInfoState_3350_, lean_object* v___f_3351_, lean_object* v_x_3352_){
_start:
{
lean_object* v___x_3353_; 
v___x_3353_ = lean_apply_1(v_modifyInfoState_3350_, v___f_3351_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object* v_modifyInfoState_3354_, lean_object* v___f_3355_, lean_object* v_x_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_3354_, v___f_3355_, v_x_3356_);
lean_dec(v_x_3356_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object* v_toApplicative_3358_, lean_object* v_mvarId_3359_, lean_object* v_modifyInfoState_3360_, lean_object* v_inst_3361_, lean_object* v_x_3362_, lean_object* v___f_3363_, lean_object* v_treesSaved_3364_){
_start:
{
lean_object* v_toFunctor_3365_; lean_object* v_map_3366_; lean_object* v___f_3367_; lean_object* v___f_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v_toFunctor_3365_ = lean_ctor_get(v_toApplicative_3358_, 0);
lean_inc_ref(v_toFunctor_3365_);
lean_dec_ref(v_toApplicative_3358_);
v_map_3366_ = lean_ctor_get(v_toFunctor_3365_, 0);
lean_inc(v_map_3366_);
lean_dec_ref(v_toFunctor_3365_);
v___f_3367_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3367_, 0, v_treesSaved_3364_);
lean_closure_set(v___f_3367_, 1, v_mvarId_3359_);
v___f_3368_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3368_, 0, v_modifyInfoState_3360_);
lean_closure_set(v___f_3368_, 1, v___f_3367_);
v___x_3369_ = lean_apply_4(v_inst_3361_, lean_box(0), lean_box(0), v_x_3362_, v___f_3368_);
v___x_3370_ = lean_apply_4(v_map_3366_, lean_box(0), lean_box(0), v___f_3363_, v___x_3369_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object* v_inst_3371_, lean_object* v_inst_3372_, lean_object* v_inst_3373_, lean_object* v_mvarId_3374_, lean_object* v_x_3375_){
_start:
{
lean_object* v_toApplicative_3376_; lean_object* v_toBind_3377_; lean_object* v_getInfoState_3378_; lean_object* v_modifyInfoState_3379_; lean_object* v___f_3380_; lean_object* v___f_3381_; lean_object* v___f_3382_; lean_object* v___x_3383_; 
v_toApplicative_3376_ = lean_ctor_get(v_inst_3372_, 0);
v_toBind_3377_ = lean_ctor_get(v_inst_3372_, 1);
lean_inc_n(v_toBind_3377_, 2);
v_getInfoState_3378_ = lean_ctor_get(v_inst_3373_, 0);
lean_inc(v_getInfoState_3378_);
v_modifyInfoState_3379_ = lean_ctor_get(v_inst_3373_, 1);
v___f_3380_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3375_);
lean_inc(v_modifyInfoState_3379_);
lean_inc_ref(v_toApplicative_3376_);
v___f_3381_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 7, 6);
lean_closure_set(v___f_3381_, 0, v_toApplicative_3376_);
lean_closure_set(v___f_3381_, 1, v_mvarId_3374_);
lean_closure_set(v___f_3381_, 2, v_modifyInfoState_3379_);
lean_closure_set(v___f_3381_, 3, v_inst_3371_);
lean_closure_set(v___f_3381_, 4, v_x_3375_);
lean_closure_set(v___f_3381_, 5, v___f_3380_);
v___f_3382_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3382_, 0, v_x_3375_);
lean_closure_set(v___f_3382_, 1, v_inst_3372_);
lean_closure_set(v___f_3382_, 2, v_inst_3373_);
lean_closure_set(v___f_3382_, 3, v_toBind_3377_);
lean_closure_set(v___f_3382_, 4, v___f_3381_);
v___x_3383_ = lean_apply_4(v_toBind_3377_, lean_box(0), lean_box(0), v_getInfoState_3378_, v___f_3382_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object* v_m_3384_, lean_object* v_00_u03b1_3385_, lean_object* v_inst_3386_, lean_object* v_inst_3387_, lean_object* v_inst_3388_, lean_object* v_mvarId_3389_, lean_object* v_x_3390_){
_start:
{
lean_object* v_toApplicative_3391_; lean_object* v_toBind_3392_; lean_object* v_getInfoState_3393_; lean_object* v_modifyInfoState_3394_; lean_object* v___f_3395_; lean_object* v___f_3396_; lean_object* v___f_3397_; lean_object* v___x_3398_; 
v_toApplicative_3391_ = lean_ctor_get(v_inst_3387_, 0);
v_toBind_3392_ = lean_ctor_get(v_inst_3387_, 1);
lean_inc_n(v_toBind_3392_, 2);
v_getInfoState_3393_ = lean_ctor_get(v_inst_3388_, 0);
lean_inc(v_getInfoState_3393_);
v_modifyInfoState_3394_ = lean_ctor_get(v_inst_3388_, 1);
v___f_3395_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3390_);
lean_inc(v_modifyInfoState_3394_);
lean_inc_ref(v_toApplicative_3391_);
v___f_3396_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 7, 6);
lean_closure_set(v___f_3396_, 0, v_toApplicative_3391_);
lean_closure_set(v___f_3396_, 1, v_mvarId_3389_);
lean_closure_set(v___f_3396_, 2, v_modifyInfoState_3394_);
lean_closure_set(v___f_3396_, 3, v_inst_3386_);
lean_closure_set(v___f_3396_, 4, v_x_3390_);
lean_closure_set(v___f_3396_, 5, v___f_3395_);
v___f_3397_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3397_, 0, v_x_3390_);
lean_closure_set(v___f_3397_, 1, v_inst_3387_);
lean_closure_set(v___f_3397_, 2, v_inst_3388_);
lean_closure_set(v___f_3397_, 3, v_toBind_3392_);
lean_closure_set(v___f_3397_, 4, v___f_3396_);
v___x_3398_ = lean_apply_4(v_toBind_3392_, lean_box(0), lean_box(0), v_getInfoState_3393_, v___f_3397_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t v_flag_3399_, lean_object* v_s_3400_){
_start:
{
lean_object* v_assignment_3401_; lean_object* v_lazyAssignment_3402_; lean_object* v_trees_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
v_assignment_3401_ = lean_ctor_get(v_s_3400_, 0);
v_lazyAssignment_3402_ = lean_ctor_get(v_s_3400_, 1);
v_trees_3403_ = lean_ctor_get(v_s_3400_, 2);
v_isSharedCheck_3410_ = !lean_is_exclusive(v_s_3400_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v_s_3400_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_trees_3403_);
lean_inc(v_lazyAssignment_3402_);
lean_inc(v_assignment_3401_);
lean_dec(v_s_3400_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_assignment_3401_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v_lazyAssignment_3402_);
lean_ctor_set(v_reuseFailAlloc_3409_, 2, v_trees_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
lean_ctor_set_uint8(v___x_3408_, sizeof(void*)*3, v_flag_3399_);
return v___x_3408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object* v_flag_3411_, lean_object* v_s_3412_){
_start:
{
uint8_t v_flag_boxed_3413_; lean_object* v_res_3414_; 
v_flag_boxed_3413_ = lean_unbox(v_flag_3411_);
v_res_3414_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_3413_, v_s_3412_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object* v_inst_3415_, uint8_t v_flag_3416_){
_start:
{
lean_object* v_modifyInfoState_3417_; lean_object* v___x_3418_; lean_object* v___f_3419_; lean_object* v___x_3420_; 
v_modifyInfoState_3417_ = lean_ctor_get(v_inst_3415_, 1);
lean_inc(v_modifyInfoState_3417_);
lean_dec_ref(v_inst_3415_);
v___x_3418_ = lean_box(v_flag_3416_);
v___f_3419_ = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3419_, 0, v___x_3418_);
v___x_3420_ = lean_apply_1(v_modifyInfoState_3417_, v___f_3419_);
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object* v_inst_3421_, lean_object* v_flag_3422_){
_start:
{
uint8_t v_flag_boxed_3423_; lean_object* v_res_3424_; 
v_flag_boxed_3423_ = lean_unbox(v_flag_3422_);
v_res_3424_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3421_, v_flag_boxed_3423_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object* v_m_3425_, lean_object* v_inst_3426_, uint8_t v_flag_3427_){
_start:
{
lean_object* v___x_3428_; 
v___x_3428_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3426_, v_flag_3427_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object* v_m_3429_, lean_object* v_inst_3430_, lean_object* v_flag_3431_){
_start:
{
uint8_t v_flag_boxed_3432_; lean_object* v_res_3433_; 
v_flag_boxed_3432_ = lean_unbox(v_flag_3431_);
v_res_3433_ = l_Lean_Elab_enableInfoTree(v_m_3429_, v_inst_3430_, v_flag_boxed_3432_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object* v_x_3434_){
_start:
{
lean_object* v_fst_3435_; 
v_fst_3435_ = lean_ctor_get(v_x_3434_, 0);
lean_inc(v_fst_3435_);
return v_fst_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object* v_x_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_3436_);
lean_dec_ref(v_x_3436_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object* v_x_3438_, lean_object* v_____r_3439_){
_start:
{
lean_inc(v_x_3438_);
return v_x_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object* v_x_3440_, lean_object* v_____r_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_3440_, v_____r_3441_);
lean_dec(v_x_3440_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object* v___x_3443_, lean_object* v_x_3444_){
_start:
{
lean_inc(v___x_3443_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object* v___x_3445_, lean_object* v_x_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_3445_, v_x_3446_);
lean_dec(v_x_3446_);
lean_dec(v___x_3445_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object* v_toFunctor_3448_, lean_object* v_inst_3449_, uint8_t v_flag_3450_, lean_object* v_toBind_3451_, lean_object* v___f_3452_, lean_object* v_inst_3453_, lean_object* v___f_3454_, lean_object* v_____do__lift_3455_){
_start:
{
uint8_t v_enabled_3456_; lean_object* v_map_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___f_3461_; lean_object* v_y_3462_; lean_object* v___x_3463_; 
v_enabled_3456_ = lean_ctor_get_uint8(v_____do__lift_3455_, sizeof(void*)*3);
v_map_3457_ = lean_ctor_get(v_toFunctor_3448_, 0);
lean_inc(v_map_3457_);
lean_dec_ref(v_toFunctor_3448_);
lean_inc_ref(v_inst_3449_);
v___x_3458_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3449_, v_flag_3450_);
v___x_3459_ = lean_apply_4(v_toBind_3451_, lean_box(0), lean_box(0), v___x_3458_, v___f_3452_);
v___x_3460_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3449_, v_enabled_3456_);
v___f_3461_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_3461_, 0, v___x_3460_);
v_y_3462_ = lean_apply_4(v_inst_3453_, lean_box(0), lean_box(0), v___x_3459_, v___f_3461_);
v___x_3463_ = lean_apply_4(v_map_3457_, lean_box(0), lean_box(0), v___f_3454_, v_y_3462_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object* v_toFunctor_3464_, lean_object* v_inst_3465_, lean_object* v_flag_3466_, lean_object* v_toBind_3467_, lean_object* v___f_3468_, lean_object* v_inst_3469_, lean_object* v___f_3470_, lean_object* v_____do__lift_3471_){
_start:
{
uint8_t v_flag_boxed_3472_; lean_object* v_res_3473_; 
v_flag_boxed_3472_ = lean_unbox(v_flag_3466_);
v_res_3473_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_3464_, v_inst_3465_, v_flag_boxed_3472_, v_toBind_3467_, v___f_3468_, v_inst_3469_, v___f_3470_, v_____do__lift_3471_);
lean_dec_ref(v_____do__lift_3471_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object* v_inst_3475_, lean_object* v_inst_3476_, lean_object* v_inst_3477_, uint8_t v_flag_3478_, lean_object* v_x_3479_){
_start:
{
lean_object* v_toApplicative_3480_; lean_object* v_toBind_3481_; lean_object* v_getInfoState_3482_; lean_object* v_toFunctor_3483_; lean_object* v___f_3484_; lean_object* v___f_3485_; lean_object* v___x_3486_; lean_object* v___f_3487_; lean_object* v___x_3488_; 
v_toApplicative_3480_ = lean_ctor_get(v_inst_3475_, 0);
lean_inc_ref(v_toApplicative_3480_);
v_toBind_3481_ = lean_ctor_get(v_inst_3475_, 1);
lean_inc_n(v_toBind_3481_, 2);
lean_dec_ref(v_inst_3475_);
v_getInfoState_3482_ = lean_ctor_get(v_inst_3476_, 0);
lean_inc(v_getInfoState_3482_);
v_toFunctor_3483_ = lean_ctor_get(v_toApplicative_3480_, 0);
lean_inc_ref(v_toFunctor_3483_);
lean_dec_ref(v_toApplicative_3480_);
v___f_3484_ = ((lean_object*)(l_Lean_Elab_withEnableInfoTree___redArg___closed__0));
v___f_3485_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3485_, 0, v_x_3479_);
v___x_3486_ = lean_box(v_flag_3478_);
v___f_3487_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_3487_, 0, v_toFunctor_3483_);
lean_closure_set(v___f_3487_, 1, v_inst_3476_);
lean_closure_set(v___f_3487_, 2, v___x_3486_);
lean_closure_set(v___f_3487_, 3, v_toBind_3481_);
lean_closure_set(v___f_3487_, 4, v___f_3485_);
lean_closure_set(v___f_3487_, 5, v_inst_3477_);
lean_closure_set(v___f_3487_, 6, v___f_3484_);
v___x_3488_ = lean_apply_4(v_toBind_3481_, lean_box(0), lean_box(0), v_getInfoState_3482_, v___f_3487_);
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object* v_inst_3489_, lean_object* v_inst_3490_, lean_object* v_inst_3491_, lean_object* v_flag_3492_, lean_object* v_x_3493_){
_start:
{
uint8_t v_flag_boxed_3494_; lean_object* v_res_3495_; 
v_flag_boxed_3494_ = lean_unbox(v_flag_3492_);
v_res_3495_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3489_, v_inst_3490_, v_inst_3491_, v_flag_boxed_3494_, v_x_3493_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object* v_m_3496_, lean_object* v_00_u03b1_3497_, lean_object* v_inst_3498_, lean_object* v_inst_3499_, lean_object* v_inst_3500_, uint8_t v_flag_3501_, lean_object* v_x_3502_){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3498_, v_inst_3499_, v_inst_3500_, v_flag_3501_, v_x_3502_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object* v_m_3504_, lean_object* v_00_u03b1_3505_, lean_object* v_inst_3506_, lean_object* v_inst_3507_, lean_object* v_inst_3508_, lean_object* v_flag_3509_, lean_object* v_x_3510_){
_start:
{
uint8_t v_flag_boxed_3511_; lean_object* v_res_3512_; 
v_flag_boxed_3511_ = lean_unbox(v_flag_3509_);
v_res_3512_ = l_Lean_Elab_withEnableInfoTree(v_m_3504_, v_00_u03b1_3505_, v_inst_3506_, v_inst_3507_, v_inst_3508_, v_flag_boxed_3511_, v_x_3510_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object* v_toPure_3513_, lean_object* v_____do__lift_3514_){
_start:
{
lean_object* v_trees_3515_; lean_object* v___x_3516_; 
v_trees_3515_ = lean_ctor_get(v_____do__lift_3514_, 2);
lean_inc_ref(v_trees_3515_);
lean_dec_ref(v_____do__lift_3514_);
v___x_3516_ = lean_apply_2(v_toPure_3513_, lean_box(0), v_trees_3515_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object* v_inst_3517_, lean_object* v_inst_3518_){
_start:
{
lean_object* v_toApplicative_3519_; lean_object* v_toBind_3520_; lean_object* v_getInfoState_3521_; lean_object* v_toPure_3522_; lean_object* v___f_3523_; lean_object* v___x_3524_; 
v_toApplicative_3519_ = lean_ctor_get(v_inst_3518_, 0);
lean_inc_ref(v_toApplicative_3519_);
v_toBind_3520_ = lean_ctor_get(v_inst_3518_, 1);
lean_inc(v_toBind_3520_);
lean_dec_ref(v_inst_3518_);
v_getInfoState_3521_ = lean_ctor_get(v_inst_3517_, 0);
lean_inc(v_getInfoState_3521_);
lean_dec_ref(v_inst_3517_);
v_toPure_3522_ = lean_ctor_get(v_toApplicative_3519_, 1);
lean_inc(v_toPure_3522_);
lean_dec_ref(v_toApplicative_3519_);
v___f_3523_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3523_, 0, v_toPure_3522_);
v___x_3524_ = lean_apply_4(v_toBind_3520_, lean_box(0), lean_box(0), v_getInfoState_3521_, v___f_3523_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object* v_m_3525_, lean_object* v_inst_3526_, lean_object* v_inst_3527_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_3526_, v_inst_3527_);
return v___x_3528_;
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
