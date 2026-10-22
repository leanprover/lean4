// Lean compiler output
// Module: Lean.Elab.ElabRules
// Imports: public import Lean.Elab.MacroArgUtil public import Lean.Elab.AuxDef public import Lean.Elab.Do.Basic
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSyntax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_evalOptPrio___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Array_mkArray5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Elab_Command_resolveSyntaxKind(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkRuleAltKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Parser_Command_visibility_ofAttrKind(lean_object*);
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elab_rules"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabRules"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__5;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__4_value),LEAN_SCALAR_PTR_LITERAL(187, 124, 47, 85, 21, 141, 50, 117)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Elab.Do.DoElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__9;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DoElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__11_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__14_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "stx"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__15 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__16;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__15_value),LEAN_SCALAR_PTR_LITERAL(89, 124, 230, 186, 154, 11, 21, 78)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__17 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__17_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__18 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__18_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__19 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__19_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__20 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__20_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__21 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__21_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__22 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__22_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__23 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__23_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__24 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__24_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__25 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__25_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__26 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__26_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noErrorIfUnused"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__27 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__27_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "no_error_if_unused%"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__28 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__28_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "throwUnsupportedSyntax"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__29 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__30;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(225, 251, 194, 35, 13, 152, 147, 184)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__31 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__32 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__33 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "aux_def"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__34 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__35_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__35_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__35_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__34_value),LEAN_SCALAR_PTR_LITERAL(83, 33, 36, 212, 17, 187, 86, 94)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__35 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__35_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__36;
static const lean_array_object l_Lean_Elab_Command_elabElabRulesAux___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__37 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__37_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.Term.TermElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__38 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__38_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__39;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "TermElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__40 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__40_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expectedType\?"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__41 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__41_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__42;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__41_value),LEAN_SCALAR_PTR_LITERAL(47, 72, 75, 114, 68, 52, 233, 214)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__43 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__43_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__44 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__44_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Elab.Term.withExpectedType"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__45 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__45_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__46;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "withExpectedType"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__47 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__47_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.Tactic.Tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__48 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__48_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__49;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__50 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__50_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cont"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__51 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__51_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__52;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__51_value),LEAN_SCALAR_PTR_LITERAL(53, 231, 177, 147, 174, 255, 200, 174)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__53 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__53_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Elab.Command.CommandElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__54 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__54_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__55;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "CommandElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__56 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__56_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__57 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__57_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__57_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__58 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__58_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doElem"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__59 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__59_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__59_value),LEAN_SCALAR_PTR_LITERAL(224, 169, 39, 82, 97, 101, 60, 174)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__60 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__60_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "syntax category `"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__61 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__61_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__62;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "` does not support expected type specification"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__63 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__63_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__64;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doElem_elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__65 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__65_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__65_value),LEAN_SCALAR_PTR_LITERAL(211, 179, 163, 70, 253, 44, 85, 125)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__66 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__66_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__67 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__67_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__67_value),LEAN_SCALAR_PTR_LITERAL(226, 9, 43, 122, 104, 86, 206, 223)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__68 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__68_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__69 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__69_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__69_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__70 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__70_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__71 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__71_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__71_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__72 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__72_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "conv"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__73 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__73_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__73_value),LEAN_SCALAR_PTR_LITERAL(232, 67, 39, 189, 45, 247, 54, 81)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__74 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__74_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "unsupported syntax category `"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__75 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__75_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__76;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__77 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__77_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__78;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "command_elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__79 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__79_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__79_value),LEAN_SCALAR_PTR_LITERAL(7, 200, 102, 28, 219, 237, 42, 33)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__80 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__80_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "invalid elab_rules command, specify category using `elab_rules : <cat> ...`"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__81 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__81_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__82;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "<="};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___boxed(lean_object**);
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 70, 226, 250, 127, 121, 118, 247)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__22_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Command_elabElabRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_elabElabRules___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Command_elabElabRules___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___closed__0_value;
static const lean_closure_object l_Lean_Elab_Command_elabElabRules___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_elabElabRules___lam__2___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___closed__0_value)} };
static const lean_object* l_Lean_Elab_Command_elabElabRules___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "elabElabRules"};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 97, 52, 186, 206, 196, 221, 235)}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(74) << 1) | 1)),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(81) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0_value),((lean_object*)(((size_t)(37) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1_value),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(74) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(74) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3_value),((lean_object*)(((size_t)(41) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4_value),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`("};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elab"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 177, 45, 203, 60, 20, 245, 118)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedPrio"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__4_value),LEAN_SCALAR_PTR_LITERAL(171, 32, 2, 102, 118, 75, 64, 185)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "priority"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__7_value),LEAN_SCALAR_PTR_LITERAL(73, 173, 122, 11, 5, 195, 101, 245)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__9_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "precedence"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__10_value),LEAN_SCALAR_PTR_LITERAL(69, 243, 176, 51, 48, 112, 202, 160)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__11_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__12_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabTail"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__14_value),LEAN_SCALAR_PTR_LITERAL(131, 240, 225, 71, 37, 75, 83, 37)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__15 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabElab"};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 235, 135, 254, 44, 234, 233, 9)}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(84) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(84) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(84) << 1) | 1)),((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4_value),((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(lean_object* v_val_1_, uint8_t v_canonical_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = l_Lean_Elab_Command_getRef___redArg(v___y_3_);
if (lean_obj_tag(v___x_5_) == 0)
{
lean_object* v_a_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_14_; 
v_a_6_ = lean_ctor_get(v___x_5_, 0);
v_isSharedCheck_14_ = !lean_is_exclusive(v___x_5_);
if (v_isSharedCheck_14_ == 0)
{
v___x_8_ = v___x_5_;
v_isShared_9_ = v_isSharedCheck_14_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_a_6_);
lean_dec(v___x_5_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_14_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; lean_object* v___x_12_; 
v___x_10_ = l_Lean_mkIdentFrom(v_a_6_, v_val_1_, v_canonical_2_);
lean_dec(v_a_6_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 0, v___x_10_);
v___x_12_ = v___x_8_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v___x_10_);
v___x_12_ = v_reuseFailAlloc_13_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
return v___x_12_;
}
}
}
else
{
lean_object* v_a_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_22_; 
lean_dec(v_val_1_);
v_a_15_ = lean_ctor_get(v___x_5_, 0);
v_isSharedCheck_22_ = !lean_is_exclusive(v___x_5_);
if (v_isSharedCheck_22_ == 0)
{
v___x_17_ = v___x_5_;
v_isShared_18_ = v_isSharedCheck_22_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_a_15_);
lean_dec(v___x_5_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_22_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_a_15_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg___boxed(lean_object* v_val_23_, lean_object* v_canonical_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
uint8_t v_canonical_boxed_27_; lean_object* v_res_28_; 
v_canonical_boxed_27_ = lean_unbox(v_canonical_24_);
v_res_28_ = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(v_val_23_, v_canonical_boxed_27_, v___y_25_);
lean_dec_ref(v___y_25_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0(lean_object* v_val_29_, uint8_t v_canonical_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(v_val_29_, v_canonical_30_, v___y_31_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___boxed(lean_object* v_val_35_, lean_object* v_canonical_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
uint8_t v_canonical_boxed_40_; lean_object* v_res_41_; 
v_canonical_boxed_40_ = lean_unbox(v_canonical_36_);
v_res_41_ = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0(v_val_35_, v_canonical_boxed_40_, v___y_37_, v___y_38_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(lean_object* v___y_42_){
_start:
{
lean_object* v___x_44_; lean_object* v_env_45_; lean_object* v___x_46_; lean_object* v_mainModule_47_; lean_object* v___x_48_; 
v___x_44_ = lean_st_ref_get(v___y_42_);
v_env_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc_ref(v_env_45_);
lean_dec(v___x_44_);
v___x_46_ = l_Lean_Environment_header(v_env_45_);
lean_dec_ref(v_env_45_);
v_mainModule_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_mainModule_47_);
lean_dec_ref(v___x_46_);
v___x_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_48_, 0, v_mainModule_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg___boxed(lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_49_);
lean_dec(v___y_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1(lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_53_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___boxed(lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1(v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0(lean_object* v_k_79_, lean_object* v_attrKind_80_, lean_object* v_attrs_x3f_81_, lean_object* v_kind_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
uint8_t v___x_86_; lean_object* v___x_87_; 
v___x_86_ = 0;
v___x_87_ = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(v_k_79_, v___x_86_, v___y_83_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v___x_89_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_a_88_);
lean_dec_ref_known(v___x_87_, 1);
v___x_89_ = l_Lean_Elab_Command_getRef___redArg(v___y_83_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_126_; 
v_a_90_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_126_ == 0)
{
v___x_92_ = v___x_89_;
v_isShared_93_ = v_isSharedCheck_126_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_126_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_94_; lean_object* v___x_115_; 
v___x_94_ = l_Lean_SourceInfo_fromRef(v_a_90_, v___x_86_);
lean_dec(v_a_90_);
v___x_115_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_83_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_quotContext_x3f_116_; 
lean_dec_ref_known(v___x_115_, 1);
v_quotContext_x3f_116_ = lean_ctor_get(v___y_83_, 5);
if (lean_obj_tag(v_quotContext_x3f_116_) == 0)
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_84_);
lean_dec_ref(v___x_117_);
goto v___jp_95_;
}
else
{
goto v___jp_95_;
}
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
lean_dec(v___x_94_);
lean_del_object(v___x_92_);
lean_dec(v_a_88_);
lean_dec(v_kind_82_);
lean_dec(v_attrKind_80_);
v_a_118_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_115_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_115_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
v___jp_95_:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_96_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4));
v___x_97_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7));
v___x_98_ = l_Lean_mkIdent(v_kind_82_);
v___x_99_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
lean_inc_n(v___x_94_, 2);
v___x_100_ = l_Lean_Syntax_node1(v___x_94_, v___x_99_, v_a_88_);
v___x_101_ = l_Lean_Syntax_node2(v___x_94_, v___x_97_, v___x_98_, v___x_100_);
v___x_102_ = l_Lean_Syntax_node2(v___x_94_, v___x_96_, v_attrKind_80_, v___x_101_);
if (lean_obj_tag(v_attrs_x3f_81_) == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_mk_empty_array_with_capacity(v___x_103_);
v___x_105_ = lean_array_push(v___x_104_, v___x_102_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 0, v___x_105_);
v___x_107_ = v___x_92_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
else
{
lean_object* v_val_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
v_val_109_ = lean_ctor_get(v_attrs_x3f_81_, 0);
v___x_110_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_109_);
v___x_111_ = lean_array_push(v___x_110_, v___x_102_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 0, v___x_111_);
v___x_113_ = v___x_92_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
else
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
lean_dec(v_a_88_);
lean_dec(v_kind_82_);
lean_dec(v_attrKind_80_);
v_a_127_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_134_ == 0)
{
v___x_129_ = v___x_89_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_89_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_127_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
else
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_142_; 
lean_dec(v_kind_82_);
lean_dec(v_attrKind_80_);
v_a_135_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_142_ == 0)
{
v___x_137_ = v___x_87_;
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_87_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_138_ == 0)
{
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_135_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___boxed(lean_object* v_k_143_, lean_object* v_attrKind_144_, lean_object* v_attrs_x3f_145_, lean_object* v_kind_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_143_, v_attrKind_144_, v_attrs_x3f_145_, v_kind_146_, v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v_attrs_x3f_145_);
return v_res_150_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_151_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__0);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_154_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_155_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
lean_ctor_set(v___x_157_, 2, v___x_156_);
lean_ctor_set(v___x_157_, 3, v___x_156_);
lean_ctor_set(v___x_157_, 4, v___x_155_);
lean_ctor_set(v___x_157_, 5, v___x_155_);
lean_ctor_set(v___x_157_, 6, v___x_155_);
lean_ctor_set(v___x_157_, 7, v___x_155_);
lean_ctor_set(v___x_157_, 8, v___x_155_);
lean_ctor_set(v___x_157_, 9, v___x_155_);
lean_ctor_set(v___x_157_, 10, v___x_154_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_unsigned_to_nat(32u);
v___x_159_ = lean_mk_empty_array_with_capacity(v___x_158_);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_161_ = ((size_t)5ULL);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_unsigned_to_nat(32u);
v___x_164_ = lean_mk_empty_array_with_capacity(v___x_163_);
v___x_165_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__3);
v___x_166_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
lean_ctor_set(v___x_166_, 2, v___x_162_);
lean_ctor_set(v___x_166_, 3, v___x_162_);
lean_ctor_set_usize(v___x_166_, 4, v___x_161_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_box(1);
v___x_168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__4);
v___x_169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__1);
v___x_170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_167_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg(lean_object* v_msgData_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___x_174_; lean_object* v_env_175_; uint8_t v___x_176_; lean_object* v_env_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v_scopes_180_; lean_object* v___x_181_; lean_object* v_opts_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_174_ = lean_st_ref_get(v___y_172_);
v_env_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc_ref(v_env_175_);
lean_dec(v___x_174_);
v___x_176_ = 0;
v_env_177_ = l_Lean_Environment_setRecordingDeps(v_env_175_, v___x_176_);
v___x_178_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_179_ = lean_st_ref_get(v___y_172_);
v_scopes_180_ = lean_ctor_get(v___x_179_, 2);
lean_inc(v_scopes_180_);
lean_dec(v___x_179_);
v___x_181_ = l_List_head_x21___redArg(v___x_178_, v_scopes_180_);
lean_dec(v_scopes_180_);
v_opts_182_ = lean_ctor_get(v___x_181_, 1);
lean_inc_ref(v_opts_182_);
lean_dec(v___x_181_);
v___x_183_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__2);
v___x_184_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___closed__5);
v___x_185_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_185_, 0, v_env_177_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
lean_ctor_set(v___x_185_, 2, v___x_184_);
lean_ctor_set(v___x_185_, 3, v_opts_182_);
v___x_186_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v_msgData_171_);
v___x_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg___boxed(lean_object* v_msgData_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg(v_msgData_188_, v___y_189_);
lean_dec(v___y_189_);
return v_res_191_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_box(1);
v___x_193_ = l_Lean_MessageData_ofFormat(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__3(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__2));
v___x_198_ = l_Lean_MessageData_ofFormat(v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7(lean_object* v_x_199_, lean_object* v_x_200_){
_start:
{
if (lean_obj_tag(v_x_200_) == 0)
{
return v_x_199_;
}
else
{
lean_object* v_head_201_; lean_object* v_tail_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_224_; 
v_head_201_ = lean_ctor_get(v_x_200_, 0);
v_tail_202_ = lean_ctor_get(v_x_200_, 1);
v_isSharedCheck_224_ = !lean_is_exclusive(v_x_200_);
if (v_isSharedCheck_224_ == 0)
{
v___x_204_ = v_x_200_;
v_isShared_205_ = v_isSharedCheck_224_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_tail_202_);
lean_inc(v_head_201_);
lean_dec(v_x_200_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_224_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v_before_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_222_; 
v_before_206_ = lean_ctor_get(v_head_201_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v_head_201_);
if (v_isSharedCheck_222_ == 0)
{
lean_object* v_unused_223_; 
v_unused_223_ = lean_ctor_get(v_head_201_, 1);
lean_dec(v_unused_223_);
v___x_208_ = v_head_201_;
v_isShared_209_ = v_isSharedCheck_222_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_before_206_);
lean_dec(v_head_201_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_222_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_210_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0);
if (v_isShared_209_ == 0)
{
lean_ctor_set_tag(v___x_208_, 7);
lean_ctor_set(v___x_208_, 1, v___x_210_);
lean_ctor_set(v___x_208_, 0, v_x_199_);
v___x_212_ = v___x_208_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_x_199_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v___x_210_);
v___x_212_ = v_reuseFailAlloc_221_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_213_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__3);
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 7);
lean_ctor_set(v___x_204_, 1, v___x_213_);
lean_ctor_set(v___x_204_, 0, v___x_212_);
v___x_215_ = v___x_204_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_213_);
v___x_215_ = v_reuseFailAlloc_220_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = l_Lean_MessageData_ofSyntax(v_before_206_);
v___x_217_ = l_Lean_indentD(v___x_216_);
v___x_218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_215_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v_x_199_ = v___x_218_;
v_x_200_ = v_tail_202_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__6(lean_object* v_opts_225_, lean_object* v_opt_226_){
_start:
{
lean_object* v_name_227_; lean_object* v_defValue_228_; lean_object* v_map_229_; lean_object* v___x_230_; 
v_name_227_ = lean_ctor_get(v_opt_226_, 0);
v_defValue_228_ = lean_ctor_get(v_opt_226_, 1);
v_map_229_ = lean_ctor_get(v_opts_225_, 0);
v___x_230_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_229_, v_name_227_);
if (lean_obj_tag(v___x_230_) == 0)
{
uint8_t v___x_231_; 
v___x_231_ = lean_unbox(v_defValue_228_);
return v___x_231_;
}
else
{
lean_object* v_val_232_; 
v_val_232_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_val_232_);
lean_dec_ref_known(v___x_230_, 1);
if (lean_obj_tag(v_val_232_) == 1)
{
uint8_t v_v_233_; 
v_v_233_ = lean_ctor_get_uint8(v_val_232_, 0);
lean_dec_ref_known(v_val_232_, 0);
return v_v_233_;
}
else
{
uint8_t v___x_234_; 
lean_dec(v_val_232_);
v___x_234_ = lean_unbox(v_defValue_228_);
return v___x_234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__6___boxed(lean_object* v_opts_235_, lean_object* v_opt_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__6(v_opts_235_, v_opt_236_);
lean_dec_ref(v_opt_236_);
lean_dec_ref(v_opts_235_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__1));
v___x_243_ = l_Lean_MessageData_ofFormat(v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg(lean_object* v_msgData_244_, lean_object* v_macroStack_245_, lean_object* v___y_246_){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v_scopes_250_; lean_object* v___x_251_; lean_object* v_opts_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_248_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_249_ = lean_st_ref_get(v___y_246_);
v_scopes_250_ = lean_ctor_get(v___x_249_, 2);
lean_inc(v_scopes_250_);
lean_dec(v___x_249_);
v___x_251_ = l_List_head_x21___redArg(v___x_248_, v_scopes_250_);
lean_dec(v_scopes_250_);
v_opts_252_ = lean_ctor_get(v___x_251_, 1);
lean_inc_ref(v_opts_252_);
lean_dec(v___x_251_);
v___x_253_ = l_Lean_Elab_pp_macroStack;
v___x_254_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__6(v_opts_252_, v___x_253_);
lean_dec_ref(v_opts_252_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
lean_dec(v_macroStack_245_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v_msgData_244_);
return v___x_255_;
}
else
{
if (lean_obj_tag(v_macroStack_245_) == 0)
{
lean_object* v___x_256_; 
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v_msgData_244_);
return v___x_256_;
}
else
{
lean_object* v_head_257_; lean_object* v_after_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_273_; 
v_head_257_ = lean_ctor_get(v_macroStack_245_, 0);
lean_inc(v_head_257_);
v_after_258_ = lean_ctor_get(v_head_257_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_head_257_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v_head_257_, 0);
lean_dec(v_unused_274_);
v___x_260_ = v_head_257_;
v_isShared_261_ = v_isSharedCheck_273_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_after_258_);
lean_dec(v_head_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_273_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7___closed__0);
if (v_isShared_261_ == 0)
{
lean_ctor_set_tag(v___x_260_, 7);
lean_ctor_set(v___x_260_, 1, v___x_262_);
lean_ctor_set(v___x_260_, 0, v_msgData_244_);
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_msgData_244_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v___x_262_);
v___x_264_ = v_reuseFailAlloc_272_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_msgData_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_265_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___closed__2);
v___x_266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = l_Lean_MessageData_ofSyntax(v_after_258_);
v___x_268_ = l_Lean_indentD(v___x_267_);
v_msgData_269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_269_, 0, v___x_266_);
lean_ctor_set(v_msgData_269_, 1, v___x_268_);
v___x_270_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5_spec__7(v_msgData_269_, v_macroStack_245_);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg___boxed(lean_object* v_msgData_275_, lean_object* v_macroStack_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg(v_msgData_275_, v_macroStack_276_, v___y_277_);
lean_dec(v___y_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(lean_object* v_msg_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Elab_Command_getRef___redArg(v___y_281_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v_macroStack_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v_a_289_; lean_object* v___x_290_; lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_299_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_a_285_);
lean_dec_ref_known(v___x_284_, 1);
v_macroStack_286_ = lean_ctor_get(v___y_281_, 4);
v___x_287_ = l_Lean_Elab_getBetterRef(v_a_285_, v_macroStack_286_);
lean_dec(v_a_285_);
v___x_288_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg(v_msg_280_, v___y_282_);
v_a_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_a_289_);
lean_dec_ref(v___x_288_);
lean_inc(v_macroStack_286_);
v___x_290_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg(v_a_289_, v_macroStack_286_, v___y_282_);
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
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_287_);
lean_ctor_set(v___x_295_, 1, v_a_291_);
if (v_isShared_294_ == 0)
{
lean_ctor_set_tag(v___x_293_, 1);
lean_ctor_set(v___x_293_, 0, v___x_295_);
v___x_297_ = v___x_293_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
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
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec_ref(v_msg_280_);
v_a_300_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_284_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_284_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg___boxed(lean_object* v_msg_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(v_msg_308_, v___y_309_, v___y_310_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(lean_object* v_ref_313_, lean_object* v_msg_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Elab_Command_getRef___redArg(v___y_315_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v_fileName_320_; lean_object* v_fileMap_321_; lean_object* v_currRecDepth_322_; lean_object* v_cmdPos_323_; lean_object* v_macroStack_324_; lean_object* v_quotContext_x3f_325_; lean_object* v_currMacroScope_326_; lean_object* v_snap_x3f_327_; lean_object* v_cancelTk_x3f_328_; uint8_t v_suppressElabErrors_329_; lean_object* v_ref_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref_known(v___x_318_, 1);
v_fileName_320_ = lean_ctor_get(v___y_315_, 0);
v_fileMap_321_ = lean_ctor_get(v___y_315_, 1);
v_currRecDepth_322_ = lean_ctor_get(v___y_315_, 2);
v_cmdPos_323_ = lean_ctor_get(v___y_315_, 3);
v_macroStack_324_ = lean_ctor_get(v___y_315_, 4);
v_quotContext_x3f_325_ = lean_ctor_get(v___y_315_, 5);
v_currMacroScope_326_ = lean_ctor_get(v___y_315_, 6);
v_snap_x3f_327_ = lean_ctor_get(v___y_315_, 8);
v_cancelTk_x3f_328_ = lean_ctor_get(v___y_315_, 9);
v_suppressElabErrors_329_ = lean_ctor_get_uint8(v___y_315_, sizeof(void*)*10);
v_ref_330_ = l_Lean_replaceRef(v_ref_313_, v_a_319_);
lean_dec(v_a_319_);
lean_inc(v_cancelTk_x3f_328_);
lean_inc(v_snap_x3f_327_);
lean_inc(v_currMacroScope_326_);
lean_inc(v_quotContext_x3f_325_);
lean_inc(v_macroStack_324_);
lean_inc(v_cmdPos_323_);
lean_inc(v_currRecDepth_322_);
lean_inc_ref(v_fileMap_321_);
lean_inc_ref(v_fileName_320_);
v___x_331_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_331_, 0, v_fileName_320_);
lean_ctor_set(v___x_331_, 1, v_fileMap_321_);
lean_ctor_set(v___x_331_, 2, v_currRecDepth_322_);
lean_ctor_set(v___x_331_, 3, v_cmdPos_323_);
lean_ctor_set(v___x_331_, 4, v_macroStack_324_);
lean_ctor_set(v___x_331_, 5, v_quotContext_x3f_325_);
lean_ctor_set(v___x_331_, 6, v_currMacroScope_326_);
lean_ctor_set(v___x_331_, 7, v_ref_330_);
lean_ctor_set(v___x_331_, 8, v_snap_x3f_327_);
lean_ctor_set(v___x_331_, 9, v_cancelTk_x3f_328_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*10, v_suppressElabErrors_329_);
v___x_332_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(v_msg_314_, v___x_331_, v___y_316_);
lean_dec_ref_known(v___x_331_, 10);
return v___x_332_;
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_dec_ref(v_msg_314_);
v_a_333_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_318_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_318_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(lean_object* v_ref_341_, lean_object* v_msg_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_341_, v_msg_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v_ref_341_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(lean_object* v_k_348_, size_t v_sz_349_, size_t v_i_350_, lean_object* v_bs_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
uint8_t v___x_355_; 
v___x_355_ = lean_usize_dec_lt(v_i_350_, v_sz_349_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
lean_dec(v_k_348_);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v_bs_351_);
return v___x_356_;
}
else
{
lean_object* v___x_357_; lean_object* v_v_358_; lean_object* v___x_359_; lean_object* v_bs_x27_360_; lean_object* v___x_361_; 
v___x_357_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___closed__0));
v_v_358_ = lean_array_uget(v_bs_351_, v_i_350_);
v___x_359_ = lean_unsigned_to_nat(0u);
v_bs_x27_360_ = lean_array_uset(v_bs_351_, v_i_350_, v___x_359_);
lean_inc(v_k_348_);
v___x_361_ = l_Lean_Elab_Command_checkRuleAltKind(v___x_357_, v_k_348_, v_v_358_, v___y_352_, v___y_353_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; size_t v___x_363_; size_t v___x_364_; lean_object* v___x_365_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref_known(v___x_361_, 1);
v___x_363_ = ((size_t)1ULL);
v___x_364_ = lean_usize_add(v_i_350_, v___x_363_);
v___x_365_ = lean_array_uset(v_bs_x27_360_, v_i_350_, v_a_362_);
v_i_350_ = v___x_364_;
v_bs_351_ = v___x_365_;
goto _start;
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_dec_ref(v_bs_x27_360_);
lean_dec(v_k_348_);
v_a_367_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_361_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_361_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___boxed(lean_object* v_k_375_, lean_object* v_sz_376_, lean_object* v_i_377_, lean_object* v_bs_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
size_t v_sz_boxed_382_; size_t v_i_boxed_383_; lean_object* v_res_384_; 
v_sz_boxed_382_ = lean_unbox_usize(v_sz_376_);
lean_dec(v_sz_376_);
v_i_boxed_383_ = lean_unbox_usize(v_i_377_);
lean_dec(v_i_377_);
v_res_384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(v_k_375_, v_sz_boxed_382_, v_i_boxed_383_, v_bs_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_384_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__4));
v___x_391_ = l_String_toRawSubstring_x27(v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__8));
v___x_397_ = l_String_toRawSubstring_x27(v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__15));
v___x_405_ = l_String_toRawSubstring_x27(v___x_404_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_421_ = l_String_toRawSubstring_x27(v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36(void){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Array_mkArray0___redArg();
return v___x_432_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__39(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__38));
v___x_437_ = l_String_toRawSubstring_x27(v___x_436_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__42(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__41));
v___x_441_ = l_String_toRawSubstring_x27(v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__46(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__45));
v___x_447_ = l_String_toRawSubstring_x27(v___x_446_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__49(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__48));
v___x_451_ = l_String_toRawSubstring_x27(v___x_450_);
return v___x_451_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__52(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__51));
v___x_455_ = l_String_toRawSubstring_x27(v___x_454_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__55(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v___x_460_ = l_String_toRawSubstring_x27(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__62(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__61));
v___x_470_ = l_Lean_stringToMessageData(v___x_469_);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__64(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__63));
v___x_473_ = l_Lean_stringToMessageData(v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__75));
v___x_491_ = l_Lean_stringToMessageData(v___x_490_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__78(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__77));
v___x_494_ = l_Lean_stringToMessageData(v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__82(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__81));
v___x_500_ = l_Lean_stringToMessageData(v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object* v_doc_x3f_501_, lean_object* v_attrs_x3f_502_, lean_object* v_attrKind_503_, lean_object* v_k_504_, lean_object* v_cat_x3f_505_, lean_object* v_expty_x3f_506_, lean_object* v_alts_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
size_t v_sz_511_; size_t v___x_512_; lean_object* v___x_513_; 
v_sz_511_ = lean_array_size(v_alts_507_);
v___x_512_ = ((size_t)0ULL);
lean_inc(v_k_504_);
v___x_513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(v_k_504_, v_sz_511_, v___x_512_, v_alts_507_, v_a_508_, v_a_509_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_1530_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_1530_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_1530_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v_a_645_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v_a_797_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v_a_910_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; uint8_t v___y_924_; lean_object* v___y_925_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v_a_1081_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v_a_1195_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v_a_1328_; lean_object* v_catName_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; 
if (lean_obj_tag(v_cat_x3f_505_) == 1)
{
lean_object* v_val_1517_; lean_object* v___x_1518_; 
v_val_1517_ = lean_ctor_get(v_cat_x3f_505_, 0);
v___x_1518_ = l_Lean_TSyntax_getId(v_val_1517_);
v_catName_1339_ = v___x_1518_;
v___y_1340_ = v_a_508_;
v___y_1341_ = v_a_509_;
goto v___jp_1338_;
}
else
{
if (lean_obj_tag(v_expty_x3f_506_) == 1)
{
lean_object* v___x_1519_; 
v___x_1519_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__58));
v_catName_1339_ = v___x_1519_;
v___y_1340_ = v_a_508_;
v___y_1341_ = v_a_509_;
goto v___jp_1338_;
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_del_object(v___x_516_);
lean_dec(v_a_514_);
lean_dec(v_expty_x3f_506_);
lean_dec(v_k_504_);
lean_dec(v_attrKind_503_);
lean_dec(v_doc_x3f_501_);
v___x_1520_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__82, &l_Lean_Elab_Command_elabElabRulesAux___closed__82_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__82);
v___x_1521_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(v___x_1520_, v_a_508_, v_a_509_);
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1521_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
v___jp_518_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
lean_inc_ref_n(v___y_527_, 4);
v___x_532_ = l_Array_append___redArg(v___y_527_, v___y_531_);
lean_dec_ref(v___y_531_);
lean_inc_n(v___y_522_, 10);
lean_inc_n(v___y_525_, 35);
v___x_533_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_533_, 0, v___y_525_);
lean_ctor_set(v___x_533_, 1, v___y_522_);
lean_ctor_set(v___x_533_, 2, v___x_532_);
v___x_534_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_535_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_536_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_521_, 11);
v___x_537_ = l_Lean_Name_mkStr4(v___y_521_, v___x_534_, v___x_535_, v___x_536_);
v___x_538_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_539_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_539_, 0, v___y_525_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_541_ = l_Lean_Syntax_SepArray_ofElems(v___x_540_, v___y_523_);
lean_dec_ref(v___y_523_);
v___x_542_ = l_Array_append___redArg(v___y_527_, v___x_541_);
lean_dec_ref(v___x_541_);
v___x_543_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_543_, 0, v___y_525_);
lean_ctor_set(v___x_543_, 1, v___y_522_);
lean_ctor_set(v___x_543_, 2, v___x_542_);
v___x_544_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_545_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_545_, 0, v___y_525_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = l_Lean_Syntax_node3(v___y_525_, v___x_537_, v___x_539_, v___x_543_, v___x_545_);
v___x_547_ = l_Lean_Syntax_node1(v___y_525_, v___y_522_, v___x_546_);
lean_inc_ref(v___y_519_);
v___x_548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_548_, 0, v___y_525_);
lean_ctor_set(v___x_548_, 1, v___y_519_);
v___x_549_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_550_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_524_, 3);
lean_inc_n(v___y_526_, 3);
v___x_551_ = l_Lean_addMacroScope(v___y_526_, v___x_550_, v___y_524_);
v___x_552_ = lean_box(0);
v___x_553_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_553_, 0, v___y_525_);
lean_ctor_set(v___x_553_, 1, v___x_549_);
lean_ctor_set(v___x_553_, 2, v___x_551_);
lean_ctor_set(v___x_553_, 3, v___x_552_);
v___x_554_ = l_Lean_mkIdent(v_k_504_);
v___x_555_ = l_Lean_Syntax_node2(v___y_525_, v___y_522_, v___x_553_, v___x_554_);
v___x_556_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_557_, 0, v___y_525_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_559_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
v___x_560_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc_ref_n(v___y_530_, 2);
v___x_561_ = l_Lean_Name_mkStr4(v___y_521_, v___y_530_, v___x_559_, v___x_560_);
lean_inc(v___x_561_);
v___x_562_ = l_Lean_addMacroScope(v___y_526_, v___x_561_, v___y_524_);
v___x_563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set(v___x_563_, 1, v___x_552_);
v___x_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v___x_552_);
v___x_565_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_565_, 0, v___y_525_);
lean_ctor_set(v___x_565_, 1, v___x_558_);
lean_ctor_set(v___x_565_, 2, v___x_562_);
lean_ctor_set(v___x_565_, 3, v___x_564_);
v___x_566_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_567_, 0, v___y_525_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_569_ = l_Lean_Name_mkStr4(v___y_521_, v___x_534_, v___x_535_, v___x_568_);
v___x_570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_570_, 0, v___y_525_);
lean_ctor_set(v___x_570_, 1, v___x_568_);
v___x_571_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_572_ = l_Lean_Name_mkStr4(v___y_521_, v___x_534_, v___x_535_, v___x_571_);
v___x_573_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_574_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_575_ = l_Lean_addMacroScope(v___y_526_, v___x_574_, v___y_524_);
v___x_576_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_576_, 0, v___y_525_);
lean_ctor_set(v___x_576_, 1, v___x_573_);
lean_ctor_set(v___x_576_, 2, v___x_575_);
lean_ctor_set(v___x_576_, 3, v___x_552_);
lean_inc_ref(v___x_576_);
v___x_577_ = l_Lean_Syntax_node2(v___y_525_, v___y_522_, v___x_576_, v___y_528_);
v___x_578_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_578_, 0, v___y_525_);
lean_ctor_set(v___x_578_, 1, v___y_522_);
lean_ctor_set(v___x_578_, 2, v___y_527_);
v___x_579_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_580_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_580_, 0, v___y_525_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_582_ = l_Lean_Name_mkStr4(v___y_521_, v___x_534_, v___x_535_, v___x_581_);
v___x_583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_583_, 0, v___y_525_);
lean_ctor_set(v___x_583_, 1, v___x_581_);
v___x_584_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_585_ = l_Lean_Name_mkStr4(v___y_521_, v___x_534_, v___x_535_, v___x_584_);
lean_inc_ref_n(v___x_578_, 3);
v___x_586_ = l_Lean_Syntax_node2(v___y_525_, v___x_585_, v___x_578_, v___x_576_);
v___x_587_ = l_Lean_Syntax_node1(v___y_525_, v___y_522_, v___x_586_);
v___x_588_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_589_, 0, v___y_525_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_591_ = l_Lean_Name_mkStr4(v___y_521_, v___x_534_, v___x_535_, v___x_590_);
v___x_592_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_593_ = l_Lean_Name_mkStr4(v___y_521_, v___x_534_, v___x_535_, v___x_592_);
v___x_594_ = l_Array_append___redArg(v___y_527_, v_a_514_);
lean_dec(v_a_514_);
v___x_595_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_596_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_596_, 0, v___y_525_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_598_ = l_Lean_Name_mkStr4(v___y_521_, v___x_534_, v___x_535_, v___x_597_);
v___x_599_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_600_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_600_, 0, v___y_525_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = l_Lean_Syntax_node1(v___y_525_, v___x_598_, v___x_600_);
v___x_602_ = l_Lean_Syntax_node1(v___y_525_, v___y_522_, v___x_601_);
v___x_603_ = l_Lean_Syntax_node1(v___y_525_, v___y_522_, v___x_602_);
v___x_604_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_605_ = l_Lean_Name_mkStr4(v___y_521_, v___x_534_, v___x_535_, v___x_604_);
v___x_606_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_607_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_607_, 0, v___y_525_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_609_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__30, &l_Lean_Elab_Command_elabElabRulesAux___closed__30_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30);
v___x_610_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_611_ = l_Lean_addMacroScope(v___y_526_, v___x_610_, v___y_524_);
v___x_612_ = l_Lean_Name_mkStr3(v___y_521_, v___y_530_, v___x_608_);
v___x_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___x_552_);
v___x_614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_552_);
v___x_615_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_615_, 0, v___y_525_);
lean_ctor_set(v___x_615_, 1, v___x_609_);
lean_ctor_set(v___x_615_, 2, v___x_611_);
lean_ctor_set(v___x_615_, 3, v___x_614_);
v___x_616_ = l_Lean_Syntax_node2(v___y_525_, v___x_605_, v___x_607_, v___x_615_);
lean_inc_ref(v___x_580_);
v___x_617_ = l_Lean_Syntax_node4(v___y_525_, v___x_593_, v___x_596_, v___x_603_, v___x_580_, v___x_616_);
v___x_618_ = lean_array_push(v___x_594_, v___x_617_);
v___x_619_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_619_, 0, v___y_525_);
lean_ctor_set(v___x_619_, 1, v___y_522_);
lean_ctor_set(v___x_619_, 2, v___x_618_);
v___x_620_ = l_Lean_Syntax_node1(v___y_525_, v___x_591_, v___x_619_);
v___x_621_ = l_Lean_Syntax_node6(v___y_525_, v___x_582_, v___x_583_, v___x_578_, v___x_578_, v___x_587_, v___x_589_, v___x_620_);
v___x_622_ = l_Lean_Syntax_node4(v___y_525_, v___x_572_, v___x_577_, v___x_578_, v___x_580_, v___x_621_);
v___x_623_ = l_Lean_Syntax_node2(v___y_525_, v___x_569_, v___x_570_, v___x_622_);
v___x_624_ = lean_unsigned_to_nat(9u);
v___x_625_ = lean_mk_empty_array_with_capacity(v___x_624_);
v___x_626_ = lean_array_push(v___x_625_, v___x_533_);
v___x_627_ = lean_array_push(v___x_626_, v___x_547_);
v___x_628_ = lean_array_push(v___x_627_, v___y_529_);
v___x_629_ = lean_array_push(v___x_628_, v___x_548_);
v___x_630_ = lean_array_push(v___x_629_, v___x_555_);
v___x_631_ = lean_array_push(v___x_630_, v___x_557_);
v___x_632_ = lean_array_push(v___x_631_, v___x_565_);
v___x_633_ = lean_array_push(v___x_632_, v___x_567_);
v___x_634_ = lean_array_push(v___x_633_, v___x_623_);
lean_inc(v___y_520_);
v___x_635_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_635_, 0, v___y_525_);
lean_ctor_set(v___x_635_, 1, v___y_520_);
lean_ctor_set(v___x_635_, 2, v___x_634_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_635_);
v___x_637_ = v___x_516_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
v___jp_639_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_646_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_647_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_648_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_649_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
v___x_650_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_651_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_501_) == 1)
{
lean_object* v_val_652_; lean_object* v___x_653_; 
v_val_652_ = lean_ctor_get(v_doc_x3f_501_, 0);
lean_inc(v_val_652_);
lean_dec_ref_known(v_doc_x3f_501_, 1);
v___x_653_ = l_Array_mkArray1___redArg(v_val_652_);
v___y_519_ = v___x_648_;
v___y_520_ = v___x_649_;
v___y_521_ = v___x_646_;
v___y_522_ = v___x_650_;
v___y_523_ = v___y_643_;
v___y_524_ = v___y_644_;
v___y_525_ = v___y_640_;
v___y_526_ = v_a_645_;
v___y_527_ = v___x_651_;
v___y_528_ = v___y_641_;
v___y_529_ = v___y_642_;
v___y_530_ = v___x_647_;
v___y_531_ = v___x_653_;
goto v___jp_518_;
}
else
{
lean_object* v___x_654_; 
lean_dec(v_doc_x3f_501_);
v___x_654_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_519_ = v___x_648_;
v___y_520_ = v___x_649_;
v___y_521_ = v___x_646_;
v___y_522_ = v___x_650_;
v___y_523_ = v___y_643_;
v___y_524_ = v___y_644_;
v___y_525_ = v___y_640_;
v___y_526_ = v_a_645_;
v___y_527_ = v___x_651_;
v___y_528_ = v___y_641_;
v___y_529_ = v___y_642_;
v___y_530_ = v___x_647_;
v___y_531_ = v___x_654_;
goto v___jp_518_;
}
}
v___jp_655_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_inc_ref_n(v___y_657_, 4);
v___x_669_ = l_Array_append___redArg(v___y_657_, v___y_668_);
lean_dec_ref(v___y_668_);
lean_inc_n(v___y_656_, 12);
lean_inc_n(v___y_660_, 42);
v___x_670_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_670_, 0, v___y_660_);
lean_ctor_set(v___x_670_, 1, v___y_656_);
lean_ctor_set(v___x_670_, 2, v___x_669_);
v___x_671_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_672_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_673_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_667_, 13);
v___x_674_ = l_Lean_Name_mkStr4(v___y_667_, v___x_671_, v___x_672_, v___x_673_);
v___x_675_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_676_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_676_, 0, v___y_660_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_678_ = l_Lean_Syntax_SepArray_ofElems(v___x_677_, v___y_666_);
lean_dec_ref(v___y_666_);
v___x_679_ = l_Array_append___redArg(v___y_657_, v___x_678_);
lean_dec_ref(v___x_678_);
v___x_680_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_680_, 0, v___y_660_);
lean_ctor_set(v___x_680_, 1, v___y_656_);
lean_ctor_set(v___x_680_, 2, v___x_679_);
v___x_681_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_682_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_682_, 0, v___y_660_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = l_Lean_Syntax_node3(v___y_660_, v___x_674_, v___x_676_, v___x_680_, v___x_682_);
v___x_684_ = l_Lean_Syntax_node1(v___y_660_, v___y_656_, v___x_683_);
lean_inc_ref(v___y_664_);
v___x_685_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_685_, 0, v___y_660_);
lean_ctor_set(v___x_685_, 1, v___y_664_);
v___x_686_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_687_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_659_, 5);
lean_inc_n(v___y_662_, 5);
v___x_688_ = l_Lean_addMacroScope(v___y_662_, v___x_687_, v___y_659_);
v___x_689_ = lean_box(0);
v___x_690_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_690_, 0, v___y_660_);
lean_ctor_set(v___x_690_, 1, v___x_686_);
lean_ctor_set(v___x_690_, 2, v___x_688_);
lean_ctor_set(v___x_690_, 3, v___x_689_);
v___x_691_ = l_Lean_mkIdent(v_k_504_);
v___x_692_ = l_Lean_Syntax_node2(v___y_660_, v___y_656_, v___x_690_, v___x_691_);
v___x_693_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_694_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_694_, 0, v___y_660_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__39, &l_Lean_Elab_Command_elabElabRulesAux___closed__39_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__39);
v___x_696_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__40));
lean_inc_ref_n(v___y_658_, 3);
v___x_697_ = l_Lean_Name_mkStr4(v___y_667_, v___y_658_, v___x_672_, v___x_696_);
lean_inc(v___x_697_);
v___x_698_ = l_Lean_addMacroScope(v___y_662_, v___x_697_, v___y_659_);
v___x_699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_689_);
v___x_700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v___x_689_);
v___x_701_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_701_, 0, v___y_660_);
lean_ctor_set(v___x_701_, 1, v___x_695_);
lean_ctor_set(v___x_701_, 2, v___x_698_);
lean_ctor_set(v___x_701_, 3, v___x_700_);
v___x_702_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_703_, 0, v___y_660_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_705_ = l_Lean_Name_mkStr4(v___y_667_, v___x_671_, v___x_672_, v___x_704_);
v___x_706_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_706_, 0, v___y_660_);
lean_ctor_set(v___x_706_, 1, v___x_704_);
v___x_707_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_708_ = l_Lean_Name_mkStr4(v___y_667_, v___x_671_, v___x_672_, v___x_707_);
v___x_709_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_710_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_711_ = l_Lean_addMacroScope(v___y_662_, v___x_710_, v___y_659_);
v___x_712_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_712_, 0, v___y_660_);
lean_ctor_set(v___x_712_, 1, v___x_709_);
lean_ctor_set(v___x_712_, 2, v___x_711_);
lean_ctor_set(v___x_712_, 3, v___x_689_);
v___x_713_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__42, &l_Lean_Elab_Command_elabElabRulesAux___closed__42_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__42);
v___x_714_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__43));
v___x_715_ = l_Lean_addMacroScope(v___y_662_, v___x_714_, v___y_659_);
v___x_716_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_716_, 0, v___y_660_);
lean_ctor_set(v___x_716_, 1, v___x_713_);
lean_ctor_set(v___x_716_, 2, v___x_715_);
lean_ctor_set(v___x_716_, 3, v___x_689_);
lean_inc_ref(v___x_716_);
lean_inc_ref(v___x_712_);
v___x_717_ = l_Lean_Syntax_node2(v___y_660_, v___y_656_, v___x_712_, v___x_716_);
v___x_718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_718_, 0, v___y_660_);
lean_ctor_set(v___x_718_, 1, v___y_656_);
lean_ctor_set(v___x_718_, 2, v___y_657_);
v___x_719_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_720_, 0, v___y_660_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__44));
v___x_722_ = l_Lean_Name_mkStr4(v___y_667_, v___x_671_, v___x_672_, v___x_721_);
v___x_723_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__46, &l_Lean_Elab_Command_elabElabRulesAux___closed__46_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__46);
v___x_724_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__47));
v___x_725_ = l_Lean_Name_mkStr4(v___y_667_, v___y_658_, v___x_672_, v___x_724_);
lean_inc(v___x_725_);
v___x_726_ = l_Lean_addMacroScope(v___y_662_, v___x_725_, v___y_659_);
v___x_727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_689_);
v___x_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v___x_689_);
v___x_729_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_729_, 0, v___y_660_);
lean_ctor_set(v___x_729_, 1, v___x_723_);
lean_ctor_set(v___x_729_, 2, v___x_726_);
lean_ctor_set(v___x_729_, 3, v___x_728_);
v___x_730_ = l_Lean_Syntax_node1(v___y_660_, v___y_656_, v___y_661_);
v___x_731_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_732_ = l_Lean_Name_mkStr4(v___y_667_, v___x_671_, v___x_672_, v___x_731_);
v___x_733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_733_, 0, v___y_660_);
lean_ctor_set(v___x_733_, 1, v___x_731_);
v___x_734_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_735_ = l_Lean_Name_mkStr4(v___y_667_, v___x_671_, v___x_672_, v___x_734_);
lean_inc_ref_n(v___x_718_, 4);
v___x_736_ = l_Lean_Syntax_node2(v___y_660_, v___x_735_, v___x_718_, v___x_712_);
v___x_737_ = l_Lean_Syntax_node1(v___y_660_, v___y_656_, v___x_736_);
v___x_738_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_739_, 0, v___y_660_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_741_ = l_Lean_Name_mkStr4(v___y_667_, v___x_671_, v___x_672_, v___x_740_);
v___x_742_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_743_ = l_Lean_Name_mkStr4(v___y_667_, v___x_671_, v___x_672_, v___x_742_);
v___x_744_ = l_Array_append___redArg(v___y_657_, v_a_514_);
lean_dec(v_a_514_);
v___x_745_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_746_, 0, v___y_660_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_748_ = l_Lean_Name_mkStr4(v___y_667_, v___x_671_, v___x_672_, v___x_747_);
v___x_749_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_750_, 0, v___y_660_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = l_Lean_Syntax_node1(v___y_660_, v___x_748_, v___x_750_);
v___x_752_ = l_Lean_Syntax_node1(v___y_660_, v___y_656_, v___x_751_);
v___x_753_ = l_Lean_Syntax_node1(v___y_660_, v___y_656_, v___x_752_);
v___x_754_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_755_ = l_Lean_Name_mkStr4(v___y_667_, v___x_671_, v___x_672_, v___x_754_);
v___x_756_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_757_, 0, v___y_660_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_759_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__30, &l_Lean_Elab_Command_elabElabRulesAux___closed__30_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30);
v___x_760_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_761_ = l_Lean_addMacroScope(v___y_662_, v___x_760_, v___y_659_);
v___x_762_ = l_Lean_Name_mkStr3(v___y_667_, v___y_658_, v___x_758_);
v___x_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v___x_689_);
v___x_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
lean_ctor_set(v___x_764_, 1, v___x_689_);
v___x_765_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_765_, 0, v___y_660_);
lean_ctor_set(v___x_765_, 1, v___x_759_);
lean_ctor_set(v___x_765_, 2, v___x_761_);
lean_ctor_set(v___x_765_, 3, v___x_764_);
v___x_766_ = l_Lean_Syntax_node2(v___y_660_, v___x_755_, v___x_757_, v___x_765_);
lean_inc_ref_n(v___x_720_, 2);
v___x_767_ = l_Lean_Syntax_node4(v___y_660_, v___x_743_, v___x_746_, v___x_753_, v___x_720_, v___x_766_);
v___x_768_ = lean_array_push(v___x_744_, v___x_767_);
v___x_769_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_769_, 0, v___y_660_);
lean_ctor_set(v___x_769_, 1, v___y_656_);
lean_ctor_set(v___x_769_, 2, v___x_768_);
v___x_770_ = l_Lean_Syntax_node1(v___y_660_, v___x_741_, v___x_769_);
v___x_771_ = l_Lean_Syntax_node6(v___y_660_, v___x_732_, v___x_733_, v___x_718_, v___x_718_, v___x_737_, v___x_739_, v___x_770_);
lean_inc(v___x_708_);
v___x_772_ = l_Lean_Syntax_node4(v___y_660_, v___x_708_, v___x_730_, v___x_718_, v___x_720_, v___x_771_);
lean_inc_ref(v___x_706_);
lean_inc(v___x_705_);
v___x_773_ = l_Lean_Syntax_node2(v___y_660_, v___x_705_, v___x_706_, v___x_772_);
v___x_774_ = l_Lean_Syntax_node2(v___y_660_, v___y_656_, v___x_716_, v___x_773_);
v___x_775_ = l_Lean_Syntax_node2(v___y_660_, v___x_722_, v___x_729_, v___x_774_);
v___x_776_ = l_Lean_Syntax_node4(v___y_660_, v___x_708_, v___x_717_, v___x_718_, v___x_720_, v___x_775_);
v___x_777_ = l_Lean_Syntax_node2(v___y_660_, v___x_705_, v___x_706_, v___x_776_);
v___x_778_ = lean_unsigned_to_nat(9u);
v___x_779_ = lean_mk_empty_array_with_capacity(v___x_778_);
v___x_780_ = lean_array_push(v___x_779_, v___x_670_);
v___x_781_ = lean_array_push(v___x_780_, v___x_684_);
v___x_782_ = lean_array_push(v___x_781_, v___y_663_);
v___x_783_ = lean_array_push(v___x_782_, v___x_685_);
v___x_784_ = lean_array_push(v___x_783_, v___x_692_);
v___x_785_ = lean_array_push(v___x_784_, v___x_694_);
v___x_786_ = lean_array_push(v___x_785_, v___x_701_);
v___x_787_ = lean_array_push(v___x_786_, v___x_703_);
v___x_788_ = lean_array_push(v___x_787_, v___x_777_);
lean_inc(v___y_665_);
v___x_789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_789_, 0, v___y_660_);
lean_ctor_set(v___x_789_, 1, v___y_665_);
lean_ctor_set(v___x_789_, 2, v___x_788_);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
return v___x_790_;
}
v___jp_791_:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_798_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_799_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_800_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_801_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
v___x_802_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_803_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_501_) == 1)
{
lean_object* v_val_804_; lean_object* v___x_805_; 
v_val_804_ = lean_ctor_get(v_doc_x3f_501_, 0);
lean_inc(v_val_804_);
lean_dec_ref_known(v_doc_x3f_501_, 1);
v___x_805_ = l_Array_mkArray1___redArg(v_val_804_);
v___y_656_ = v___x_802_;
v___y_657_ = v___x_803_;
v___y_658_ = v___x_799_;
v___y_659_ = v___y_794_;
v___y_660_ = v___y_792_;
v___y_661_ = v___y_793_;
v___y_662_ = v_a_797_;
v___y_663_ = v___y_795_;
v___y_664_ = v___x_800_;
v___y_665_ = v___x_801_;
v___y_666_ = v___y_796_;
v___y_667_ = v___x_798_;
v___y_668_ = v___x_805_;
goto v___jp_655_;
}
else
{
lean_object* v___x_806_; 
lean_dec(v_doc_x3f_501_);
v___x_806_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_656_ = v___x_802_;
v___y_657_ = v___x_803_;
v___y_658_ = v___x_799_;
v___y_659_ = v___y_794_;
v___y_660_ = v___y_792_;
v___y_661_ = v___y_793_;
v___y_662_ = v_a_797_;
v___y_663_ = v___y_795_;
v___y_664_ = v___x_800_;
v___y_665_ = v___x_801_;
v___y_666_ = v___y_796_;
v___y_667_ = v___x_798_;
v___y_668_ = v___x_806_;
goto v___jp_655_;
}
}
v___jp_807_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
lean_inc_ref_n(v___y_810_, 3);
v___x_820_ = l_Array_append___redArg(v___y_810_, v___y_819_);
lean_dec_ref(v___y_819_);
lean_inc_n(v___y_809_, 7);
lean_inc_n(v___y_817_, 26);
v___x_821_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_821_, 0, v___y_817_);
lean_ctor_set(v___x_821_, 1, v___y_809_);
lean_ctor_set(v___x_821_, 2, v___x_820_);
v___x_822_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_823_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_824_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_813_, 8);
v___x_825_ = l_Lean_Name_mkStr4(v___y_813_, v___x_822_, v___x_823_, v___x_824_);
v___x_826_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_827_, 0, v___y_817_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_829_ = l_Lean_Syntax_SepArray_ofElems(v___x_828_, v___y_816_);
lean_dec_ref(v___y_816_);
v___x_830_ = l_Array_append___redArg(v___y_810_, v___x_829_);
lean_dec_ref(v___x_829_);
v___x_831_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_831_, 0, v___y_817_);
lean_ctor_set(v___x_831_, 1, v___y_809_);
lean_ctor_set(v___x_831_, 2, v___x_830_);
v___x_832_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_833_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_833_, 0, v___y_817_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = l_Lean_Syntax_node3(v___y_817_, v___x_825_, v___x_827_, v___x_831_, v___x_833_);
v___x_835_ = l_Lean_Syntax_node1(v___y_817_, v___y_809_, v___x_834_);
lean_inc_ref(v___y_815_);
v___x_836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_836_, 0, v___y_817_);
lean_ctor_set(v___x_836_, 1, v___y_815_);
v___x_837_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_838_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_812_, 2);
lean_inc_n(v___y_818_, 2);
v___x_839_ = l_Lean_addMacroScope(v___y_818_, v___x_838_, v___y_812_);
v___x_840_ = lean_box(0);
v___x_841_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_841_, 0, v___y_817_);
lean_ctor_set(v___x_841_, 1, v___x_837_);
lean_ctor_set(v___x_841_, 2, v___x_839_);
lean_ctor_set(v___x_841_, 3, v___x_840_);
v___x_842_ = l_Lean_mkIdent(v_k_504_);
v___x_843_ = l_Lean_Syntax_node2(v___y_817_, v___y_809_, v___x_841_, v___x_842_);
v___x_844_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_845_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_845_, 0, v___y_817_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__49, &l_Lean_Elab_Command_elabElabRulesAux___closed__49_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__49);
v___x_847_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__50));
lean_inc_ref_n(v___y_814_, 2);
v___x_848_ = l_Lean_Name_mkStr4(v___y_813_, v___y_814_, v___x_847_, v___x_847_);
lean_inc(v___x_848_);
v___x_849_ = l_Lean_addMacroScope(v___y_818_, v___x_848_, v___y_812_);
v___x_850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_840_);
v___x_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v___x_840_);
v___x_852_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_852_, 0, v___y_817_);
lean_ctor_set(v___x_852_, 1, v___x_846_);
lean_ctor_set(v___x_852_, 2, v___x_849_);
lean_ctor_set(v___x_852_, 3, v___x_851_);
v___x_853_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_854_, 0, v___y_817_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_856_ = l_Lean_Name_mkStr4(v___y_813_, v___x_822_, v___x_823_, v___x_855_);
v___x_857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_857_, 0, v___y_817_);
lean_ctor_set(v___x_857_, 1, v___x_855_);
v___x_858_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_859_ = l_Lean_Name_mkStr4(v___y_813_, v___x_822_, v___x_823_, v___x_858_);
v___x_860_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_861_ = l_Lean_Name_mkStr4(v___y_813_, v___x_822_, v___x_823_, v___x_860_);
v___x_862_ = l_Array_append___redArg(v___y_810_, v_a_514_);
lean_dec(v_a_514_);
v___x_863_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_864_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_864_, 0, v___y_817_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_866_ = l_Lean_Name_mkStr4(v___y_813_, v___x_822_, v___x_823_, v___x_865_);
v___x_867_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_868_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_868_, 0, v___y_817_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_Lean_Syntax_node1(v___y_817_, v___x_866_, v___x_868_);
v___x_870_ = l_Lean_Syntax_node1(v___y_817_, v___y_809_, v___x_869_);
v___x_871_ = l_Lean_Syntax_node1(v___y_817_, v___y_809_, v___x_870_);
v___x_872_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_873_, 0, v___y_817_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_875_ = l_Lean_Name_mkStr4(v___y_813_, v___x_822_, v___x_823_, v___x_874_);
v___x_876_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_877_, 0, v___y_817_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_879_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__30, &l_Lean_Elab_Command_elabElabRulesAux___closed__30_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30);
v___x_880_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_881_ = l_Lean_addMacroScope(v___y_818_, v___x_880_, v___y_812_);
v___x_882_ = l_Lean_Name_mkStr3(v___y_813_, v___y_814_, v___x_878_);
v___x_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v___x_840_);
v___x_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v___x_840_);
v___x_885_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_885_, 0, v___y_817_);
lean_ctor_set(v___x_885_, 1, v___x_879_);
lean_ctor_set(v___x_885_, 2, v___x_881_);
lean_ctor_set(v___x_885_, 3, v___x_884_);
v___x_886_ = l_Lean_Syntax_node2(v___y_817_, v___x_875_, v___x_877_, v___x_885_);
v___x_887_ = l_Lean_Syntax_node4(v___y_817_, v___x_861_, v___x_864_, v___x_871_, v___x_873_, v___x_886_);
v___x_888_ = lean_array_push(v___x_862_, v___x_887_);
v___x_889_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_889_, 0, v___y_817_);
lean_ctor_set(v___x_889_, 1, v___y_809_);
lean_ctor_set(v___x_889_, 2, v___x_888_);
v___x_890_ = l_Lean_Syntax_node1(v___y_817_, v___x_859_, v___x_889_);
v___x_891_ = l_Lean_Syntax_node2(v___y_817_, v___x_856_, v___x_857_, v___x_890_);
v___x_892_ = lean_unsigned_to_nat(9u);
v___x_893_ = lean_mk_empty_array_with_capacity(v___x_892_);
v___x_894_ = lean_array_push(v___x_893_, v___x_821_);
v___x_895_ = lean_array_push(v___x_894_, v___x_835_);
v___x_896_ = lean_array_push(v___x_895_, v___y_811_);
v___x_897_ = lean_array_push(v___x_896_, v___x_836_);
v___x_898_ = lean_array_push(v___x_897_, v___x_843_);
v___x_899_ = lean_array_push(v___x_898_, v___x_845_);
v___x_900_ = lean_array_push(v___x_899_, v___x_852_);
v___x_901_ = lean_array_push(v___x_900_, v___x_854_);
v___x_902_ = lean_array_push(v___x_901_, v___x_891_);
lean_inc(v___y_808_);
v___x_903_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_903_, 0, v___y_817_);
lean_ctor_set(v___x_903_, 1, v___y_808_);
lean_ctor_set(v___x_903_, 2, v___x_902_);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
return v___x_904_;
}
v___jp_905_:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_911_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_912_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_913_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_914_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
v___x_915_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_916_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_501_) == 1)
{
lean_object* v_val_917_; lean_object* v___x_918_; 
v_val_917_ = lean_ctor_get(v_doc_x3f_501_, 0);
lean_inc(v_val_917_);
lean_dec_ref_known(v_doc_x3f_501_, 1);
v___x_918_ = l_Array_mkArray1___redArg(v_val_917_);
v___y_808_ = v___x_914_;
v___y_809_ = v___x_915_;
v___y_810_ = v___x_916_;
v___y_811_ = v___y_907_;
v___y_812_ = v___y_906_;
v___y_813_ = v___x_911_;
v___y_814_ = v___x_912_;
v___y_815_ = v___x_913_;
v___y_816_ = v___y_908_;
v___y_817_ = v___y_909_;
v___y_818_ = v_a_910_;
v___y_819_ = v___x_918_;
goto v___jp_807_;
}
else
{
lean_object* v___x_919_; 
lean_dec(v_doc_x3f_501_);
v___x_919_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_808_ = v___x_914_;
v___y_809_ = v___x_915_;
v___y_810_ = v___x_916_;
v___y_811_ = v___y_907_;
v___y_812_ = v___y_906_;
v___y_813_ = v___x_911_;
v___y_814_ = v___x_912_;
v___y_815_ = v___x_913_;
v___y_816_ = v___y_908_;
v___y_817_ = v___y_909_;
v___y_818_ = v_a_910_;
v___y_819_ = v___x_919_;
goto v___jp_807_;
}
}
v___jp_920_:
{
lean_object* v___x_926_; 
lean_inc(v___y_923_);
lean_inc(v_k_504_);
v___x_926_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_504_, v_attrKind_503_, v_attrs_x3f_502_, v___y_923_, v___y_921_, v___y_925_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_928_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref_known(v___x_926_, 1);
v___x_928_ = l_Lean_Elab_Command_getRef___redArg(v___y_921_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_928_, 1);
v___x_930_ = l_Lean_SourceInfo_fromRef(v_a_929_, v___y_924_);
lean_dec(v_a_929_);
v___x_931_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_921_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_quotContext_x3f_932_; 
v_quotContext_x3f_932_ = lean_ctor_get(v___y_921_, 5);
if (lean_obj_tag(v_quotContext_x3f_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_934_; lean_object* v_a_935_; 
v_a_933_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_931_, 1);
v___x_934_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_925_);
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
lean_dec_ref(v___x_934_);
v___y_906_ = v_a_933_;
v___y_907_ = v___y_922_;
v___y_908_ = v_a_927_;
v___y_909_ = v___x_930_;
v_a_910_ = v_a_935_;
goto v___jp_905_;
}
else
{
lean_object* v_a_936_; lean_object* v_val_937_; 
v_a_936_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_931_, 1);
v_val_937_ = lean_ctor_get(v_quotContext_x3f_932_, 0);
lean_inc(v_val_937_);
v___y_906_ = v_a_936_;
v___y_907_ = v___y_922_;
v___y_908_ = v_a_927_;
v___y_909_ = v___x_930_;
v_a_910_ = v_val_937_;
goto v___jp_905_;
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec(v___x_930_);
lean_dec(v_a_927_);
lean_dec(v___y_922_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_938_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_931_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_931_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
else
{
lean_dec(v_a_927_);
lean_dec(v___y_922_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
return v___x_928_;
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec(v___y_922_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_946_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_926_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_926_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
v___jp_954_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_inc_ref_n(v___y_958_, 4);
v___x_967_ = l_Array_append___redArg(v___y_958_, v___y_966_);
lean_dec_ref(v___y_966_);
lean_inc_n(v___y_957_, 10);
lean_inc_n(v___y_962_, 36);
v___x_968_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_968_, 0, v___y_962_);
lean_ctor_set(v___x_968_, 1, v___y_957_);
lean_ctor_set(v___x_968_, 2, v___x_967_);
v___x_969_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_970_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_971_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_964_, 11);
v___x_972_ = l_Lean_Name_mkStr4(v___y_964_, v___x_969_, v___x_970_, v___x_971_);
v___x_973_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_974_, 0, v___y_962_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_976_ = l_Lean_Syntax_SepArray_ofElems(v___x_975_, v___y_956_);
lean_dec_ref(v___y_956_);
v___x_977_ = l_Array_append___redArg(v___y_958_, v___x_976_);
lean_dec_ref(v___x_976_);
v___x_978_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_978_, 0, v___y_962_);
lean_ctor_set(v___x_978_, 1, v___y_957_);
lean_ctor_set(v___x_978_, 2, v___x_977_);
v___x_979_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_980_, 0, v___y_962_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = l_Lean_Syntax_node3(v___y_962_, v___x_972_, v___x_974_, v___x_978_, v___x_980_);
v___x_982_ = l_Lean_Syntax_node1(v___y_962_, v___y_957_, v___x_981_);
lean_inc_ref(v___y_959_);
v___x_983_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_983_, 0, v___y_962_);
lean_ctor_set(v___x_983_, 1, v___y_959_);
v___x_984_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_985_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_961_, 4);
lean_inc_n(v___y_965_, 4);
v___x_986_ = l_Lean_addMacroScope(v___y_965_, v___x_985_, v___y_961_);
v___x_987_ = lean_box(0);
v___x_988_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_988_, 0, v___y_962_);
lean_ctor_set(v___x_988_, 1, v___x_984_);
lean_ctor_set(v___x_988_, 2, v___x_986_);
lean_ctor_set(v___x_988_, 3, v___x_987_);
v___x_989_ = l_Lean_mkIdent(v_k_504_);
v___x_990_ = l_Lean_Syntax_node2(v___y_962_, v___y_957_, v___x_988_, v___x_989_);
v___x_991_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_992_, 0, v___y_962_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_994_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
v___x_995_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc_ref_n(v___y_955_, 2);
v___x_996_ = l_Lean_Name_mkStr4(v___y_964_, v___y_955_, v___x_994_, v___x_995_);
lean_inc(v___x_996_);
v___x_997_ = l_Lean_addMacroScope(v___y_965_, v___x_996_, v___y_961_);
v___x_998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_987_);
v___x_999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_987_);
v___x_1000_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1000_, 0, v___y_962_);
lean_ctor_set(v___x_1000_, 1, v___x_993_);
lean_ctor_set(v___x_1000_, 2, v___x_997_);
lean_ctor_set(v___x_1000_, 3, v___x_999_);
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___y_962_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1004_ = l_Lean_Name_mkStr4(v___y_964_, v___x_969_, v___x_970_, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___y_962_);
lean_ctor_set(v___x_1005_, 1, v___x_1003_);
v___x_1006_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_1007_ = l_Lean_Name_mkStr4(v___y_964_, v___x_969_, v___x_970_, v___x_1006_);
v___x_1008_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_1009_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1010_ = l_Lean_addMacroScope(v___y_965_, v___x_1009_, v___y_961_);
v___x_1011_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1011_, 0, v___y_962_);
lean_ctor_set(v___x_1011_, 1, v___x_1008_);
lean_ctor_set(v___x_1011_, 2, v___x_1010_);
lean_ctor_set(v___x_1011_, 3, v___x_987_);
v___x_1012_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__52, &l_Lean_Elab_Command_elabElabRulesAux___closed__52_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__52);
v___x_1013_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__53));
v___x_1014_ = l_Lean_addMacroScope(v___y_965_, v___x_1013_, v___y_961_);
v___x_1015_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1015_, 0, v___y_962_);
lean_ctor_set(v___x_1015_, 1, v___x_1012_);
lean_ctor_set(v___x_1015_, 2, v___x_1014_);
lean_ctor_set(v___x_1015_, 3, v___x_987_);
lean_inc_ref(v___x_1011_);
v___x_1016_ = l_Lean_Syntax_node2(v___y_962_, v___y_957_, v___x_1011_, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1017_, 0, v___y_962_);
lean_ctor_set(v___x_1017_, 1, v___y_957_);
lean_ctor_set(v___x_1017_, 2, v___y_958_);
v___x_1018_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1019_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___y_962_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_1021_ = l_Lean_Name_mkStr4(v___y_964_, v___x_969_, v___x_970_, v___x_1020_);
v___x_1022_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___y_962_);
lean_ctor_set(v___x_1022_, 1, v___x_1020_);
v___x_1023_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_1024_ = l_Lean_Name_mkStr4(v___y_964_, v___x_969_, v___x_970_, v___x_1023_);
lean_inc_ref_n(v___x_1017_, 3);
v___x_1025_ = l_Lean_Syntax_node2(v___y_962_, v___x_1024_, v___x_1017_, v___x_1011_);
v___x_1026_ = l_Lean_Syntax_node1(v___y_962_, v___y_957_, v___x_1025_);
v___x_1027_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1028_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___y_962_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1030_ = l_Lean_Name_mkStr4(v___y_964_, v___x_969_, v___x_970_, v___x_1029_);
v___x_1031_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1032_ = l_Lean_Name_mkStr4(v___y_964_, v___x_969_, v___x_970_, v___x_1031_);
v___x_1033_ = l_Array_append___redArg(v___y_958_, v_a_514_);
lean_dec(v_a_514_);
v___x_1034_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1035_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___y_962_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1037_ = l_Lean_Name_mkStr4(v___y_964_, v___x_969_, v___x_970_, v___x_1036_);
v___x_1038_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___y_962_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = l_Lean_Syntax_node1(v___y_962_, v___x_1037_, v___x_1039_);
v___x_1041_ = l_Lean_Syntax_node1(v___y_962_, v___y_957_, v___x_1040_);
v___x_1042_ = l_Lean_Syntax_node1(v___y_962_, v___y_957_, v___x_1041_);
v___x_1043_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1044_ = l_Lean_Name_mkStr4(v___y_964_, v___x_969_, v___x_970_, v___x_1043_);
v___x_1045_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___y_962_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1048_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__30, &l_Lean_Elab_Command_elabElabRulesAux___closed__30_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30);
v___x_1049_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1050_ = l_Lean_addMacroScope(v___y_965_, v___x_1049_, v___y_961_);
v___x_1051_ = l_Lean_Name_mkStr3(v___y_964_, v___y_955_, v___x_1047_);
v___x_1052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v___x_987_);
v___x_1053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v___x_987_);
v___x_1054_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1054_, 0, v___y_962_);
lean_ctor_set(v___x_1054_, 1, v___x_1048_);
lean_ctor_set(v___x_1054_, 2, v___x_1050_);
lean_ctor_set(v___x_1054_, 3, v___x_1053_);
v___x_1055_ = l_Lean_Syntax_node2(v___y_962_, v___x_1044_, v___x_1046_, v___x_1054_);
lean_inc_ref(v___x_1019_);
v___x_1056_ = l_Lean_Syntax_node4(v___y_962_, v___x_1032_, v___x_1035_, v___x_1042_, v___x_1019_, v___x_1055_);
v___x_1057_ = lean_array_push(v___x_1033_, v___x_1056_);
v___x_1058_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1058_, 0, v___y_962_);
lean_ctor_set(v___x_1058_, 1, v___y_957_);
lean_ctor_set(v___x_1058_, 2, v___x_1057_);
v___x_1059_ = l_Lean_Syntax_node1(v___y_962_, v___x_1030_, v___x_1058_);
v___x_1060_ = l_Lean_Syntax_node6(v___y_962_, v___x_1021_, v___x_1022_, v___x_1017_, v___x_1017_, v___x_1026_, v___x_1028_, v___x_1059_);
v___x_1061_ = l_Lean_Syntax_node4(v___y_962_, v___x_1007_, v___x_1016_, v___x_1017_, v___x_1019_, v___x_1060_);
v___x_1062_ = l_Lean_Syntax_node2(v___y_962_, v___x_1004_, v___x_1005_, v___x_1061_);
v___x_1063_ = lean_unsigned_to_nat(9u);
v___x_1064_ = lean_mk_empty_array_with_capacity(v___x_1063_);
v___x_1065_ = lean_array_push(v___x_1064_, v___x_968_);
v___x_1066_ = lean_array_push(v___x_1065_, v___x_982_);
v___x_1067_ = lean_array_push(v___x_1066_, v___y_963_);
v___x_1068_ = lean_array_push(v___x_1067_, v___x_983_);
v___x_1069_ = lean_array_push(v___x_1068_, v___x_990_);
v___x_1070_ = lean_array_push(v___x_1069_, v___x_992_);
v___x_1071_ = lean_array_push(v___x_1070_, v___x_1000_);
v___x_1072_ = lean_array_push(v___x_1071_, v___x_1002_);
v___x_1073_ = lean_array_push(v___x_1072_, v___x_1062_);
lean_inc(v___y_960_);
v___x_1074_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1074_, 0, v___y_962_);
lean_ctor_set(v___x_1074_, 1, v___y_960_);
lean_ctor_set(v___x_1074_, 2, v___x_1073_);
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
v___jp_1076_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1082_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1083_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1084_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_1085_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
v___x_1086_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1087_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_501_) == 1)
{
lean_object* v_val_1088_; lean_object* v___x_1089_; 
v_val_1088_ = lean_ctor_get(v_doc_x3f_501_, 0);
lean_inc(v_val_1088_);
lean_dec_ref_known(v_doc_x3f_501_, 1);
v___x_1089_ = l_Array_mkArray1___redArg(v_val_1088_);
v___y_955_ = v___x_1083_;
v___y_956_ = v___y_1077_;
v___y_957_ = v___x_1086_;
v___y_958_ = v___x_1087_;
v___y_959_ = v___x_1084_;
v___y_960_ = v___x_1085_;
v___y_961_ = v___y_1079_;
v___y_962_ = v___y_1078_;
v___y_963_ = v___y_1080_;
v___y_964_ = v___x_1082_;
v___y_965_ = v_a_1081_;
v___y_966_ = v___x_1089_;
goto v___jp_954_;
}
else
{
lean_object* v___x_1090_; 
lean_dec(v_doc_x3f_501_);
v___x_1090_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_955_ = v___x_1083_;
v___y_956_ = v___y_1077_;
v___y_957_ = v___x_1086_;
v___y_958_ = v___x_1087_;
v___y_959_ = v___x_1084_;
v___y_960_ = v___x_1085_;
v___y_961_ = v___y_1079_;
v___y_962_ = v___y_1078_;
v___y_963_ = v___y_1080_;
v___y_964_ = v___x_1082_;
v___y_965_ = v_a_1081_;
v___y_966_ = v___x_1090_;
goto v___jp_954_;
}
}
v___jp_1091_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_inc_ref_n(v___y_1092_, 3);
v___x_1105_ = l_Array_append___redArg(v___y_1092_, v___y_1104_);
lean_dec_ref(v___y_1104_);
lean_inc_n(v___y_1099_, 7);
lean_inc_n(v___y_1095_, 26);
v___x_1106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1106_, 0, v___y_1095_);
lean_ctor_set(v___x_1106_, 1, v___y_1099_);
lean_ctor_set(v___x_1106_, 2, v___x_1105_);
v___x_1107_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1108_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1109_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1097_, 8);
v___x_1110_ = l_Lean_Name_mkStr4(v___y_1097_, v___x_1107_, v___x_1108_, v___x_1109_);
v___x_1111_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___y_1095_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1114_ = l_Lean_Syntax_SepArray_ofElems(v___x_1113_, v___y_1096_);
lean_dec_ref(v___y_1096_);
v___x_1115_ = l_Array_append___redArg(v___y_1092_, v___x_1114_);
lean_dec_ref(v___x_1114_);
v___x_1116_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1116_, 0, v___y_1095_);
lean_ctor_set(v___x_1116_, 1, v___y_1099_);
lean_ctor_set(v___x_1116_, 2, v___x_1115_);
v___x_1117_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1118_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___y_1095_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = l_Lean_Syntax_node3(v___y_1095_, v___x_1110_, v___x_1112_, v___x_1116_, v___x_1118_);
v___x_1120_ = l_Lean_Syntax_node1(v___y_1095_, v___y_1099_, v___x_1119_);
lean_inc_ref(v___y_1093_);
v___x_1121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___y_1095_);
lean_ctor_set(v___x_1121_, 1, v___y_1093_);
v___x_1122_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1123_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1102_, 2);
lean_inc_n(v___y_1101_, 2);
v___x_1124_ = l_Lean_addMacroScope(v___y_1101_, v___x_1123_, v___y_1102_);
v___x_1125_ = lean_box(0);
v___x_1126_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1126_, 0, v___y_1095_);
lean_ctor_set(v___x_1126_, 1, v___x_1122_);
lean_ctor_set(v___x_1126_, 2, v___x_1124_);
lean_ctor_set(v___x_1126_, 3, v___x_1125_);
v___x_1127_ = l_Lean_mkIdent(v_k_504_);
v___x_1128_ = l_Lean_Syntax_node2(v___y_1095_, v___y_1099_, v___x_1126_, v___x_1127_);
v___x_1129_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___y_1095_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__55, &l_Lean_Elab_Command_elabElabRulesAux___closed__55_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__55);
v___x_1132_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__56));
lean_inc_ref(v___y_1103_);
lean_inc_ref_n(v___y_1094_, 2);
v___x_1133_ = l_Lean_Name_mkStr4(v___y_1097_, v___y_1094_, v___y_1103_, v___x_1132_);
lean_inc(v___x_1133_);
v___x_1134_ = l_Lean_addMacroScope(v___y_1101_, v___x_1133_, v___y_1102_);
v___x_1135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1125_);
v___x_1136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v___x_1125_);
v___x_1137_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1137_, 0, v___y_1095_);
lean_ctor_set(v___x_1137_, 1, v___x_1131_);
lean_ctor_set(v___x_1137_, 2, v___x_1134_);
lean_ctor_set(v___x_1137_, 3, v___x_1136_);
v___x_1138_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1139_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___y_1095_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1141_ = l_Lean_Name_mkStr4(v___y_1097_, v___x_1107_, v___x_1108_, v___x_1140_);
v___x_1142_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___y_1095_);
lean_ctor_set(v___x_1142_, 1, v___x_1140_);
v___x_1143_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1144_ = l_Lean_Name_mkStr4(v___y_1097_, v___x_1107_, v___x_1108_, v___x_1143_);
v___x_1145_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1146_ = l_Lean_Name_mkStr4(v___y_1097_, v___x_1107_, v___x_1108_, v___x_1145_);
v___x_1147_ = l_Array_append___redArg(v___y_1092_, v_a_514_);
lean_dec(v_a_514_);
v___x_1148_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___y_1095_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1151_ = l_Lean_Name_mkStr4(v___y_1097_, v___x_1107_, v___x_1108_, v___x_1150_);
v___x_1152_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1153_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___y_1095_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l_Lean_Syntax_node1(v___y_1095_, v___x_1151_, v___x_1153_);
v___x_1155_ = l_Lean_Syntax_node1(v___y_1095_, v___y_1099_, v___x_1154_);
v___x_1156_ = l_Lean_Syntax_node1(v___y_1095_, v___y_1099_, v___x_1155_);
v___x_1157_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1158_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___y_1095_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1160_ = l_Lean_Name_mkStr4(v___y_1097_, v___x_1107_, v___x_1108_, v___x_1159_);
v___x_1161_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1162_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___y_1095_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1164_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__30, &l_Lean_Elab_Command_elabElabRulesAux___closed__30_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30);
v___x_1165_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1166_ = l_Lean_addMacroScope(v___y_1101_, v___x_1165_, v___y_1102_);
v___x_1167_ = l_Lean_Name_mkStr3(v___y_1097_, v___y_1094_, v___x_1163_);
v___x_1168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
lean_ctor_set(v___x_1168_, 1, v___x_1125_);
v___x_1169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
lean_ctor_set(v___x_1169_, 1, v___x_1125_);
v___x_1170_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1170_, 0, v___y_1095_);
lean_ctor_set(v___x_1170_, 1, v___x_1164_);
lean_ctor_set(v___x_1170_, 2, v___x_1166_);
lean_ctor_set(v___x_1170_, 3, v___x_1169_);
v___x_1171_ = l_Lean_Syntax_node2(v___y_1095_, v___x_1160_, v___x_1162_, v___x_1170_);
v___x_1172_ = l_Lean_Syntax_node4(v___y_1095_, v___x_1146_, v___x_1149_, v___x_1156_, v___x_1158_, v___x_1171_);
v___x_1173_ = lean_array_push(v___x_1147_, v___x_1172_);
v___x_1174_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1174_, 0, v___y_1095_);
lean_ctor_set(v___x_1174_, 1, v___y_1099_);
lean_ctor_set(v___x_1174_, 2, v___x_1173_);
v___x_1175_ = l_Lean_Syntax_node1(v___y_1095_, v___x_1144_, v___x_1174_);
v___x_1176_ = l_Lean_Syntax_node2(v___y_1095_, v___x_1141_, v___x_1142_, v___x_1175_);
v___x_1177_ = lean_unsigned_to_nat(9u);
v___x_1178_ = lean_mk_empty_array_with_capacity(v___x_1177_);
v___x_1179_ = lean_array_push(v___x_1178_, v___x_1106_);
v___x_1180_ = lean_array_push(v___x_1179_, v___x_1120_);
v___x_1181_ = lean_array_push(v___x_1180_, v___y_1100_);
v___x_1182_ = lean_array_push(v___x_1181_, v___x_1121_);
v___x_1183_ = lean_array_push(v___x_1182_, v___x_1128_);
v___x_1184_ = lean_array_push(v___x_1183_, v___x_1130_);
v___x_1185_ = lean_array_push(v___x_1184_, v___x_1137_);
v___x_1186_ = lean_array_push(v___x_1185_, v___x_1139_);
v___x_1187_ = lean_array_push(v___x_1186_, v___x_1176_);
lean_inc(v___y_1098_);
v___x_1188_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1188_, 0, v___y_1095_);
lean_ctor_set(v___x_1188_, 1, v___y_1098_);
lean_ctor_set(v___x_1188_, 2, v___x_1187_);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
v___jp_1190_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1196_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1197_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1198_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___x_1199_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_1200_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
v___x_1201_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1202_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_501_) == 1)
{
lean_object* v_val_1203_; lean_object* v___x_1204_; 
v_val_1203_ = lean_ctor_get(v_doc_x3f_501_, 0);
lean_inc(v_val_1203_);
lean_dec_ref_known(v_doc_x3f_501_, 1);
v___x_1204_ = l_Array_mkArray1___redArg(v_val_1203_);
v___y_1092_ = v___x_1202_;
v___y_1093_ = v___x_1199_;
v___y_1094_ = v___x_1197_;
v___y_1095_ = v___y_1194_;
v___y_1096_ = v___y_1193_;
v___y_1097_ = v___x_1196_;
v___y_1098_ = v___x_1200_;
v___y_1099_ = v___x_1201_;
v___y_1100_ = v___y_1191_;
v___y_1101_ = v_a_1195_;
v___y_1102_ = v___y_1192_;
v___y_1103_ = v___x_1198_;
v___y_1104_ = v___x_1204_;
goto v___jp_1091_;
}
else
{
lean_object* v___x_1205_; 
lean_dec(v_doc_x3f_501_);
v___x_1205_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_1092_ = v___x_1202_;
v___y_1093_ = v___x_1199_;
v___y_1094_ = v___x_1197_;
v___y_1095_ = v___y_1194_;
v___y_1096_ = v___y_1193_;
v___y_1097_ = v___x_1196_;
v___y_1098_ = v___x_1200_;
v___y_1099_ = v___x_1201_;
v___y_1100_ = v___y_1191_;
v___y_1101_ = v_a_1195_;
v___y_1102_ = v___y_1192_;
v___y_1103_ = v___x_1198_;
v___y_1104_ = v___x_1205_;
goto v___jp_1091_;
}
}
v___jp_1206_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_inc_ref_n(v___y_1214_, 4);
v___x_1219_ = l_Array_append___redArg(v___y_1214_, v___y_1218_);
lean_dec_ref(v___y_1218_);
lean_inc_n(v___y_1210_, 10);
lean_inc_n(v___y_1217_, 35);
v___x_1220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1220_, 0, v___y_1217_);
lean_ctor_set(v___x_1220_, 1, v___y_1210_);
lean_ctor_set(v___x_1220_, 2, v___x_1219_);
v___x_1221_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1222_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1223_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1212_, 11);
v___x_1224_ = l_Lean_Name_mkStr4(v___y_1212_, v___x_1221_, v___x_1222_, v___x_1223_);
v___x_1225_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1226_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___y_1217_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1228_ = l_Lean_Syntax_SepArray_ofElems(v___x_1227_, v___y_1216_);
lean_dec_ref(v___y_1216_);
v___x_1229_ = l_Array_append___redArg(v___y_1214_, v___x_1228_);
lean_dec_ref(v___x_1228_);
v___x_1230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1230_, 0, v___y_1217_);
lean_ctor_set(v___x_1230_, 1, v___y_1210_);
lean_ctor_set(v___x_1230_, 2, v___x_1229_);
v___x_1231_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___y_1217_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = l_Lean_Syntax_node3(v___y_1217_, v___x_1224_, v___x_1226_, v___x_1230_, v___x_1232_);
v___x_1234_ = l_Lean_Syntax_node1(v___y_1217_, v___y_1210_, v___x_1233_);
lean_inc_ref(v___y_1208_);
v___x_1235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___y_1217_);
lean_ctor_set(v___x_1235_, 1, v___y_1208_);
v___x_1236_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1237_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1207_, 3);
lean_inc_n(v___y_1209_, 3);
v___x_1238_ = l_Lean_addMacroScope(v___y_1209_, v___x_1237_, v___y_1207_);
v___x_1239_ = lean_box(0);
v___x_1240_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1240_, 0, v___y_1217_);
lean_ctor_set(v___x_1240_, 1, v___x_1236_);
lean_ctor_set(v___x_1240_, 2, v___x_1238_);
lean_ctor_set(v___x_1240_, 3, v___x_1239_);
v___x_1241_ = l_Lean_mkIdent(v_k_504_);
v___x_1242_ = l_Lean_Syntax_node2(v___y_1217_, v___y_1210_, v___x_1240_, v___x_1241_);
v___x_1243_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___y_1217_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__39, &l_Lean_Elab_Command_elabElabRulesAux___closed__39_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__39);
v___x_1246_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__40));
lean_inc_ref_n(v___y_1213_, 2);
v___x_1247_ = l_Lean_Name_mkStr4(v___y_1212_, v___y_1213_, v___x_1222_, v___x_1246_);
lean_inc(v___x_1247_);
v___x_1248_ = l_Lean_addMacroScope(v___y_1209_, v___x_1247_, v___y_1207_);
v___x_1249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1239_);
v___x_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v___x_1239_);
v___x_1251_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1251_, 0, v___y_1217_);
lean_ctor_set(v___x_1251_, 1, v___x_1245_);
lean_ctor_set(v___x_1251_, 2, v___x_1248_);
lean_ctor_set(v___x_1251_, 3, v___x_1250_);
v___x_1252_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___y_1217_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
v___x_1254_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1255_ = l_Lean_Name_mkStr4(v___y_1212_, v___x_1221_, v___x_1222_, v___x_1254_);
v___x_1256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___y_1217_);
lean_ctor_set(v___x_1256_, 1, v___x_1254_);
v___x_1257_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_1258_ = l_Lean_Name_mkStr4(v___y_1212_, v___x_1221_, v___x_1222_, v___x_1257_);
v___x_1259_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_1260_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1261_ = l_Lean_addMacroScope(v___y_1209_, v___x_1260_, v___y_1207_);
v___x_1262_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1262_, 0, v___y_1217_);
lean_ctor_set(v___x_1262_, 1, v___x_1259_);
lean_ctor_set(v___x_1262_, 2, v___x_1261_);
lean_ctor_set(v___x_1262_, 3, v___x_1239_);
v___x_1263_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1264_ = l_Lean_Name_mkStr4(v___y_1212_, v___x_1221_, v___x_1222_, v___x_1263_);
v___x_1265_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___y_1217_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = l_Lean_Syntax_node1(v___y_1217_, v___x_1264_, v___x_1266_);
lean_inc(v___x_1267_);
lean_inc_ref(v___x_1262_);
v___x_1268_ = l_Lean_Syntax_node2(v___y_1217_, v___y_1210_, v___x_1262_, v___x_1267_);
v___x_1269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1269_, 0, v___y_1217_);
lean_ctor_set(v___x_1269_, 1, v___y_1210_);
lean_ctor_set(v___x_1269_, 2, v___y_1214_);
v___x_1270_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1271_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___y_1217_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_1273_ = l_Lean_Name_mkStr4(v___y_1212_, v___x_1221_, v___x_1222_, v___x_1272_);
v___x_1274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___y_1217_);
lean_ctor_set(v___x_1274_, 1, v___x_1272_);
v___x_1275_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_1276_ = l_Lean_Name_mkStr4(v___y_1212_, v___x_1221_, v___x_1222_, v___x_1275_);
lean_inc_ref_n(v___x_1269_, 3);
v___x_1277_ = l_Lean_Syntax_node2(v___y_1217_, v___x_1276_, v___x_1269_, v___x_1262_);
v___x_1278_ = l_Lean_Syntax_node1(v___y_1217_, v___y_1210_, v___x_1277_);
v___x_1279_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___y_1217_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1282_ = l_Lean_Name_mkStr4(v___y_1212_, v___x_1221_, v___x_1222_, v___x_1281_);
v___x_1283_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1284_ = l_Lean_Name_mkStr4(v___y_1212_, v___x_1221_, v___x_1222_, v___x_1283_);
v___x_1285_ = l_Array_append___redArg(v___y_1214_, v_a_514_);
lean_dec(v_a_514_);
v___x_1286_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___y_1217_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = l_Lean_Syntax_node1(v___y_1217_, v___y_1210_, v___x_1267_);
v___x_1289_ = l_Lean_Syntax_node1(v___y_1217_, v___y_1210_, v___x_1288_);
v___x_1290_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1291_ = l_Lean_Name_mkStr4(v___y_1212_, v___x_1221_, v___x_1222_, v___x_1290_);
v___x_1292_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___y_1217_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
v___x_1294_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1295_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__30, &l_Lean_Elab_Command_elabElabRulesAux___closed__30_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__30);
v___x_1296_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1297_ = l_Lean_addMacroScope(v___y_1209_, v___x_1296_, v___y_1207_);
v___x_1298_ = l_Lean_Name_mkStr3(v___y_1212_, v___y_1213_, v___x_1294_);
v___x_1299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v___x_1239_);
v___x_1300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___x_1239_);
v___x_1301_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1301_, 0, v___y_1217_);
lean_ctor_set(v___x_1301_, 1, v___x_1295_);
lean_ctor_set(v___x_1301_, 2, v___x_1297_);
lean_ctor_set(v___x_1301_, 3, v___x_1300_);
v___x_1302_ = l_Lean_Syntax_node2(v___y_1217_, v___x_1291_, v___x_1293_, v___x_1301_);
lean_inc_ref(v___x_1271_);
v___x_1303_ = l_Lean_Syntax_node4(v___y_1217_, v___x_1284_, v___x_1287_, v___x_1289_, v___x_1271_, v___x_1302_);
v___x_1304_ = lean_array_push(v___x_1285_, v___x_1303_);
v___x_1305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1305_, 0, v___y_1217_);
lean_ctor_set(v___x_1305_, 1, v___y_1210_);
lean_ctor_set(v___x_1305_, 2, v___x_1304_);
v___x_1306_ = l_Lean_Syntax_node1(v___y_1217_, v___x_1282_, v___x_1305_);
v___x_1307_ = l_Lean_Syntax_node6(v___y_1217_, v___x_1273_, v___x_1274_, v___x_1269_, v___x_1269_, v___x_1278_, v___x_1280_, v___x_1306_);
v___x_1308_ = l_Lean_Syntax_node4(v___y_1217_, v___x_1258_, v___x_1268_, v___x_1269_, v___x_1271_, v___x_1307_);
v___x_1309_ = l_Lean_Syntax_node2(v___y_1217_, v___x_1255_, v___x_1256_, v___x_1308_);
v___x_1310_ = lean_unsigned_to_nat(9u);
v___x_1311_ = lean_mk_empty_array_with_capacity(v___x_1310_);
v___x_1312_ = lean_array_push(v___x_1311_, v___x_1220_);
v___x_1313_ = lean_array_push(v___x_1312_, v___x_1234_);
v___x_1314_ = lean_array_push(v___x_1313_, v___y_1215_);
v___x_1315_ = lean_array_push(v___x_1314_, v___x_1235_);
v___x_1316_ = lean_array_push(v___x_1315_, v___x_1242_);
v___x_1317_ = lean_array_push(v___x_1316_, v___x_1244_);
v___x_1318_ = lean_array_push(v___x_1317_, v___x_1251_);
v___x_1319_ = lean_array_push(v___x_1318_, v___x_1253_);
v___x_1320_ = lean_array_push(v___x_1319_, v___x_1309_);
lean_inc(v___y_1211_);
v___x_1321_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1321_, 0, v___y_1217_);
lean_ctor_set(v___x_1321_, 1, v___y_1211_);
lean_ctor_set(v___x_1321_, 2, v___x_1320_);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
return v___x_1322_;
}
v___jp_1323_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1329_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1330_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1331_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_1332_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
v___x_1333_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1334_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_501_) == 1)
{
lean_object* v_val_1335_; lean_object* v___x_1336_; 
v_val_1335_ = lean_ctor_get(v_doc_x3f_501_, 0);
lean_inc(v_val_1335_);
lean_dec_ref_known(v_doc_x3f_501_, 1);
v___x_1336_ = l_Array_mkArray1___redArg(v_val_1335_);
v___y_1207_ = v___y_1324_;
v___y_1208_ = v___x_1331_;
v___y_1209_ = v_a_1328_;
v___y_1210_ = v___x_1333_;
v___y_1211_ = v___x_1332_;
v___y_1212_ = v___x_1329_;
v___y_1213_ = v___x_1330_;
v___y_1214_ = v___x_1334_;
v___y_1215_ = v___y_1325_;
v___y_1216_ = v___y_1326_;
v___y_1217_ = v___y_1327_;
v___y_1218_ = v___x_1336_;
goto v___jp_1206_;
}
else
{
lean_object* v___x_1337_; 
lean_dec(v_doc_x3f_501_);
v___x_1337_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_1207_ = v___y_1324_;
v___y_1208_ = v___x_1331_;
v___y_1209_ = v_a_1328_;
v___y_1210_ = v___x_1333_;
v___y_1211_ = v___x_1332_;
v___y_1212_ = v___x_1329_;
v___y_1213_ = v___x_1330_;
v___y_1214_ = v___x_1334_;
v___y_1215_ = v___y_1325_;
v___y_1216_ = v___y_1326_;
v___y_1217_ = v___y_1327_;
v___y_1218_ = v___x_1337_;
goto v___jp_1206_;
}
}
v___jp_1338_:
{
lean_object* v___x_1342_; 
lean_inc(v_attrKind_503_);
v___x_1342_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_503_);
if (lean_obj_tag(v_expty_x3f_506_) == 1)
{
lean_object* v_val_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v_val_1343_ = lean_ctor_get(v_expty_x3f_506_, 0);
lean_inc(v_val_1343_);
lean_dec_ref_known(v_expty_x3f_506_, 1);
v___x_1344_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__58));
v___x_1345_ = lean_name_eq(v_catName_1339_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1346_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__60));
v___x_1347_ = lean_name_eq(v_catName_1339_, v___x_1346_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_dec(v___x_1342_);
lean_del_object(v___x_516_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_attrKind_503_);
lean_dec(v_doc_x3f_501_);
v___x_1348_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__62, &l_Lean_Elab_Command_elabElabRulesAux___closed__62_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__62);
v___x_1349_ = l_Lean_MessageData_ofName(v_catName_1339_);
v___x_1350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1348_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
v___x_1351_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__64, &l_Lean_Elab_Command_elabElabRulesAux___closed__64_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__64);
v___x_1352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1350_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_val_1343_, v___x_1352_, v___y_1340_, v___y_1341_);
lean_dec(v_val_1343_);
return v___x_1353_;
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_dec(v_catName_1339_);
v___x_1354_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__66));
lean_inc(v_k_504_);
v___x_1355_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_504_, v_attrKind_503_, v_attrs_x3f_502_, v___x_1354_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1357_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v___x_1357_ = l_Lean_Elab_Command_getRef___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v___x_1359_ = l_Lean_SourceInfo_fromRef(v_a_1358_, v___x_1345_);
lean_dec(v_a_1358_);
v___x_1360_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_quotContext_x3f_1361_; 
v_quotContext_x3f_1361_ = lean_ctor_get(v___y_1340_, 5);
if (lean_obj_tag(v_quotContext_x3f_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1363_; lean_object* v_a_1364_; 
v_a_1362_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v___x_1360_, 1);
v___x_1363_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1341_);
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref(v___x_1363_);
v___y_640_ = v___x_1359_;
v___y_641_ = v_val_1343_;
v___y_642_ = v___x_1342_;
v___y_643_ = v_a_1356_;
v___y_644_ = v_a_1362_;
v_a_645_ = v_a_1364_;
goto v___jp_639_;
}
else
{
lean_object* v_a_1365_; lean_object* v_val_1366_; 
v_a_1365_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1360_, 1);
v_val_1366_ = lean_ctor_get(v_quotContext_x3f_1361_, 0);
lean_inc(v_val_1366_);
v___y_640_ = v___x_1359_;
v___y_641_ = v_val_1343_;
v___y_642_ = v___x_1342_;
v___y_643_ = v_a_1356_;
v___y_644_ = v_a_1365_;
v_a_645_ = v_val_1366_;
goto v___jp_639_;
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec(v___x_1359_);
lean_dec(v_a_1356_);
lean_dec(v_val_1343_);
lean_dec(v___x_1342_);
lean_del_object(v___x_516_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1367_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1360_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1360_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
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
lean_dec(v_a_1356_);
lean_dec(v_val_1343_);
lean_dec(v___x_1342_);
lean_del_object(v___x_516_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
return v___x_1357_;
}
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_dec(v_val_1343_);
lean_dec(v___x_1342_);
lean_del_object(v___x_516_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1375_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1355_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1355_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
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
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_dec(v_catName_1339_);
lean_del_object(v___x_516_);
v___x_1383_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__68));
lean_inc(v_k_504_);
v___x_1384_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_504_, v_attrKind_503_, v_attrs_x3f_502_, v___x_1383_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = l_Lean_Elab_Command_getRef___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1386_, 1);
v___x_1388_ = 0;
v___x_1389_ = l_Lean_SourceInfo_fromRef(v_a_1387_, v___x_1388_);
lean_dec(v_a_1387_);
v___x_1390_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_quotContext_x3f_1391_; 
v_quotContext_x3f_1391_ = lean_ctor_get(v___y_1340_, 5);
if (lean_obj_tag(v_quotContext_x3f_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1393_; lean_object* v_a_1394_; 
v_a_1392_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1390_, 1);
v___x_1393_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1341_);
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref(v___x_1393_);
v___y_792_ = v___x_1389_;
v___y_793_ = v_val_1343_;
v___y_794_ = v_a_1392_;
v___y_795_ = v___x_1342_;
v___y_796_ = v_a_1385_;
v_a_797_ = v_a_1394_;
goto v___jp_791_;
}
else
{
lean_object* v_a_1395_; lean_object* v_val_1396_; 
v_a_1395_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1390_, 1);
v_val_1396_ = lean_ctor_get(v_quotContext_x3f_1391_, 0);
lean_inc(v_val_1396_);
v___y_792_ = v___x_1389_;
v___y_793_ = v_val_1343_;
v___y_794_ = v_a_1395_;
v___y_795_ = v___x_1342_;
v___y_796_ = v_a_1385_;
v_a_797_ = v_val_1396_;
goto v___jp_791_;
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec(v___x_1389_);
lean_dec(v_a_1385_);
lean_dec(v_val_1343_);
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1397_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1390_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1390_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
else
{
lean_dec(v_a_1385_);
lean_dec(v_val_1343_);
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
return v___x_1386_;
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec(v_val_1343_);
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1405_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1384_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1384_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
else
{
lean_object* v___x_1413_; uint8_t v___x_1414_; 
lean_del_object(v___x_516_);
lean_dec(v_expty_x3f_506_);
v___x_1413_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__58));
v___x_1414_ = lean_name_eq(v_catName_1339_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1415_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__70));
v___x_1416_ = lean_name_eq(v_catName_1339_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1417_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__72));
v___x_1418_ = lean_name_eq(v_catName_1339_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1419_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__74));
v___x_1420_ = lean_name_eq(v_catName_1339_, v___x_1419_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1421_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__60));
v___x_1422_ = lean_name_eq(v_catName_1339_, v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_attrKind_503_);
lean_dec(v_doc_x3f_501_);
v___x_1423_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__76, &l_Lean_Elab_Command_elabElabRulesAux___closed__76_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76);
v___x_1424_ = l_Lean_MessageData_ofName(v_catName_1339_);
v___x_1425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1423_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
v___x_1426_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__78, &l_Lean_Elab_Command_elabElabRulesAux___closed__78_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__78);
v___x_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1425_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(v___x_1427_, v___y_1340_, v___y_1341_);
return v___x_1428_;
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec(v_catName_1339_);
v___x_1429_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__66));
lean_inc(v_k_504_);
v___x_1430_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_504_, v_attrKind_503_, v_attrs_x3f_502_, v___x_1429_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1432_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1432_ = l_Lean_Elab_Command_getRef___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___x_1432_, 1);
v___x_1434_ = l_Lean_SourceInfo_fromRef(v_a_1433_, v___x_1420_);
lean_dec(v_a_1433_);
v___x_1435_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_quotContext_x3f_1436_; 
v_quotContext_x3f_1436_ = lean_ctor_get(v___y_1340_, 5);
if (lean_obj_tag(v_quotContext_x3f_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1438_; lean_object* v_a_1439_; 
v_a_1437_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1437_);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1438_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1341_);
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
lean_dec_ref(v___x_1438_);
v___y_1077_ = v_a_1431_;
v___y_1078_ = v___x_1434_;
v___y_1079_ = v_a_1437_;
v___y_1080_ = v___x_1342_;
v_a_1081_ = v_a_1439_;
goto v___jp_1076_;
}
else
{
lean_object* v_a_1440_; lean_object* v_val_1441_; 
v_a_1440_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1435_, 1);
v_val_1441_ = lean_ctor_get(v_quotContext_x3f_1436_, 0);
lean_inc(v_val_1441_);
v___y_1077_ = v_a_1431_;
v___y_1078_ = v___x_1434_;
v___y_1079_ = v_a_1440_;
v___y_1080_ = v___x_1342_;
v_a_1081_ = v_val_1441_;
goto v___jp_1076_;
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v___x_1434_);
lean_dec(v_a_1431_);
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1442_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1435_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1435_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
else
{
lean_dec(v_a_1431_);
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
return v___x_1432_;
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1450_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1430_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1430_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
else
{
lean_dec(v_catName_1339_);
v___y_921_ = v___y_1340_;
v___y_922_ = v___x_1342_;
v___y_923_ = v___x_1417_;
v___y_924_ = v___x_1416_;
v___y_925_ = v___y_1341_;
goto v___jp_920_;
}
}
else
{
lean_dec(v_catName_1339_);
v___y_921_ = v___y_1340_;
v___y_922_ = v___x_1342_;
v___y_923_ = v___x_1417_;
v___y_924_ = v___x_1416_;
v___y_925_ = v___y_1341_;
goto v___jp_920_;
}
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_dec(v_catName_1339_);
v___x_1458_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__80));
lean_inc(v_k_504_);
v___x_1459_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_504_, v_attrKind_503_, v_attrs_x3f_502_, v___x_1458_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1461_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1459_, 1);
v___x_1461_ = l_Lean_Elab_Command_getRef___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1461_, 1);
v___x_1463_ = l_Lean_SourceInfo_fromRef(v_a_1462_, v___x_1414_);
lean_dec(v_a_1462_);
v___x_1464_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_quotContext_x3f_1465_; 
v_quotContext_x3f_1465_ = lean_ctor_get(v___y_1340_, 5);
if (lean_obj_tag(v_quotContext_x3f_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1467_; lean_object* v_a_1468_; 
v_a_1466_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1464_, 1);
v___x_1467_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1341_);
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1468_);
lean_dec_ref(v___x_1467_);
v___y_1191_ = v___x_1342_;
v___y_1192_ = v_a_1466_;
v___y_1193_ = v_a_1460_;
v___y_1194_ = v___x_1463_;
v_a_1195_ = v_a_1468_;
goto v___jp_1190_;
}
else
{
lean_object* v_a_1469_; lean_object* v_val_1470_; 
v_a_1469_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1469_);
lean_dec_ref_known(v___x_1464_, 1);
v_val_1470_ = lean_ctor_get(v_quotContext_x3f_1465_, 0);
lean_inc(v_val_1470_);
v___y_1191_ = v___x_1342_;
v___y_1192_ = v_a_1469_;
v___y_1193_ = v_a_1460_;
v___y_1194_ = v___x_1463_;
v_a_1195_ = v_val_1470_;
goto v___jp_1190_;
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v___x_1463_);
lean_dec(v_a_1460_);
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1471_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1464_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1464_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_dec(v_a_1460_);
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
return v___x_1461_;
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1479_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1459_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1459_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_dec(v_catName_1339_);
v___x_1487_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__68));
lean_inc(v_k_504_);
v___x_1488_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_504_, v_attrKind_503_, v_attrs_x3f_502_, v___x_1487_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v___x_1490_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1488_, 1);
v___x_1490_ = l_Lean_Elab_Command_getRef___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref_known(v___x_1490_, 1);
v___x_1492_ = 0;
v___x_1493_ = l_Lean_SourceInfo_fromRef(v_a_1491_, v___x_1492_);
lean_dec(v_a_1491_);
v___x_1494_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1340_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_quotContext_x3f_1495_; 
v_quotContext_x3f_1495_ = lean_ctor_get(v___y_1340_, 5);
if (lean_obj_tag(v_quotContext_x3f_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1497_; lean_object* v_a_1498_; 
v_a_1496_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1496_);
lean_dec_ref_known(v___x_1494_, 1);
v___x_1497_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1341_);
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref(v___x_1497_);
v___y_1324_ = v_a_1496_;
v___y_1325_ = v___x_1342_;
v___y_1326_ = v_a_1489_;
v___y_1327_ = v___x_1493_;
v_a_1328_ = v_a_1498_;
goto v___jp_1323_;
}
else
{
lean_object* v_a_1499_; lean_object* v_val_1500_; 
v_a_1499_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v___x_1494_, 1);
v_val_1500_ = lean_ctor_get(v_quotContext_x3f_1495_, 0);
lean_inc(v_val_1500_);
v___y_1324_ = v_a_1499_;
v___y_1325_ = v___x_1342_;
v___y_1326_ = v_a_1489_;
v___y_1327_ = v___x_1493_;
v_a_1328_ = v_val_1500_;
goto v___jp_1323_;
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec(v___x_1493_);
lean_dec(v_a_1489_);
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1501_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1494_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1494_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
lean_dec(v_a_1489_);
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
return v___x_1490_;
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec(v___x_1342_);
lean_dec(v_a_514_);
lean_dec(v_k_504_);
lean_dec(v_doc_x3f_501_);
v_a_1509_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1488_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1488_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
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
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v_expty_x3f_506_);
lean_dec(v_k_504_);
lean_dec(v_attrKind_503_);
lean_dec(v_doc_x3f_501_);
v_a_1531_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_513_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_513_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object* v_doc_x3f_1539_, lean_object* v_attrs_x3f_1540_, lean_object* v_attrKind_1541_, lean_object* v_k_1542_, lean_object* v_cat_x3f_1543_, lean_object* v_expty_x3f_1544_, lean_object* v_alts_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_Elab_Command_elabElabRulesAux(v_doc_x3f_1539_, v_attrs_x3f_1540_, v_attrKind_1541_, v_k_1542_, v_cat_x3f_1543_, v_expty_x3f_1544_, v_alts_1545_, v_a_1546_, v_a_1547_);
lean_dec(v_a_1547_);
lean_dec_ref(v_a_1546_);
lean_dec(v_cat_x3f_1543_);
lean_dec(v_attrs_x3f_1540_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(lean_object* v_00_u03b1_1550_, lean_object* v_ref_1551_, lean_object* v_msg_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_1551_, v_msg_1552_, v___y_1553_, v___y_1554_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___boxed(lean_object* v_00_u03b1_1557_, lean_object* v_ref_1558_, lean_object* v_msg_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(v_00_u03b1_1557_, v_ref_1558_, v_msg_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v_ref_1558_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4(lean_object* v_msgData_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg(v_msgData_1564_, v___y_1566_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___boxed(lean_object* v_msgData_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4(v_msgData_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(lean_object* v_00_u03b1_1574_, lean_object* v_msg_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___redArg(v_msg_1575_, v___y_1576_, v___y_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(lean_object* v_00_u03b1_1580_, lean_object* v_msg_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_00_u03b1_1580_, v_msg_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5(lean_object* v_msgData_1586_, lean_object* v_macroStack_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___redArg(v_msgData_1586_, v_macroStack_1587_, v___y_1589_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5___boxed(lean_object* v_msgData_1592_, lean_object* v_macroStack_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__5(v_msgData_1592_, v_macroStack_1593_, v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
return v_res_1597_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1598_ = lean_box(0);
v___x_1599_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
lean_ctor_set(v___x_1600_, 1, v___x_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg(){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___closed__0);
v___x_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg___boxed(lean_object* v___y_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0(lean_object* v_00_u03b1_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___boxed(lean_object* v_00_u03b1_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0(v_00_u03b1_1611_, v___y_1612_, v___y_1613_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0(lean_object* v_x_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0___boxed(lean_object* v_x_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_Elab_Command_elabElabRules___lam__0(v_x_1618_);
lean_dec(v_x_1618_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1(lean_object* v___x_1624_, lean_object* v___x_1625_, lean_object* v_attrKind_1626_, lean_object* v_expty_x3f_1627_, lean_object* v___f_1628_, lean_object* v_cat_x3f_1629_, lean_object* v___x_1630_, lean_object* v___x_1631_, lean_object* v_attrs_x3f_1632_, lean_object* v___x_1633_, lean_object* v___x_1634_, lean_object* v___x_1635_, lean_object* v_doc_x3f_1636_, lean_object* v_kind_x3f_1637_, lean_object* v_alts_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Elab_Command_getRef___redArg(v___y_1639_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1751_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1751_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1751_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
uint8_t v___x_1647_; lean_object* v___x_1648_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___x_1740_; 
v___x_1647_ = 0;
v___x_1648_ = l_Lean_SourceInfo_fromRef(v_a_1643_, v___x_1647_);
lean_dec(v_a_1643_);
v___x_1740_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1639_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_quotContext_x3f_1741_; 
lean_dec_ref_known(v___x_1740_, 1);
v_quotContext_x3f_1741_ = lean_ctor_get(v___y_1639_, 5);
if (lean_obj_tag(v_quotContext_x3f_1741_) == 0)
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1640_);
lean_dec_ref(v___x_1742_);
goto v___jp_1734_;
}
else
{
goto v___jp_1734_;
}
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_dec(v___x_1648_);
lean_del_object(v___x_1645_);
lean_dec(v_kind_x3f_1637_);
lean_dec(v_doc_x3f_1636_);
lean_dec_ref(v___x_1635_);
lean_dec_ref(v___x_1634_);
lean_dec_ref(v___x_1633_);
lean_dec_ref(v___x_1630_);
lean_dec(v_cat_x3f_1629_);
lean_dec_ref(v___f_1628_);
lean_dec(v_expty_x3f_1627_);
lean_dec(v_attrKind_1626_);
lean_dec(v___x_1625_);
lean_dec(v___x_1624_);
v_a_1743_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1740_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1740_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
v___jp_1649_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1665_; 
lean_inc_ref_n(v___y_1650_, 2);
v___x_1658_ = l_Array_append___redArg(v___y_1650_, v___y_1657_);
lean_dec_ref(v___y_1657_);
lean_inc_n(v___y_1653_, 2);
lean_inc_n(v___x_1648_, 3);
v___x_1659_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1648_);
lean_ctor_set(v___x_1659_, 1, v___y_1653_);
lean_ctor_set(v___x_1659_, 2, v___x_1658_);
v___x_1660_ = l_Array_append___redArg(v___y_1650_, v_alts_1638_);
v___x_1661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1648_);
lean_ctor_set(v___x_1661_, 1, v___y_1653_);
lean_ctor_set(v___x_1661_, 2, v___x_1660_);
v___x_1662_ = l_Lean_Syntax_node1(v___x_1648_, v___x_1624_, v___x_1661_);
v___x_1663_ = l_Lean_Syntax_node8(v___x_1648_, v___x_1625_, v___y_1651_, v___y_1656_, v_attrKind_1626_, v___y_1652_, v___y_1654_, v___y_1655_, v___x_1659_, v___x_1662_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1663_);
v___x_1665_ = v___x_1645_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
v___jp_1667_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
lean_inc_ref(v___y_1668_);
v___x_1675_ = l_Array_append___redArg(v___y_1668_, v___y_1674_);
lean_dec_ref(v___y_1674_);
lean_inc(v___y_1671_);
lean_inc(v___x_1648_);
v___x_1676_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1648_);
lean_ctor_set(v___x_1676_, 1, v___y_1671_);
lean_ctor_set(v___x_1676_, 2, v___x_1675_);
if (lean_obj_tag(v_expty_x3f_1627_) == 1)
{
lean_object* v_val_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec_ref(v___f_1628_);
v_val_1677_ = lean_ctor_get(v_expty_x3f_1627_, 0);
lean_inc(v_val_1677_);
lean_dec_ref_known(v_expty_x3f_1627_, 1);
v___x_1678_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___x_1648_);
v___x_1679_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1648_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = l_Array_mkArray2___redArg(v___x_1679_, v_val_1677_);
v___y_1650_ = v___y_1668_;
v___y_1651_ = v___y_1669_;
v___y_1652_ = v___y_1670_;
v___y_1653_ = v___y_1671_;
v___y_1654_ = v___y_1672_;
v___y_1655_ = v___x_1676_;
v___y_1656_ = v___y_1673_;
v___y_1657_ = v___x_1680_;
goto v___jp_1649_;
}
else
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_apply_1(v___f_1628_, v_expty_x3f_1627_);
v___y_1650_ = v___y_1668_;
v___y_1651_ = v___y_1669_;
v___y_1652_ = v___y_1670_;
v___y_1653_ = v___y_1671_;
v___y_1654_ = v___y_1672_;
v___y_1655_ = v___x_1676_;
v___y_1656_ = v___y_1673_;
v___y_1657_ = v___x_1681_;
goto v___jp_1649_;
}
}
v___jp_1682_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_inc_ref(v___y_1683_);
v___x_1689_ = l_Array_append___redArg(v___y_1683_, v___y_1688_);
lean_dec_ref(v___y_1688_);
lean_inc(v___y_1686_);
lean_inc(v___x_1648_);
v___x_1690_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1648_);
lean_ctor_set(v___x_1690_, 1, v___y_1686_);
lean_ctor_set(v___x_1690_, 2, v___x_1689_);
if (lean_obj_tag(v_cat_x3f_1629_) == 1)
{
lean_object* v_val_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v_val_1691_ = lean_ctor_get(v_cat_x3f_1629_, 0);
lean_inc(v_val_1691_);
lean_dec_ref_known(v_cat_x3f_1629_, 1);
v___x_1692_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(v___x_1648_);
v___x_1693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1648_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = l_Array_mkArray2___redArg(v___x_1693_, v_val_1691_);
v___y_1668_ = v___y_1683_;
v___y_1669_ = v___y_1684_;
v___y_1670_ = v___y_1685_;
v___y_1671_ = v___y_1686_;
v___y_1672_ = v___x_1690_;
v___y_1673_ = v___y_1687_;
v___y_1674_ = v___x_1694_;
goto v___jp_1667_;
}
else
{
lean_object* v___x_1695_; 
lean_inc_ref(v___f_1628_);
v___x_1695_ = lean_apply_1(v___f_1628_, v_cat_x3f_1629_);
v___y_1668_ = v___y_1683_;
v___y_1669_ = v___y_1684_;
v___y_1670_ = v___y_1685_;
v___y_1671_ = v___y_1686_;
v___y_1672_ = v___x_1690_;
v___y_1673_ = v___y_1687_;
v___y_1674_ = v___x_1695_;
goto v___jp_1667_;
}
}
v___jp_1696_:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
lean_inc_ref(v___y_1697_);
v___x_1701_ = l_Array_append___redArg(v___y_1697_, v___y_1700_);
lean_dec_ref(v___y_1700_);
lean_inc(v___y_1699_);
lean_inc_n(v___x_1648_, 2);
v___x_1702_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1648_);
lean_ctor_set(v___x_1702_, 1, v___y_1699_);
lean_ctor_set(v___x_1702_, 2, v___x_1701_);
v___x_1703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1648_);
lean_ctor_set(v___x_1703_, 1, v___x_1630_);
if (lean_obj_tag(v_kind_x3f_1637_) == 0)
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_mk_empty_array_with_capacity(v___x_1631_);
v___y_1683_ = v___y_1697_;
v___y_1684_ = v___y_1698_;
v___y_1685_ = v___x_1703_;
v___y_1686_ = v___y_1699_;
v___y_1687_ = v___x_1702_;
v___y_1688_ = v___x_1704_;
goto v___jp_1682_;
}
else
{
lean_object* v_val_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v_val_1705_ = lean_ctor_get(v_kind_x3f_1637_, 0);
lean_inc(v_val_1705_);
lean_dec_ref_known(v_kind_x3f_1637_, 1);
v___x_1706_ = l_Lean_mkIdent(v_val_1705_);
v___x_1707_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc_n(v___x_1648_, 4);
v___x_1708_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1648_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
v___x_1709_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__2));
v___x_1710_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1648_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1648_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
v___x_1713_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_1714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1648_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
v___x_1715_ = l_Array_mkArray5___redArg(v___x_1708_, v___x_1710_, v___x_1712_, v___x_1706_, v___x_1714_);
v___y_1683_ = v___y_1697_;
v___y_1684_ = v___y_1698_;
v___y_1685_ = v___x_1703_;
v___y_1686_ = v___y_1699_;
v___y_1687_ = v___x_1702_;
v___y_1688_ = v___x_1715_;
goto v___jp_1682_;
}
}
v___jp_1716_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_inc_ref(v___y_1717_);
v___x_1720_ = l_Array_append___redArg(v___y_1717_, v___y_1719_);
lean_dec_ref(v___y_1719_);
lean_inc(v___y_1718_);
lean_inc(v___x_1648_);
v___x_1721_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1648_);
lean_ctor_set(v___x_1721_, 1, v___y_1718_);
lean_ctor_set(v___x_1721_, 2, v___x_1720_);
if (lean_obj_tag(v_attrs_x3f_1632_) == 1)
{
lean_object* v_val_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v_val_1722_ = lean_ctor_get(v_attrs_x3f_1632_, 0);
v___x_1723_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
v___x_1724_ = l_Lean_Name_mkStr4(v___x_1633_, v___x_1634_, v___x_1635_, v___x_1723_);
v___x_1725_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc_n(v___x_1648_, 4);
v___x_1726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1648_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
lean_inc_ref(v___y_1717_);
v___x_1727_ = l_Array_append___redArg(v___y_1717_, v_val_1722_);
lean_inc(v___y_1718_);
v___x_1728_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1648_);
lean_ctor_set(v___x_1728_, 1, v___y_1718_);
lean_ctor_set(v___x_1728_, 2, v___x_1727_);
v___x_1729_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1648_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v___x_1731_ = l_Lean_Syntax_node3(v___x_1648_, v___x_1724_, v___x_1726_, v___x_1728_, v___x_1730_);
v___x_1732_ = l_Array_mkArray1___redArg(v___x_1731_);
v___y_1697_ = v___y_1717_;
v___y_1698_ = v___x_1721_;
v___y_1699_ = v___y_1718_;
v___y_1700_ = v___x_1732_;
goto v___jp_1696_;
}
else
{
lean_object* v___x_1733_; 
lean_dec_ref(v___x_1635_);
lean_dec_ref(v___x_1634_);
lean_dec_ref(v___x_1633_);
v___x_1733_ = lean_mk_empty_array_with_capacity(v___x_1631_);
v___y_1697_ = v___y_1717_;
v___y_1698_ = v___x_1721_;
v___y_1699_ = v___y_1718_;
v___y_1700_ = v___x_1733_;
goto v___jp_1696_;
}
}
v___jp_1734_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1736_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v_doc_x3f_1636_) == 1)
{
lean_object* v_val_1737_; lean_object* v___x_1738_; 
v_val_1737_ = lean_ctor_get(v_doc_x3f_1636_, 0);
lean_inc(v_val_1737_);
lean_dec_ref_known(v_doc_x3f_1636_, 1);
v___x_1738_ = l_Array_mkArray1___redArg(v_val_1737_);
v___y_1717_ = v___x_1736_;
v___y_1718_ = v___x_1735_;
v___y_1719_ = v___x_1738_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1739_; 
lean_dec(v_doc_x3f_1636_);
v___x_1739_ = lean_mk_empty_array_with_capacity(v___x_1631_);
v___y_1717_ = v___x_1736_;
v___y_1718_ = v___x_1735_;
v___y_1719_ = v___x_1739_;
goto v___jp_1716_;
}
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec(v_kind_x3f_1637_);
lean_dec(v_doc_x3f_1636_);
lean_dec_ref(v___x_1635_);
lean_dec_ref(v___x_1634_);
lean_dec_ref(v___x_1633_);
lean_dec_ref(v___x_1630_);
lean_dec(v_cat_x3f_1629_);
lean_dec_ref(v___f_1628_);
lean_dec(v_expty_x3f_1627_);
lean_dec(v_attrKind_1626_);
lean_dec(v___x_1625_);
lean_dec(v___x_1624_);
v_a_1752_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1642_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1642_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___boxed(lean_object** _args){
lean_object* v___x_1760_ = _args[0];
lean_object* v___x_1761_ = _args[1];
lean_object* v_attrKind_1762_ = _args[2];
lean_object* v_expty_x3f_1763_ = _args[3];
lean_object* v___f_1764_ = _args[4];
lean_object* v_cat_x3f_1765_ = _args[5];
lean_object* v___x_1766_ = _args[6];
lean_object* v___x_1767_ = _args[7];
lean_object* v_attrs_x3f_1768_ = _args[8];
lean_object* v___x_1769_ = _args[9];
lean_object* v___x_1770_ = _args[10];
lean_object* v___x_1771_ = _args[11];
lean_object* v_doc_x3f_1772_ = _args[12];
lean_object* v_kind_x3f_1773_ = _args[13];
lean_object* v_alts_1774_ = _args[14];
lean_object* v___y_1775_ = _args[15];
lean_object* v___y_1776_ = _args[16];
lean_object* v___y_1777_ = _args[17];
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_Elab_Command_elabElabRules___lam__1(v___x_1760_, v___x_1761_, v_attrKind_1762_, v_expty_x3f_1763_, v___f_1764_, v_cat_x3f_1765_, v___x_1766_, v___x_1767_, v_attrs_x3f_1768_, v___x_1769_, v___x_1770_, v___x_1771_, v_doc_x3f_1772_, v_kind_x3f_1773_, v_alts_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v_alts_1774_);
lean_dec(v_attrs_x3f_1768_);
lean_dec(v___x_1767_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2(lean_object* v___f_1806_, lean_object* v_stx_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1811_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1812_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___closed__0));
v___x_1814_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
lean_inc(v_stx_1807_);
v___x_1815_ = l_Lean_Syntax_isOfKind(v_stx_1807_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; 
lean_dec(v_stx_1807_);
lean_dec_ref(v___f_1806_);
v___x_1816_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1816_;
}
else
{
lean_object* v___x_1817_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v_expty_x3f_1825_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v_cat_x3f_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v_expty_x3f_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v_cat_x3f_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v_attrs_x3f_1923_; lean_object* v_doc_x3f_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v___x_1817_ = lean_unsigned_to_nat(0u);
v___x_1970_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1817_);
v___x_1971_ = l_Lean_Syntax_isNone(v___x_1970_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; uint8_t v___x_1973_; 
v___x_1972_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1970_);
v___x_1973_ = l_Lean_Syntax_matchesNull(v___x_1970_, v___x_1972_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; 
lean_dec(v___x_1970_);
lean_dec(v_stx_1807_);
lean_dec_ref(v___f_1806_);
v___x_1974_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1974_;
}
else
{
lean_object* v_doc_x3f_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v_doc_x3f_1975_ = l_Lean_Syntax_getArg(v___x_1970_, v___x_1817_);
lean_dec(v___x_1970_);
v___x_1976_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__6));
lean_inc(v_doc_x3f_1975_);
v___x_1977_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1975_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_dec(v_doc_x3f_1975_);
lean_dec(v_stx_1807_);
lean_dec_ref(v___f_1806_);
v___x_1978_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1978_;
}
else
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1979_, 0, v_doc_x3f_1975_);
v_doc_x3f_1954_ = v___x_1979_;
v___y_1955_ = v___y_1808_;
v___y_1956_ = v___y_1809_;
goto v___jp_1953_;
}
}
}
else
{
lean_object* v___x_1980_; 
lean_dec(v___x_1970_);
v___x_1980_ = lean_box(0);
v_doc_x3f_1954_ = v___x_1980_;
v___y_1955_ = v___y_1808_;
v___y_1956_ = v___y_1809_;
goto v___jp_1953_;
}
v___jp_1818_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1826_ = lean_unsigned_to_nat(7u);
v___x_1827_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1826_);
lean_dec(v_stx_1807_);
v___x_1828_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1829_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
lean_inc(v___x_1827_);
v___x_1830_ = l_Lean_Syntax_isOfKind(v___x_1827_, v___x_1829_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; 
lean_dec(v___x_1827_);
lean_dec(v_expty_x3f_1825_);
lean_dec(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec(v___y_1819_);
lean_dec_ref(v___f_1806_);
v___x_1831_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1831_;
}
else
{
lean_object* v___f_1832_; lean_object* v___x_1833_; lean_object* v_alts_1834_; lean_object* v___x_1835_; 
v___f_1832_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___lam__1___boxed), 18, 13);
lean_closure_set(v___f_1832_, 0, v___x_1829_);
lean_closure_set(v___f_1832_, 1, v___x_1814_);
lean_closure_set(v___f_1832_, 2, v___y_1822_);
lean_closure_set(v___f_1832_, 3, v_expty_x3f_1825_);
lean_closure_set(v___f_1832_, 4, v___f_1806_);
lean_closure_set(v___f_1832_, 5, v___y_1824_);
lean_closure_set(v___f_1832_, 6, v___x_1813_);
lean_closure_set(v___f_1832_, 7, v___x_1817_);
lean_closure_set(v___f_1832_, 8, v___y_1819_);
lean_closure_set(v___f_1832_, 9, v___x_1811_);
lean_closure_set(v___f_1832_, 10, v___x_1812_);
lean_closure_set(v___f_1832_, 11, v___x_1828_);
lean_closure_set(v___f_1832_, 12, v___y_1823_);
v___x_1833_ = l_Lean_Syntax_getArg(v___x_1827_, v___x_1817_);
lean_dec(v___x_1827_);
v_alts_1834_ = l_Lean_Syntax_getArgs(v___x_1833_);
lean_dec(v___x_1833_);
v___x_1835_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(v_alts_1834_, v___x_1813_, v___f_1832_, v___y_1820_, v___y_1821_);
lean_dec_ref(v_alts_1834_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
v_a_1844_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1835_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1835_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
v___jp_1852_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v___x_1861_ = lean_unsigned_to_nat(6u);
v___x_1862_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1861_);
v___x_1863_ = l_Lean_Syntax_isNone(v___x_1862_);
if (v___x_1863_ == 0)
{
uint8_t v___x_1864_; 
lean_inc(v___x_1862_);
v___x_1864_ = l_Lean_Syntax_matchesNull(v___x_1862_, v___y_1856_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; 
lean_dec(v___x_1862_);
lean_dec(v_cat_x3f_1858_);
lean_dec(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec(v_stx_1807_);
lean_dec_ref(v___f_1806_);
v___x_1865_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1865_;
}
else
{
lean_object* v_expty_x3f_1866_; lean_object* v___x_1867_; 
v_expty_x3f_1866_ = l_Lean_Syntax_getArg(v___x_1862_, v___y_1857_);
lean_dec(v___x_1862_);
v___x_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1867_, 0, v_expty_x3f_1866_);
v___y_1819_ = v___y_1853_;
v___y_1820_ = v___y_1859_;
v___y_1821_ = v___y_1860_;
v___y_1822_ = v___y_1854_;
v___y_1823_ = v___y_1855_;
v___y_1824_ = v_cat_x3f_1858_;
v_expty_x3f_1825_ = v___x_1867_;
goto v___jp_1818_;
}
}
else
{
lean_object* v___x_1868_; 
lean_dec(v___x_1862_);
v___x_1868_ = lean_box(0);
v___y_1819_ = v___y_1853_;
v___y_1820_ = v___y_1859_;
v___y_1821_ = v___y_1860_;
v___y_1822_ = v___y_1854_;
v___y_1823_ = v___y_1855_;
v___y_1824_ = v_cat_x3f_1858_;
v_expty_x3f_1825_ = v___x_1868_;
goto v___jp_1818_;
}
}
v___jp_1869_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; 
v___x_1879_ = lean_unsigned_to_nat(7u);
v___x_1880_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1879_);
lean_dec(v_stx_1807_);
v___x_1881_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(v___y_1872_);
v___x_1882_ = l_Lean_Name_mkStr4(v___x_1811_, v___x_1812_, v___y_1872_, v___x_1881_);
lean_inc(v___x_1880_);
v___x_1883_ = l_Lean_Syntax_isOfKind(v___x_1880_, v___x_1882_);
lean_dec(v___x_1882_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; 
lean_dec(v___x_1880_);
lean_dec(v_expty_x3f_1876_);
lean_dec(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec(v___y_1871_);
lean_dec(v___y_1870_);
v___x_1884_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1884_;
}
else
{
lean_object* v___x_1885_; lean_object* v_alts_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1885_ = l_Lean_Syntax_getArg(v___x_1880_, v___x_1817_);
lean_dec(v___x_1880_);
v_alts_1886_ = l_Lean_Syntax_getArgs(v___x_1885_);
lean_dec(v___x_1885_);
v___x_1887_ = l_Lean_TSyntax_getId(v___y_1871_);
lean_dec(v___y_1871_);
v___x_1888_ = l_Lean_Elab_Command_resolveSyntaxKind(v___x_1887_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1890_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v___x_1888_, 1);
v___x_1890_ = l_Lean_Elab_Command_elabElabRulesAux(v___y_1870_, v___y_1874_, v___y_1875_, v_a_1889_, v___y_1873_, v_expty_x3f_1876_, v_alts_1886_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1873_);
lean_dec(v___y_1874_);
return v___x_1890_;
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec_ref(v_alts_1886_);
lean_dec(v_expty_x3f_1876_);
lean_dec(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec(v___y_1870_);
v_a_1891_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1888_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1888_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
v___jp_1899_:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; 
v___x_1910_ = lean_unsigned_to_nat(6u);
v___x_1911_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1910_);
v___x_1912_ = l_Lean_Syntax_isNone(v___x_1911_);
if (v___x_1912_ == 0)
{
uint8_t v___x_1913_; 
lean_inc(v___x_1911_);
v___x_1913_ = l_Lean_Syntax_matchesNull(v___x_1911_, v___y_1902_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; 
lean_dec(v___x_1911_);
lean_dec(v_cat_x3f_1907_);
lean_dec(v___y_1906_);
lean_dec(v___y_1904_);
lean_dec(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec(v_stx_1807_);
v___x_1914_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1914_;
}
else
{
lean_object* v_expty_x3f_1915_; lean_object* v___x_1916_; 
v_expty_x3f_1915_ = l_Lean_Syntax_getArg(v___x_1911_, v___y_1905_);
lean_dec(v___x_1911_);
v___x_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_expty_x3f_1915_);
v___y_1870_ = v___y_1900_;
v___y_1871_ = v___y_1901_;
v___y_1872_ = v___y_1903_;
v___y_1873_ = v_cat_x3f_1907_;
v___y_1874_ = v___y_1904_;
v___y_1875_ = v___y_1906_;
v_expty_x3f_1876_ = v___x_1916_;
v___y_1877_ = v___y_1908_;
v___y_1878_ = v___y_1909_;
goto v___jp_1869_;
}
}
else
{
lean_object* v___x_1917_; 
lean_dec(v___x_1911_);
v___x_1917_ = lean_box(0);
v___y_1870_ = v___y_1900_;
v___y_1871_ = v___y_1901_;
v___y_1872_ = v___y_1903_;
v___y_1873_ = v_cat_x3f_1907_;
v___y_1874_ = v___y_1904_;
v___y_1875_ = v___y_1906_;
v_expty_x3f_1876_ = v___x_1917_;
v___y_1877_ = v___y_1908_;
v___y_1878_ = v___y_1909_;
goto v___jp_1869_;
}
}
v___jp_1918_:
{
lean_object* v___x_1924_; lean_object* v_attrKind_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1924_ = lean_unsigned_to_nat(2u);
v_attrKind_1925_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1924_);
v___x_1926_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1927_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__3));
lean_inc(v_attrKind_1925_);
v___x_1928_ = l_Lean_Syntax_isOfKind(v_attrKind_1925_, v___x_1927_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; 
lean_dec(v_attrKind_1925_);
lean_dec(v_attrs_x3f_1923_);
lean_dec(v___y_1921_);
lean_dec(v_stx_1807_);
lean_dec_ref(v___f_1806_);
v___x_1929_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1929_;
}
else
{
lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v___x_1930_ = lean_unsigned_to_nat(4u);
v___x_1931_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1930_);
lean_inc(v___x_1931_);
v___x_1932_ = l_Lean_Syntax_matchesNull(v___x_1931_, v___x_1817_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; uint8_t v___x_1934_; 
lean_dec_ref(v___f_1806_);
v___x_1933_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1931_);
v___x_1934_ = l_Lean_Syntax_matchesNull(v___x_1931_, v___x_1933_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; 
lean_dec(v___x_1931_);
lean_dec(v_attrKind_1925_);
lean_dec(v_attrs_x3f_1923_);
lean_dec(v___y_1921_);
lean_dec(v_stx_1807_);
v___x_1935_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1935_;
}
else
{
lean_object* v___x_1936_; lean_object* v_kind_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1936_ = lean_unsigned_to_nat(3u);
v_kind_1937_ = l_Lean_Syntax_getArg(v___x_1931_, v___x_1936_);
lean_dec(v___x_1931_);
v___x_1938_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1933_);
v___x_1939_ = l_Lean_Syntax_isNone(v___x_1938_);
if (v___x_1939_ == 0)
{
uint8_t v___x_1940_; 
lean_inc(v___x_1938_);
v___x_1940_ = l_Lean_Syntax_matchesNull(v___x_1938_, v___x_1924_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; 
lean_dec(v___x_1938_);
lean_dec(v_kind_1937_);
lean_dec(v_attrKind_1925_);
lean_dec(v_attrs_x3f_1923_);
lean_dec(v___y_1921_);
lean_dec(v_stx_1807_);
v___x_1941_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1941_;
}
else
{
lean_object* v_cat_x3f_1942_; lean_object* v___x_1943_; 
v_cat_x3f_1942_ = l_Lean_Syntax_getArg(v___x_1938_, v___y_1922_);
lean_dec(v___x_1938_);
v___x_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1943_, 0, v_cat_x3f_1942_);
v___y_1900_ = v___y_1921_;
v___y_1901_ = v_kind_1937_;
v___y_1902_ = v___x_1924_;
v___y_1903_ = v___x_1926_;
v___y_1904_ = v_attrs_x3f_1923_;
v___y_1905_ = v___y_1922_;
v___y_1906_ = v_attrKind_1925_;
v_cat_x3f_1907_ = v___x_1943_;
v___y_1908_ = v___y_1919_;
v___y_1909_ = v___y_1920_;
goto v___jp_1899_;
}
}
else
{
lean_object* v___x_1944_; 
lean_dec(v___x_1938_);
v___x_1944_ = lean_box(0);
v___y_1900_ = v___y_1921_;
v___y_1901_ = v_kind_1937_;
v___y_1902_ = v___x_1924_;
v___y_1903_ = v___x_1926_;
v___y_1904_ = v_attrs_x3f_1923_;
v___y_1905_ = v___y_1922_;
v___y_1906_ = v_attrKind_1925_;
v_cat_x3f_1907_ = v___x_1944_;
v___y_1908_ = v___y_1919_;
v___y_1909_ = v___y_1920_;
goto v___jp_1899_;
}
}
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; 
lean_dec(v___x_1931_);
v___x_1945_ = lean_unsigned_to_nat(5u);
v___x_1946_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1945_);
v___x_1947_ = l_Lean_Syntax_isNone(v___x_1946_);
if (v___x_1947_ == 0)
{
uint8_t v___x_1948_; 
lean_inc(v___x_1946_);
v___x_1948_ = l_Lean_Syntax_matchesNull(v___x_1946_, v___x_1924_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; 
lean_dec(v___x_1946_);
lean_dec(v_attrKind_1925_);
lean_dec(v_attrs_x3f_1923_);
lean_dec(v___y_1921_);
lean_dec(v_stx_1807_);
lean_dec_ref(v___f_1806_);
v___x_1949_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1949_;
}
else
{
lean_object* v_cat_x3f_1950_; lean_object* v___x_1951_; 
v_cat_x3f_1950_ = l_Lean_Syntax_getArg(v___x_1946_, v___y_1922_);
lean_dec(v___x_1946_);
v___x_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1951_, 0, v_cat_x3f_1950_);
v___y_1853_ = v_attrs_x3f_1923_;
v___y_1854_ = v_attrKind_1925_;
v___y_1855_ = v___y_1921_;
v___y_1856_ = v___x_1924_;
v___y_1857_ = v___y_1922_;
v_cat_x3f_1858_ = v___x_1951_;
v___y_1859_ = v___y_1919_;
v___y_1860_ = v___y_1920_;
goto v___jp_1852_;
}
}
else
{
lean_object* v___x_1952_; 
lean_dec(v___x_1946_);
v___x_1952_ = lean_box(0);
v___y_1853_ = v_attrs_x3f_1923_;
v___y_1854_ = v_attrKind_1925_;
v___y_1855_ = v___y_1921_;
v___y_1856_ = v___x_1924_;
v___y_1857_ = v___y_1922_;
v_cat_x3f_1858_ = v___x_1952_;
v___y_1859_ = v___y_1919_;
v___y_1860_ = v___y_1920_;
goto v___jp_1852_;
}
}
}
}
v___jp_1953_:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v___x_1957_ = lean_unsigned_to_nat(1u);
v___x_1958_ = l_Lean_Syntax_getArg(v_stx_1807_, v___x_1957_);
v___x_1959_ = l_Lean_Syntax_isNone(v___x_1958_);
if (v___x_1959_ == 0)
{
uint8_t v___x_1960_; 
lean_inc(v___x_1958_);
v___x_1960_ = l_Lean_Syntax_matchesNull(v___x_1958_, v___x_1957_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; 
lean_dec(v___x_1958_);
lean_dec(v_doc_x3f_1954_);
lean_dec(v_stx_1807_);
lean_dec_ref(v___f_1806_);
v___x_1961_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1961_;
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1962_ = l_Lean_Syntax_getArg(v___x_1958_, v___x_1817_);
lean_dec(v___x_1958_);
v___x_1963_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v___x_1962_);
v___x_1964_ = l_Lean_Syntax_isOfKind(v___x_1962_, v___x_1963_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; 
lean_dec(v___x_1962_);
lean_dec(v_doc_x3f_1954_);
lean_dec(v_stx_1807_);
lean_dec_ref(v___f_1806_);
v___x_1965_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_1965_;
}
else
{
lean_object* v___x_1966_; lean_object* v_attrs_x3f_1967_; lean_object* v___x_1968_; 
v___x_1966_ = l_Lean_Syntax_getArg(v___x_1962_, v___x_1957_);
lean_dec(v___x_1962_);
v_attrs_x3f_1967_ = l_Lean_Syntax_getArgs(v___x_1966_);
lean_dec(v___x_1966_);
v___x_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1968_, 0, v_attrs_x3f_1967_);
v___y_1919_ = v___y_1955_;
v___y_1920_ = v___y_1956_;
v___y_1921_ = v_doc_x3f_1954_;
v___y_1922_ = v___x_1957_;
v_attrs_x3f_1923_ = v___x_1968_;
goto v___jp_1918_;
}
}
}
else
{
lean_object* v___x_1969_; 
lean_dec(v___x_1958_);
v___x_1969_ = lean_box(0);
v___y_1919_ = v___y_1955_;
v___y_1920_ = v___y_1956_;
v___y_1921_ = v_doc_x3f_1954_;
v___y_1922_ = v___x_1957_;
v_attrs_x3f_1923_ = v___x_1969_;
goto v___jp_1918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___boxed(lean_object* v___f_1981_, lean_object* v_stx_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Elab_Command_elabElabRules___lam__2(v___f_1981_, v_stx_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v___f_1994_; lean_object* v___x_1995_; 
v___f_1994_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___closed__1));
v___x_1995_ = l_Lean_Elab_Command_adaptExpander(v___f_1994_, v_a_1990_, v_a_1991_, v_a_1992_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___boxed(lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lean_Elab_Command_elabElabRules(v_a_1996_, v_a_1997_, v_a_1998_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1(){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2008_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2009_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
v___x_2010_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2011_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___boxed), 4, 0);
v___x_2012_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2008_, v___x_2009_, v___x_2010_, v___x_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___boxed(lean_object* v_a_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3(){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2041_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2042_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6));
v___x_2043_ = l_Lean_addBuiltinDeclarationRanges(v___x_2041_, v___x_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___boxed(lean_object* v_a_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(size_t v_sz_2046_, size_t v_i_2047_, lean_object* v_bs_2048_){
_start:
{
uint8_t v___x_2049_; 
v___x_2049_ = lean_usize_dec_lt(v_i_2047_, v_sz_2046_);
if (v___x_2049_ == 0)
{
return v_bs_2048_;
}
else
{
lean_object* v_v_2050_; lean_object* v___x_2051_; lean_object* v_bs_x27_2052_; size_t v___x_2053_; size_t v___x_2054_; lean_object* v___x_2055_; 
v_v_2050_ = lean_array_uget(v_bs_2048_, v_i_2047_);
v___x_2051_ = lean_unsigned_to_nat(0u);
v_bs_x27_2052_ = lean_array_uset(v_bs_2048_, v_i_2047_, v___x_2051_);
v___x_2053_ = ((size_t)1ULL);
v___x_2054_ = lean_usize_add(v_i_2047_, v___x_2053_);
v___x_2055_ = lean_array_uset(v_bs_x27_2052_, v_i_2047_, v_v_2050_);
v_i_2047_ = v___x_2054_;
v_bs_2048_ = v___x_2055_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2___boxed(lean_object* v_sz_2057_, lean_object* v_i_2058_, lean_object* v_bs_2059_){
_start:
{
size_t v_sz_boxed_2060_; size_t v_i_boxed_2061_; lean_object* v_res_2062_; 
v_sz_boxed_2060_ = lean_unbox_usize(v_sz_2057_);
lean_dec(v_sz_2057_);
v_i_boxed_2061_ = lean_unbox_usize(v_i_2058_);
lean_dec(v_i_2058_);
v_res_2062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_boxed_2060_, v_i_boxed_2061_, v_bs_2059_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(size_t v_sz_2063_, size_t v_i_2064_, lean_object* v_bs_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
uint8_t v___x_2069_; 
v___x_2069_ = lean_usize_dec_lt(v_i_2064_, v_sz_2063_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v_bs_2065_);
return v___x_2070_;
}
else
{
lean_object* v_v_2071_; lean_object* v___x_2072_; lean_object* v_bs_x27_2073_; lean_object* v___x_2074_; 
v_v_2071_ = lean_array_uget(v_bs_2065_, v_i_2064_);
v___x_2072_ = lean_unsigned_to_nat(0u);
v_bs_x27_2073_ = lean_array_uset(v_bs_2065_, v_i_2064_, v___x_2072_);
v___x_2074_ = l_Lean_Elab_Command_expandMacroArg(v_v_2071_, v___y_2066_, v___y_2067_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; size_t v___x_2076_; size_t v___x_2077_; lean_object* v___x_2078_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref_known(v___x_2074_, 1);
v___x_2076_ = ((size_t)1ULL);
v___x_2077_ = lean_usize_add(v_i_2064_, v___x_2076_);
v___x_2078_ = lean_array_uset(v_bs_x27_2073_, v_i_2064_, v_a_2075_);
v_i_2064_ = v___x_2077_;
v_bs_2065_ = v___x_2078_;
goto _start;
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec_ref(v_bs_x27_2073_);
v_a_2080_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2074_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2074_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1___boxed(lean_object* v_sz_2088_, lean_object* v_i_2089_, lean_object* v_bs_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
size_t v_sz_boxed_2094_; size_t v_i_boxed_2095_; lean_object* v_res_2096_; 
v_sz_boxed_2094_ = lean_unbox_usize(v_sz_2088_);
lean_dec(v_sz_2088_);
v_i_boxed_2095_ = lean_unbox_usize(v_i_2089_);
lean_dec(v_i_2089_);
v_res_2096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_boxed_2094_, v_i_boxed_2095_, v_bs_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
return v_res_2096_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(lean_object* v_keys_2097_, lean_object* v_i_2098_, lean_object* v_k_2099_){
_start:
{
lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2100_ = lean_array_get_size(v_keys_2097_);
v___x_2101_ = lean_nat_dec_lt(v_i_2098_, v___x_2100_);
if (v___x_2101_ == 0)
{
lean_dec(v_i_2098_);
return v___x_2101_;
}
else
{
lean_object* v_k_x27_2102_; uint8_t v___x_2103_; 
v_k_x27_2102_ = lean_array_fget_borrowed(v_keys_2097_, v_i_2098_);
v___x_2103_ = l_Lean_instBEqExtraModUse_beq(v_k_2099_, v_k_x27_2102_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_unsigned_to_nat(1u);
v___x_2105_ = lean_nat_add(v_i_2098_, v___x_2104_);
lean_dec(v_i_2098_);
v_i_2098_ = v___x_2105_;
goto _start;
}
else
{
lean_dec(v_i_2098_);
return v___x_2101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_keys_2107_, lean_object* v_i_2108_, lean_object* v_k_2109_){
_start:
{
uint8_t v_res_2110_; lean_object* v_r_2111_; 
v_res_2110_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_2107_, v_i_2108_, v_k_2109_);
lean_dec_ref(v_k_2109_);
lean_dec_ref(v_keys_2107_);
v_r_2111_ = lean_box(v_res_2110_);
return v_r_2111_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(lean_object* v_x_2112_, size_t v_x_2113_, lean_object* v_x_2114_){
_start:
{
if (lean_obj_tag(v_x_2112_) == 0)
{
lean_object* v_es_2115_; lean_object* v___x_2116_; size_t v___x_2117_; size_t v___x_2118_; lean_object* v_j_2119_; lean_object* v___x_2120_; 
v_es_2115_ = lean_ctor_get(v_x_2112_, 0);
v___x_2116_ = lean_box(2);
v___x_2117_ = ((size_t)31ULL);
v___x_2118_ = lean_usize_land(v_x_2113_, v___x_2117_);
v_j_2119_ = lean_usize_to_nat(v___x_2118_);
v___x_2120_ = lean_array_get_borrowed(v___x_2116_, v_es_2115_, v_j_2119_);
lean_dec(v_j_2119_);
switch(lean_obj_tag(v___x_2120_))
{
case 0:
{
lean_object* v_key_2121_; uint8_t v___x_2122_; 
v_key_2121_ = lean_ctor_get(v___x_2120_, 0);
v___x_2122_ = l_Lean_instBEqExtraModUse_beq(v_x_2114_, v_key_2121_);
return v___x_2122_;
}
case 1:
{
lean_object* v_node_2123_; size_t v___x_2124_; size_t v___x_2125_; 
v_node_2123_ = lean_ctor_get(v___x_2120_, 0);
v___x_2124_ = ((size_t)5ULL);
v___x_2125_ = lean_usize_shift_right(v_x_2113_, v___x_2124_);
v_x_2112_ = v_node_2123_;
v_x_2113_ = v___x_2125_;
goto _start;
}
default: 
{
uint8_t v___x_2127_; 
v___x_2127_ = 0;
return v___x_2127_;
}
}
}
else
{
lean_object* v_ks_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; 
v_ks_2128_ = lean_ctor_get(v_x_2112_, 0);
v___x_2129_ = lean_unsigned_to_nat(0u);
v___x_2130_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_ks_2128_, v___x_2129_, v_x_2114_);
return v___x_2130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_x_2131_, lean_object* v_x_2132_, lean_object* v_x_2133_){
_start:
{
size_t v_x_16580__boxed_2134_; uint8_t v_res_2135_; lean_object* v_r_2136_; 
v_x_16580__boxed_2134_ = lean_unbox_usize(v_x_2132_);
lean_dec(v_x_2132_);
v_res_2135_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2131_, v_x_16580__boxed_2134_, v_x_2133_);
lean_dec_ref(v_x_2133_);
lean_dec_ref(v_x_2131_);
v_r_2136_ = lean_box(v_res_2135_);
return v_r_2136_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(lean_object* v_x_2137_, lean_object* v_x_2138_){
_start:
{
uint64_t v___x_2139_; size_t v___x_2140_; uint8_t v___x_2141_; 
v___x_2139_ = l_Lean_instHashableExtraModUse_hash(v_x_2138_);
v___x_2140_ = lean_uint64_to_usize(v___x_2139_);
v___x_2141_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2137_, v___x_2140_, v_x_2138_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_x_2142_, lean_object* v_x_2143_){
_start:
{
uint8_t v_res_2144_; lean_object* v_r_2145_; 
v_res_2144_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_2142_, v_x_2143_);
lean_dec_ref(v_x_2143_);
lean_dec_ref(v_x_2142_);
v_r_2145_ = lean_box(v_res_2144_);
return v_r_2145_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2146_; double v___x_2147_; 
v___x_2146_ = lean_unsigned_to_nat(0u);
v___x_2147_ = lean_float_of_nat(v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(lean_object* v_cls_2151_, lean_object* v_msg_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Lean_Elab_Command_getRef___redArg(v___y_2153_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2158_; lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2207_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2156_, 1);
v___x_2158_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_spec__4___redArg(v_msg_2152_, v___y_2154_);
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2161_ = v___x_2158_;
v_isShared_2162_ = v_isSharedCheck_2207_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2158_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2207_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; lean_object* v_traceState_2164_; lean_object* v_env_2165_; lean_object* v_messages_2166_; lean_object* v_scopes_2167_; lean_object* v_usedQuotCtxts_2168_; lean_object* v_nextMacroScope_2169_; lean_object* v_maxRecDepth_2170_; lean_object* v_ngen_2171_; lean_object* v_auxDeclNGen_2172_; lean_object* v_infoState_2173_; lean_object* v_snapshotTasks_2174_; lean_object* v_prevLinterStates_2175_; lean_object* v_codeQualityEntryTasks_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2206_; 
v___x_2163_ = lean_st_ref_take(v___y_2154_);
v_traceState_2164_ = lean_ctor_get(v___x_2163_, 9);
v_env_2165_ = lean_ctor_get(v___x_2163_, 0);
v_messages_2166_ = lean_ctor_get(v___x_2163_, 1);
v_scopes_2167_ = lean_ctor_get(v___x_2163_, 2);
v_usedQuotCtxts_2168_ = lean_ctor_get(v___x_2163_, 3);
v_nextMacroScope_2169_ = lean_ctor_get(v___x_2163_, 4);
v_maxRecDepth_2170_ = lean_ctor_get(v___x_2163_, 5);
v_ngen_2171_ = lean_ctor_get(v___x_2163_, 6);
v_auxDeclNGen_2172_ = lean_ctor_get(v___x_2163_, 7);
v_infoState_2173_ = lean_ctor_get(v___x_2163_, 8);
v_snapshotTasks_2174_ = lean_ctor_get(v___x_2163_, 10);
v_prevLinterStates_2175_ = lean_ctor_get(v___x_2163_, 11);
v_codeQualityEntryTasks_2176_ = lean_ctor_get(v___x_2163_, 12);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2178_ = v___x_2163_;
v_isShared_2179_ = v_isSharedCheck_2206_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2176_);
lean_inc(v_prevLinterStates_2175_);
lean_inc(v_snapshotTasks_2174_);
lean_inc(v_traceState_2164_);
lean_inc(v_infoState_2173_);
lean_inc(v_auxDeclNGen_2172_);
lean_inc(v_ngen_2171_);
lean_inc(v_maxRecDepth_2170_);
lean_inc(v_nextMacroScope_2169_);
lean_inc(v_usedQuotCtxts_2168_);
lean_inc(v_scopes_2167_);
lean_inc(v_messages_2166_);
lean_inc(v_env_2165_);
lean_dec(v___x_2163_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2206_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
uint64_t v_tid_2180_; lean_object* v_traces_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2205_; 
v_tid_2180_ = lean_ctor_get_uint64(v_traceState_2164_, sizeof(void*)*1);
v_traces_2181_ = lean_ctor_get(v_traceState_2164_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_traceState_2164_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2183_ = v_traceState_2164_;
v_isShared_2184_ = v_isSharedCheck_2205_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_traces_2181_);
lean_dec(v_traceState_2164_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2205_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; double v___x_2187_; uint8_t v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2185_ = lean_box(0);
v___x_2186_ = lean_box(0);
v___x_2187_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0);
v___x_2188_ = 0;
v___x_2189_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1));
v___x_2190_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2190_, 0, v_cls_2151_);
lean_ctor_set(v___x_2190_, 1, v___x_2186_);
lean_ctor_set(v___x_2190_, 2, v___x_2189_);
lean_ctor_set_float(v___x_2190_, sizeof(void*)*3, v___x_2187_);
lean_ctor_set_float(v___x_2190_, sizeof(void*)*3 + 8, v___x_2187_);
lean_ctor_set_uint8(v___x_2190_, sizeof(void*)*3 + 16, v___x_2188_);
v___x_2191_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2));
v___x_2192_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2190_);
lean_ctor_set(v___x_2192_, 1, v_a_2159_);
lean_ctor_set(v___x_2192_, 2, v___x_2191_);
v___x_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2193_, 0, v_a_2157_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v___x_2194_ = l_Lean_PersistentArray_push___redArg(v_traces_2181_, v___x_2193_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2194_);
v___x_2196_ = v___x_2183_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2194_);
lean_ctor_set_uint64(v_reuseFailAlloc_2204_, sizeof(void*)*1, v_tid_2180_);
v___x_2196_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2198_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 9, v___x_2196_);
v___x_2198_ = v___x_2178_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_env_2165_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_messages_2166_);
lean_ctor_set(v_reuseFailAlloc_2203_, 2, v_scopes_2167_);
lean_ctor_set(v_reuseFailAlloc_2203_, 3, v_usedQuotCtxts_2168_);
lean_ctor_set(v_reuseFailAlloc_2203_, 4, v_nextMacroScope_2169_);
lean_ctor_set(v_reuseFailAlloc_2203_, 5, v_maxRecDepth_2170_);
lean_ctor_set(v_reuseFailAlloc_2203_, 6, v_ngen_2171_);
lean_ctor_set(v_reuseFailAlloc_2203_, 7, v_auxDeclNGen_2172_);
lean_ctor_set(v_reuseFailAlloc_2203_, 8, v_infoState_2173_);
lean_ctor_set(v_reuseFailAlloc_2203_, 9, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2203_, 10, v_snapshotTasks_2174_);
lean_ctor_set(v_reuseFailAlloc_2203_, 11, v_prevLinterStates_2175_);
lean_ctor_set(v_reuseFailAlloc_2203_, 12, v_codeQualityEntryTasks_2176_);
v___x_2198_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2199_; lean_object* v___x_2201_; 
v___x_2199_ = lean_st_ref_put(v___y_2154_, v___x_2198_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v___x_2185_);
v___x_2201_ = v___x_2161_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2185_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec_ref(v_msg_2152_);
lean_dec(v_cls_2151_);
v_a_2208_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2156_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2156_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___boxed(lean_object* v_cls_2216_, lean_object* v_msg_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_2216_, v_msg_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___lam__0(lean_object* v___x_2222_, lean_object* v_entry_2223_, lean_object* v_s_2224_){
_start:
{
lean_object* v_addEntryFn_2225_; lean_object* v_importedEntries_2226_; lean_object* v_state_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2235_; 
v_addEntryFn_2225_ = lean_ctor_get(v___x_2222_, 3);
lean_inc(v_addEntryFn_2225_);
lean_dec_ref(v___x_2222_);
v_importedEntries_2226_ = lean_ctor_get(v_s_2224_, 0);
v_state_2227_ = lean_ctor_get(v_s_2224_, 1);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_s_2224_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2229_ = v_s_2224_;
v_isShared_2230_ = v_isSharedCheck_2235_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_state_2227_);
lean_inc(v_importedEntries_2226_);
lean_dec(v_s_2224_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2235_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v_state_2231_; lean_object* v___x_2233_; 
v_state_2231_ = lean_apply_2(v_addEntryFn_2225_, v_state_2227_, v_entry_2223_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v_state_2231_);
v___x_2233_ = v___x_2229_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_importedEntries_2226_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_state_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2236_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3));
v___x_2242_ = l_Lean_stringToMessageData(v___x_2241_);
return v___x_2242_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5));
v___x_2245_ = l_Lean_stringToMessageData(v___x_2244_);
return v___x_2245_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1));
v___x_2247_ = l_Lean_stringToMessageData(v___x_2246_);
return v___x_2247_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v_cls_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v_cls_2251_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2));
v___x_2252_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9));
v___x_2253_ = l_Lean_Name_append(v___x_2252_, v_cls_2251_);
return v___x_2253_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11));
v___x_2256_ = l_Lean_stringToMessageData(v___x_2255_);
return v___x_2256_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13));
v___x_2259_ = l_Lean_stringToMessageData(v___x_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(lean_object* v_mod_2264_, uint8_t v_isMeta_2265_, lean_object* v_hint_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v_env_2291_; uint8_t v_isExporting_2292_; lean_object* v_entry_2293_; lean_object* v___x_2294_; lean_object* v_env_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v___x_2289_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0);
v___x_2290_ = lean_st_ref_get(v___y_2268_);
v_env_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc_ref(v_env_2291_);
lean_dec(v___x_2290_);
v_isExporting_2292_ = lean_ctor_get_uint8(v_env_2291_, sizeof(void*)*13);
lean_dec_ref(v_env_2291_);
lean_inc(v_mod_2264_);
v_entry_2293_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2293_, 0, v_mod_2264_);
lean_ctor_set_uint8(v_entry_2293_, sizeof(void*)*1, v_isExporting_2292_);
lean_ctor_set_uint8(v_entry_2293_, sizeof(void*)*1 + 1, v_isMeta_2265_);
v___x_2294_ = lean_st_ref_get(v___y_2268_);
v_env_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc_ref(v_env_2295_);
lean_dec(v___x_2294_);
v___x_2296_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2297_ = lean_box(1);
v___x_2298_ = lean_box(0);
v___x_2299_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2289_, v___x_2296_, v_env_2295_, v___x_2297_, v___x_2298_);
v___x_2300_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v___x_2299_, v_entry_2293_);
lean_dec(v___x_2299_);
if (v___x_2300_ == 0)
{
lean_object* v___f_2301_; uint8_t v___x_2302_; lean_object* v___y_2304_; lean_object* v_cls_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v_scopes_2350_; lean_object* v___x_2351_; lean_object* v_opts_2352_; uint8_t v_hasTrace_2353_; 
v___f_2301_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_2301_, 0, v___x_2296_);
lean_closure_set(v___f_2301_, 1, v_entry_2293_);
v___x_2302_ = 1;
v_cls_2326_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2));
v___x_2327_ = l_Lean_inheritedTraceOptions;
v___x_2328_ = lean_st_ref_get(v___x_2327_);
v___x_2329_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2330_ = lean_st_ref_get(v___y_2268_);
v_scopes_2350_ = lean_ctor_get(v___x_2330_, 2);
lean_inc(v_scopes_2350_);
lean_dec(v___x_2330_);
v___x_2351_ = l_List_head_x21___redArg(v___x_2329_, v_scopes_2350_);
lean_dec(v_scopes_2350_);
v_opts_2352_ = lean_ctor_get(v___x_2351_, 1);
lean_inc_ref(v_opts_2352_);
lean_dec(v___x_2351_);
v_hasTrace_2353_ = lean_ctor_get_uint8(v_opts_2352_, sizeof(void*)*1);
if (v_hasTrace_2353_ == 0)
{
lean_dec_ref(v_opts_2352_);
lean_dec(v___x_2328_);
lean_dec(v_hint_2266_);
lean_dec(v_mod_2264_);
v___y_2304_ = v___y_2268_;
goto v___jp_2303_;
}
else
{
lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2354_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10);
v___x_2355_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2328_, v_opts_2352_, v___x_2354_);
lean_dec_ref(v_opts_2352_);
lean_dec(v___x_2328_);
if (v___x_2355_ == 0)
{
lean_dec(v_hint_2266_);
lean_dec(v_mod_2264_);
v___y_2304_ = v___y_2268_;
goto v___jp_2303_;
}
else
{
lean_object* v___x_2356_; lean_object* v___y_2358_; 
v___x_2356_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12);
if (v_isExporting_2292_ == 0)
{
lean_object* v___x_2365_; 
v___x_2365_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17));
v___y_2358_ = v___x_2365_;
goto v___jp_2357_;
}
else
{
lean_object* v___x_2366_; 
v___x_2366_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18));
v___y_2358_ = v___x_2366_;
goto v___jp_2357_;
}
v___jp_2357_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
lean_inc_ref(v___y_2358_);
v___x_2359_ = l_Lean_stringToMessageData(v___y_2358_);
v___x_2360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2356_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14);
v___x_2362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2360_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
if (v_isMeta_2265_ == 0)
{
lean_object* v___x_2363_; 
v___x_2363_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15));
v___y_2337_ = v___x_2362_;
v___y_2338_ = v___x_2363_;
goto v___jp_2336_;
}
else
{
lean_object* v___x_2364_; 
v___x_2364_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16));
v___y_2337_ = v___x_2362_;
v___y_2338_ = v___x_2364_;
goto v___jp_2336_;
}
}
}
}
v___jp_2303_:
{
lean_object* v___x_2305_; lean_object* v_toEnvExtension_2306_; lean_object* v_env_2307_; lean_object* v_messages_2308_; lean_object* v_scopes_2309_; lean_object* v_usedQuotCtxts_2310_; lean_object* v_nextMacroScope_2311_; lean_object* v_maxRecDepth_2312_; lean_object* v_ngen_2313_; lean_object* v_auxDeclNGen_2314_; lean_object* v_infoState_2315_; lean_object* v_traceState_2316_; lean_object* v_snapshotTasks_2317_; lean_object* v_prevLinterStates_2318_; lean_object* v_codeQualityEntryTasks_2319_; lean_object* v_asyncMode_2320_; uint8_t v_logWrites_2321_; lean_object* v___x_2322_; 
v___x_2305_ = lean_st_ref_take(v___y_2304_);
v_toEnvExtension_2306_ = lean_ctor_get(v___x_2296_, 0);
v_env_2307_ = lean_ctor_get(v___x_2305_, 0);
lean_inc_ref(v_env_2307_);
v_messages_2308_ = lean_ctor_get(v___x_2305_, 1);
lean_inc_ref(v_messages_2308_);
v_scopes_2309_ = lean_ctor_get(v___x_2305_, 2);
lean_inc(v_scopes_2309_);
v_usedQuotCtxts_2310_ = lean_ctor_get(v___x_2305_, 3);
lean_inc(v_usedQuotCtxts_2310_);
v_nextMacroScope_2311_ = lean_ctor_get(v___x_2305_, 4);
lean_inc(v_nextMacroScope_2311_);
v_maxRecDepth_2312_ = lean_ctor_get(v___x_2305_, 5);
lean_inc(v_maxRecDepth_2312_);
v_ngen_2313_ = lean_ctor_get(v___x_2305_, 6);
lean_inc_ref(v_ngen_2313_);
v_auxDeclNGen_2314_ = lean_ctor_get(v___x_2305_, 7);
lean_inc_ref(v_auxDeclNGen_2314_);
v_infoState_2315_ = lean_ctor_get(v___x_2305_, 8);
lean_inc_ref(v_infoState_2315_);
v_traceState_2316_ = lean_ctor_get(v___x_2305_, 9);
lean_inc_ref(v_traceState_2316_);
v_snapshotTasks_2317_ = lean_ctor_get(v___x_2305_, 10);
lean_inc_ref(v_snapshotTasks_2317_);
v_prevLinterStates_2318_ = lean_ctor_get(v___x_2305_, 11);
lean_inc(v_prevLinterStates_2318_);
v_codeQualityEntryTasks_2319_ = lean_ctor_get(v___x_2305_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2319_);
lean_dec(v___x_2305_);
v_asyncMode_2320_ = lean_ctor_get(v_toEnvExtension_2306_, 2);
v_logWrites_2321_ = lean_ctor_get_uint8(v_toEnvExtension_2306_, sizeof(void*)*6);
v___x_2322_ = lean_box(0);
if (v_logWrites_2321_ == 0)
{
lean_object* v___x_2323_; 
lean_inc_ref(v_toEnvExtension_2306_);
v___x_2323_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2306_, v_env_2307_, v___f_2301_, v_asyncMode_2320_, v___x_2298_, v___x_2302_);
v___y_2271_ = v_snapshotTasks_2317_;
v___y_2272_ = v_ngen_2313_;
v___y_2273_ = v_infoState_2315_;
v___y_2274_ = v_messages_2308_;
v___y_2275_ = v_traceState_2316_;
v___y_2276_ = v_prevLinterStates_2318_;
v___y_2277_ = v_maxRecDepth_2312_;
v___y_2278_ = v_codeQualityEntryTasks_2319_;
v___y_2279_ = v___y_2304_;
v___y_2280_ = v_auxDeclNGen_2314_;
v___y_2281_ = v_usedQuotCtxts_2310_;
v___y_2282_ = v___x_2322_;
v___y_2283_ = v_scopes_2309_;
v___y_2284_ = v_nextMacroScope_2311_;
v___y_2285_ = v___x_2323_;
goto v___jp_2270_;
}
else
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
lean_inc_ref_n(v_toEnvExtension_2306_, 2);
v___x_2324_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2306_, v_env_2307_);
lean_dec_ref(v_env_2307_);
v___x_2325_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2306_, v___x_2324_, v___f_2301_, v_asyncMode_2320_, v___x_2298_, v___x_2302_);
v___y_2271_ = v_snapshotTasks_2317_;
v___y_2272_ = v_ngen_2313_;
v___y_2273_ = v_infoState_2315_;
v___y_2274_ = v_messages_2308_;
v___y_2275_ = v_traceState_2316_;
v___y_2276_ = v_prevLinterStates_2318_;
v___y_2277_ = v_maxRecDepth_2312_;
v___y_2278_ = v_codeQualityEntryTasks_2319_;
v___y_2279_ = v___y_2304_;
v___y_2280_ = v_auxDeclNGen_2314_;
v___y_2281_ = v_usedQuotCtxts_2310_;
v___y_2282_ = v___x_2322_;
v___y_2283_ = v_scopes_2309_;
v___y_2284_ = v_nextMacroScope_2311_;
v___y_2285_ = v___x_2325_;
goto v___jp_2270_;
}
}
v___jp_2331_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___y_2332_);
lean_ctor_set(v___x_2334_, 1, v___y_2333_);
v___x_2335_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_2326_, v___x_2334_, v___y_2267_, v___y_2268_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_dec_ref_known(v___x_2335_, 1);
v___y_2304_ = v___y_2268_;
goto v___jp_2303_;
}
else
{
lean_dec_ref(v___f_2301_);
return v___x_2335_;
}
}
v___jp_2336_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; 
lean_inc_ref(v___y_2338_);
v___x_2339_ = l_Lean_stringToMessageData(v___y_2338_);
v___x_2340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___y_2337_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
v___x_2341_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4);
v___x_2342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2340_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = l_Lean_MessageData_ofName(v_mod_2264_);
v___x_2344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2342_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = l_Lean_Name_isAnonymous(v_hint_2266_);
if (v___x_2345_ == 0)
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2346_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6);
v___x_2347_ = l_Lean_MessageData_ofName(v_hint_2266_);
v___x_2348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2346_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___y_2332_ = v___x_2344_;
v___y_2333_ = v___x_2348_;
goto v___jp_2331_;
}
else
{
lean_object* v___x_2349_; 
lean_dec(v_hint_2266_);
v___x_2349_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7);
v___y_2332_ = v___x_2344_;
v___y_2333_ = v___x_2349_;
goto v___jp_2331_;
}
}
}
else
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
lean_dec_ref_known(v_entry_2293_, 1);
lean_dec(v_hint_2266_);
lean_dec(v_mod_2264_);
v___x_2367_ = lean_box(0);
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
return v___x_2368_;
}
v___jp_2270_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2286_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2286_, 0, v___y_2285_);
lean_ctor_set(v___x_2286_, 1, v___y_2274_);
lean_ctor_set(v___x_2286_, 2, v___y_2283_);
lean_ctor_set(v___x_2286_, 3, v___y_2281_);
lean_ctor_set(v___x_2286_, 4, v___y_2284_);
lean_ctor_set(v___x_2286_, 5, v___y_2277_);
lean_ctor_set(v___x_2286_, 6, v___y_2272_);
lean_ctor_set(v___x_2286_, 7, v___y_2280_);
lean_ctor_set(v___x_2286_, 8, v___y_2273_);
lean_ctor_set(v___x_2286_, 9, v___y_2275_);
lean_ctor_set(v___x_2286_, 10, v___y_2271_);
lean_ctor_set(v___x_2286_, 11, v___y_2276_);
lean_ctor_set(v___x_2286_, 12, v___y_2278_);
v___x_2287_ = lean_st_ref_put(v___y_2279_, v___x_2286_);
v___x_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2288_, 0, v___y_2282_);
return v___x_2288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___boxed(lean_object* v_mod_2369_, lean_object* v_isMeta_2370_, lean_object* v_hint_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
uint8_t v_isMeta_boxed_2375_; lean_object* v_res_2376_; 
v_isMeta_boxed_2375_ = lean_unbox(v_isMeta_2370_);
v_res_2376_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_mod_2369_, v_isMeta_boxed_2375_, v_hint_2371_, v___y_2372_, v___y_2373_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(lean_object* v___x_2377_, lean_object* v_declName_2378_, lean_object* v_as_2379_, size_t v_sz_2380_, size_t v_i_2381_, lean_object* v_b_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
uint8_t v___x_2386_; 
v___x_2386_ = lean_usize_dec_lt(v_i_2381_, v_sz_2380_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; 
lean_dec(v_declName_2378_);
v___x_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2387_, 0, v_b_2382_);
return v___x_2387_;
}
else
{
lean_object* v___x_2388_; lean_object* v_modules_2389_; lean_object* v___x_2390_; lean_object* v_a_2391_; lean_object* v___x_2392_; lean_object* v_toImport_2393_; lean_object* v_module_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; 
v___x_2388_ = l_Lean_Environment_header(v___x_2377_);
v_modules_2389_ = lean_ctor_get(v___x_2388_, 3);
lean_inc_ref(v_modules_2389_);
lean_dec_ref(v___x_2388_);
v___x_2390_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2391_ = lean_array_uget_borrowed(v_as_2379_, v_i_2381_);
v___x_2392_ = lean_array_get(v___x_2390_, v_modules_2389_, v_a_2391_);
lean_dec_ref(v_modules_2389_);
v_toImport_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc_ref(v_toImport_2393_);
lean_dec(v___x_2392_);
v_module_2394_ = lean_ctor_get(v_toImport_2393_, 0);
lean_inc(v_module_2394_);
lean_dec_ref(v_toImport_2393_);
v___x_2395_ = lean_box(0);
v___x_2396_ = 0;
lean_inc(v_declName_2378_);
v___x_2397_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_2394_, v___x_2396_, v_declName_2378_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2397_) == 0)
{
size_t v___x_2398_; size_t v___x_2399_; 
lean_dec_ref_known(v___x_2397_, 1);
v___x_2398_ = ((size_t)1ULL);
v___x_2399_ = lean_usize_add(v_i_2381_, v___x_2398_);
v_i_2381_ = v___x_2399_;
v_b_2382_ = v___x_2395_;
goto _start;
}
else
{
lean_dec(v_declName_2378_);
return v___x_2397_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4___boxed(lean_object* v___x_2401_, lean_object* v_declName_2402_, lean_object* v_as_2403_, lean_object* v_sz_2404_, lean_object* v_i_2405_, lean_object* v_b_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
size_t v_sz_boxed_2410_; size_t v_i_boxed_2411_; lean_object* v_res_2412_; 
v_sz_boxed_2410_ = lean_unbox_usize(v_sz_2404_);
lean_dec(v_sz_2404_);
v_i_boxed_2411_ = lean_unbox_usize(v_i_2405_);
lean_dec(v_i_2405_);
v_res_2412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v___x_2401_, v_declName_2402_, v_as_2403_, v_sz_boxed_2410_, v_i_boxed_2411_, v_b_2406_, v___y_2407_, v___y_2408_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec_ref(v_as_2403_);
lean_dec_ref(v___x_2401_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(lean_object* v_a_2413_, lean_object* v_x_2414_){
_start:
{
if (lean_obj_tag(v_x_2414_) == 0)
{
lean_object* v___x_2415_; 
v___x_2415_ = lean_box(0);
return v___x_2415_;
}
else
{
lean_object* v_key_2416_; lean_object* v_value_2417_; lean_object* v_tail_2418_; uint8_t v___x_2419_; 
v_key_2416_ = lean_ctor_get(v_x_2414_, 0);
v_value_2417_ = lean_ctor_get(v_x_2414_, 1);
v_tail_2418_ = lean_ctor_get(v_x_2414_, 2);
v___x_2419_ = lean_name_eq(v_key_2416_, v_a_2413_);
if (v___x_2419_ == 0)
{
v_x_2414_ = v_tail_2418_;
goto _start;
}
else
{
lean_object* v___x_2421_; 
lean_inc(v_value_2417_);
v___x_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2421_, 0, v_value_2417_);
return v___x_2421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v_a_2422_, lean_object* v_x_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_2422_, v_x_2423_);
lean_dec(v_x_2423_);
lean_dec(v_a_2422_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(lean_object* v_m_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v_buckets_2427_; lean_object* v___x_2428_; uint64_t v___y_2430_; 
v_buckets_2427_ = lean_ctor_get(v_m_2425_, 1);
v___x_2428_ = lean_array_get_size(v_buckets_2427_);
if (lean_obj_tag(v_a_2426_) == 0)
{
uint64_t v___x_2444_; 
v___x_2444_ = 1723ULL;
v___y_2430_ = v___x_2444_;
goto v___jp_2429_;
}
else
{
uint64_t v_hash_2445_; 
v_hash_2445_ = lean_ctor_get_uint64(v_a_2426_, sizeof(void*)*2);
v___y_2430_ = v_hash_2445_;
goto v___jp_2429_;
}
v___jp_2429_:
{
uint64_t v___x_2431_; uint64_t v___x_2432_; uint64_t v_fold_2433_; uint64_t v___x_2434_; uint64_t v___x_2435_; uint64_t v___x_2436_; size_t v___x_2437_; size_t v___x_2438_; size_t v___x_2439_; size_t v___x_2440_; size_t v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2431_ = 32ULL;
v___x_2432_ = lean_uint64_shift_right(v___y_2430_, v___x_2431_);
v_fold_2433_ = lean_uint64_xor(v___y_2430_, v___x_2432_);
v___x_2434_ = 16ULL;
v___x_2435_ = lean_uint64_shift_right(v_fold_2433_, v___x_2434_);
v___x_2436_ = lean_uint64_xor(v_fold_2433_, v___x_2435_);
v___x_2437_ = lean_uint64_to_usize(v___x_2436_);
v___x_2438_ = lean_usize_of_nat(v___x_2428_);
v___x_2439_ = ((size_t)1ULL);
v___x_2440_ = lean_usize_sub(v___x_2438_, v___x_2439_);
v___x_2441_ = lean_usize_land(v___x_2437_, v___x_2440_);
v___x_2442_ = lean_array_uget_borrowed(v_buckets_2427_, v___x_2441_);
v___x_2443_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_2426_, v___x_2442_);
return v___x_2443_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_m_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_2446_, v_a_2447_);
lean_dec(v_a_2447_);
lean_dec_ref(v_m_2446_);
return v_res_2448_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(lean_object* v_declName_2452_, uint8_t v_isMeta_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v_env_2462_; lean_object* v___y_2464_; lean_object* v___x_2477_; 
v___x_2457_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0);
v___x_2458_ = lean_st_ref_get(v___y_2455_);
v_env_2462_ = lean_ctor_get(v___x_2458_, 0);
lean_inc_ref(v_env_2462_);
lean_dec(v___x_2458_);
v___x_2477_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2462_, v_declName_2452_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_dec_ref(v_env_2462_);
lean_dec(v_declName_2452_);
goto v___jp_2459_;
}
else
{
lean_object* v_val_2478_; lean_object* v___x_2479_; lean_object* v_modules_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
v_val_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_val_2478_);
lean_dec_ref_known(v___x_2477_, 1);
v___x_2479_ = l_Lean_Environment_header(v_env_2462_);
v_modules_2480_ = lean_ctor_get(v___x_2479_, 3);
lean_inc_ref(v_modules_2480_);
lean_dec_ref(v___x_2479_);
v___x_2481_ = lean_array_get_size(v_modules_2480_);
v___x_2482_ = lean_nat_dec_lt(v_val_2478_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_dec_ref(v_modules_2480_);
lean_dec(v_val_2478_);
lean_dec_ref(v_env_2462_);
lean_dec(v_declName_2452_);
goto v___jp_2459_;
}
else
{
lean_object* v___x_2483_; lean_object* v___x_2484_; uint8_t v___y_2486_; 
v___x_2483_ = lean_array_fget(v_modules_2480_, v_val_2478_);
lean_dec(v_val_2478_);
lean_dec_ref(v_modules_2480_);
v___x_2484_ = lean_st_ref_get(v___y_2455_);
if (v_isMeta_2453_ == 0)
{
lean_dec(v___x_2484_);
v___y_2486_ = v_isMeta_2453_;
goto v___jp_2485_;
}
else
{
lean_object* v_env_2497_; uint8_t v___x_2498_; 
v_env_2497_ = lean_ctor_get(v___x_2484_, 0);
lean_inc_ref(v_env_2497_);
lean_dec(v___x_2484_);
lean_inc(v_declName_2452_);
v___x_2498_ = l_Lean_isMarkedMeta(v_env_2497_, v_declName_2452_);
if (v___x_2498_ == 0)
{
v___y_2486_ = v_isMeta_2453_;
goto v___jp_2485_;
}
else
{
uint8_t v___x_2499_; 
v___x_2499_ = 0;
v___y_2486_ = v___x_2499_;
goto v___jp_2485_;
}
}
v___jp_2485_:
{
lean_object* v_toImport_2487_; lean_object* v_module_2488_; lean_object* v___x_2489_; 
v_toImport_2487_ = lean_ctor_get(v___x_2483_, 0);
lean_inc_ref(v_toImport_2487_);
lean_dec(v___x_2483_);
v_module_2488_ = lean_ctor_get(v_toImport_2487_, 0);
lean_inc(v_module_2488_);
lean_dec_ref(v_toImport_2487_);
lean_inc(v_declName_2452_);
v___x_2489_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_2488_, v___y_2486_, v_declName_2452_, v___y_2454_, v___y_2455_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
lean_dec_ref_known(v___x_2489_, 1);
v___x_2490_ = l_Lean_indirectModUseExt;
v___x_2491_ = lean_box(1);
v___x_2492_ = lean_box(0);
lean_inc_ref(v_env_2462_);
v___x_2493_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2457_, v___x_2490_, v_env_2462_, v___x_2491_, v___x_2492_);
v___x_2494_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v___x_2493_, v_declName_2452_);
lean_dec(v___x_2493_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v___x_2495_; 
v___x_2495_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1));
v___y_2464_ = v___x_2495_;
goto v___jp_2463_;
}
else
{
lean_object* v_val_2496_; 
v_val_2496_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_val_2496_);
lean_dec_ref_known(v___x_2494_, 1);
v___y_2464_ = v_val_2496_;
goto v___jp_2463_;
}
}
else
{
lean_dec_ref(v_env_2462_);
lean_dec(v_declName_2452_);
return v___x_2489_;
}
}
}
}
v___jp_2459_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = lean_box(0);
v___x_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
return v___x_2461_;
}
v___jp_2463_:
{
lean_object* v___x_2465_; size_t v_sz_2466_; size_t v___x_2467_; lean_object* v___x_2468_; 
v___x_2465_ = lean_box(0);
v_sz_2466_ = lean_array_size(v___y_2464_);
v___x_2467_ = ((size_t)0ULL);
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v_env_2462_, v_declName_2452_, v___y_2464_, v_sz_2466_, v___x_2467_, v___x_2465_, v___y_2454_, v___y_2455_);
lean_dec_ref(v___y_2464_);
lean_dec_ref(v_env_2462_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2475_ == 0)
{
lean_object* v_unused_2476_; 
v_unused_2476_ = lean_ctor_get(v___x_2468_, 0);
lean_dec(v_unused_2476_);
v___x_2470_ = v___x_2468_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_dec(v___x_2468_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v___x_2465_);
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2465_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
else
{
return v___x_2468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___boxed(lean_object* v_declName_2500_, lean_object* v_isMeta_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
uint8_t v_isMeta_boxed_2505_; lean_object* v_res_2506_; 
v_isMeta_boxed_2505_ = lean_unbox(v_isMeta_2501_);
v_res_2506_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_declName_2500_, v_isMeta_boxed_2505_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(lean_object* v_as_x27_2507_, lean_object* v_b_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
if (lean_obj_tag(v_as_x27_2507_) == 0)
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2512_, 0, v_b_2508_);
return v___x_2512_;
}
else
{
lean_object* v_head_2513_; lean_object* v_tail_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; lean_object* v___x_2517_; 
v_head_2513_ = lean_ctor_get(v_as_x27_2507_, 0);
v_tail_2514_ = lean_ctor_get(v_as_x27_2507_, 1);
v___x_2515_ = lean_box(0);
v___x_2516_ = 1;
lean_inc(v_head_2513_);
v___x_2517_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_head_2513_, v___x_2516_, v___y_2509_, v___y_2510_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_dec_ref_known(v___x_2517_, 1);
v_as_x27_2507_ = v_tail_2514_;
v_b_2508_ = v___x_2515_;
goto _start;
}
else
{
return v___x_2517_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_2519_, lean_object* v_b_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_2519_, v_b_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v_as_x27_2519_);
return v_res_2524_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = l_Lean_maxRecDepthErrorMessage;
v___x_2531_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2530_);
return v___x_2531_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3);
v___x_2533_ = l_Lean_MessageData_ofFormat(v___x_2532_);
return v___x_2533_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4);
v___x_2535_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2));
v___x_2536_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
lean_ctor_set(v___x_2536_, 1, v___x_2534_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(lean_object* v_ref_2537_){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2539_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5);
v___x_2540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2540_, 0, v_ref_2537_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
v___x_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___boxed(lean_object* v_ref_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_2542_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(lean_object* v_currNamespace_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2548_, 0, v_currNamespace_2545_);
lean_ctor_set(v___x_2548_, 1, v___y_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(v_currNamespace_2549_, v___y_2550_, v___y_2551_);
lean_dec_ref(v___y_2550_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(lean_object* v_env_2553_, lean_object* v_declName_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
uint8_t v___x_2557_; lean_object* v_env_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; uint8_t v___x_2561_; 
v___x_2557_ = 0;
v_env_2558_ = l_Lean_Environment_setExporting(v_env_2553_, v___x_2557_);
lean_inc(v_declName_2554_);
v___x_2559_ = l_Lean_mkPrivateName(v_env_2558_, v_declName_2554_);
v___x_2560_ = 1;
lean_inc_ref(v_env_2558_);
v___x_2561_ = l_Lean_Environment_contains(v_env_2558_, v___x_2559_, v___x_2560_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2562_; uint8_t v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2562_ = l_Lean_privateToUserName(v_declName_2554_);
v___x_2563_ = l_Lean_Environment_contains(v_env_2558_, v___x_2562_, v___x_2560_);
v___x_2564_ = lean_box(v___x_2563_);
v___x_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
lean_ctor_set(v___x_2565_, 1, v___y_2556_);
return v___x_2565_;
}
else
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
lean_dec_ref(v_env_2558_);
lean_dec(v_declName_2554_);
v___x_2566_ = lean_box(v___x_2561_);
v___x_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
lean_ctor_set(v___x_2567_, 1, v___y_2556_);
return v___x_2567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed(lean_object* v_env_2568_, lean_object* v_declName_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(v_env_2568_, v_declName_2569_, v___y_2570_, v___y_2571_);
lean_dec_ref(v___y_2570_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(lean_object* v_x_2573_, lean_object* v___y_2574_){
_start:
{
if (lean_obj_tag(v_x_2573_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2576_; 
v_a_2575_ = lean_ctor_get(v_x_2573_, 0);
lean_inc(v_a_2575_);
v___x_2576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2576_, 0, v_a_2575_);
lean_ctor_set(v___x_2576_, 1, v___y_2574_);
return v___x_2576_;
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2578_; 
v_a_2577_ = lean_ctor_get(v_x_2573_, 0);
lean_inc(v_a_2577_);
v___x_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2578_, 0, v_a_2577_);
lean_ctor_set(v___x_2578_, 1, v___y_2574_);
return v___x_2578_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg___boxed(lean_object* v_x_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_2579_, v___y_2580_);
lean_dec_ref(v_x_2579_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(lean_object* v_env_2582_, lean_object* v_stx_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2582_, v_stx_2583_, v___y_2584_, v___y_2585_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
if (lean_obj_tag(v_a_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2596_; 
v_a_2588_ = lean_ctor_get(v___x_2586_, 1);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2596_ == 0)
{
lean_object* v_unused_2597_; 
v_unused_2597_ = lean_ctor_get(v___x_2586_, 0);
lean_dec(v_unused_2597_);
v___x_2590_ = v___x_2586_;
v_isShared_2591_ = v_isSharedCheck_2596_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2586_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2596_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2592_ = lean_box(0);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v___x_2592_);
v___x_2594_ = v___x_2590_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2592_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v_a_2588_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
else
{
lean_object* v_val_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2626_; 
v_val_2598_ = lean_ctor_get(v_a_2587_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_a_2587_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2600_ = v_a_2587_;
v_isShared_2601_ = v_isSharedCheck_2626_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_val_2598_);
lean_dec(v_a_2587_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2626_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v_snd_2602_; 
v_snd_2602_ = lean_ctor_get(v_val_2598_, 1);
lean_inc(v_snd_2602_);
lean_dec(v_val_2598_);
if (lean_obj_tag(v_snd_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2612_; 
lean_del_object(v___x_2600_);
v_a_2603_ = lean_ctor_get(v___x_2586_, 1);
lean_inc(v_a_2603_);
lean_dec_ref_known(v___x_2586_, 2);
v_a_2604_ = lean_ctor_get(v_snd_2602_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_snd_2602_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2606_ = v_snd_2602_;
v_isShared_2607_ = v_isSharedCheck_2612_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v_snd_2602_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2612_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2610_; 
v___x_2610_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_2609_, v_a_2603_);
lean_dec_ref(v___x_2609_);
return v___x_2610_;
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2625_; 
v_a_2613_ = lean_ctor_get(v___x_2586_, 1);
lean_inc(v_a_2613_);
lean_dec_ref_known(v___x_2586_, 2);
v_a_2614_ = lean_ctor_get(v_snd_2602_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_snd_2602_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2616_ = v_snd_2602_;
v_isShared_2617_ = v_isSharedCheck_2625_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v_snd_2602_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2625_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v_a_2614_);
v___x_2619_ = v___x_2600_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
lean_object* v___x_2621_; 
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2619_);
v___x_2621_ = v___x_2616_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2622_; 
v___x_2622_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_2621_, v_a_2613_);
lean_dec_ref(v___x_2621_);
return v___x_2622_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
v_a_2627_ = lean_ctor_get(v___x_2586_, 0);
v_a_2628_ = lean_ctor_get(v___x_2586_, 1);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2586_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_inc(v_a_2627_);
lean_dec(v___x_2586_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2627_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed(lean_object* v_env_2636_, lean_object* v_stx_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(v_env_2636_, v_stx_2637_, v___y_2638_, v___y_2639_);
lean_dec_ref(v___y_2638_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(lean_object* v_env_2641_, lean_object* v_currNamespace_2642_, lean_object* v_openDecls_2643_, lean_object* v_n_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = l_Lean_ResolveName_resolveNamespace(v_env_2641_, v_currNamespace_2642_, v_openDecls_2643_, v_n_2644_);
v___x_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
lean_ctor_set(v___x_2648_, 1, v___y_2646_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed(lean_object* v_env_2649_, lean_object* v_currNamespace_2650_, lean_object* v_openDecls_2651_, lean_object* v_n_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(v_env_2649_, v_currNamespace_2650_, v_openDecls_2651_, v_n_2652_, v___y_2653_, v___y_2654_);
lean_dec_ref(v___y_2653_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(lean_object* v_as_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
if (lean_obj_tag(v_as_2656_) == 0)
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = lean_box(0);
v___x_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2660_);
return v___x_2661_;
}
else
{
lean_object* v_head_2662_; lean_object* v_tail_2663_; lean_object* v_fst_2664_; lean_object* v_snd_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v_scopes_2670_; lean_object* v___x_2671_; lean_object* v_opts_2672_; uint8_t v_hasTrace_2673_; 
v_head_2662_ = lean_ctor_get(v_as_2656_, 0);
lean_inc(v_head_2662_);
v_tail_2663_ = lean_ctor_get(v_as_2656_, 1);
lean_inc(v_tail_2663_);
lean_dec_ref_known(v_as_2656_, 2);
v_fst_2664_ = lean_ctor_get(v_head_2662_, 0);
lean_inc(v_fst_2664_);
v_snd_2665_ = lean_ctor_get(v_head_2662_, 1);
lean_inc(v_snd_2665_);
lean_dec(v_head_2662_);
v___x_2666_ = l_Lean_inheritedTraceOptions;
v___x_2667_ = lean_st_ref_get(v___x_2666_);
v___x_2668_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2669_ = lean_st_ref_get(v___y_2658_);
v_scopes_2670_ = lean_ctor_get(v___x_2669_, 2);
lean_inc(v_scopes_2670_);
lean_dec(v___x_2669_);
v___x_2671_ = l_List_head_x21___redArg(v___x_2668_, v_scopes_2670_);
lean_dec(v_scopes_2670_);
v_opts_2672_ = lean_ctor_get(v___x_2671_, 1);
lean_inc_ref(v_opts_2672_);
lean_dec(v___x_2671_);
v_hasTrace_2673_ = lean_ctor_get_uint8(v_opts_2672_, sizeof(void*)*1);
if (v_hasTrace_2673_ == 0)
{
lean_dec_ref(v_opts_2672_);
lean_dec(v___x_2667_);
lean_dec(v_snd_2665_);
lean_dec(v_fst_2664_);
v_as_2656_ = v_tail_2663_;
goto _start;
}
else
{
lean_object* v___x_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2675_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9));
lean_inc(v_fst_2664_);
v___x_2676_ = l_Lean_Name_append(v___x_2675_, v_fst_2664_);
v___x_2677_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2667_, v_opts_2672_, v___x_2676_);
lean_dec(v___x_2676_);
lean_dec_ref(v_opts_2672_);
lean_dec(v___x_2667_);
if (v___x_2677_ == 0)
{
lean_dec(v_snd_2665_);
lean_dec(v_fst_2664_);
v_as_2656_ = v_tail_2663_;
goto _start;
}
else
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2679_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2679_, 0, v_snd_2665_);
v___x_2680_ = l_Lean_MessageData_ofFormat(v___x_2679_);
v___x_2681_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_fst_2664_, v___x_2680_, v___y_2657_, v___y_2658_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_dec_ref_known(v___x_2681_, 1);
v_as_2656_ = v_tail_2663_;
goto _start;
}
else
{
lean_dec(v_tail_2663_);
return v___x_2681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___boxed(lean_object* v_as_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v_as_2683_, v___y_2684_, v___y_2685_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(lean_object* v_env_2688_, lean_object* v_opts_2689_, lean_object* v_currNamespace_2690_, lean_object* v_openDecls_2691_, lean_object* v_n_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2695_ = l_Lean_ResolveName_resolveGlobalName(v_env_2688_, v_opts_2689_, v_currNamespace_2690_, v_openDecls_2691_, v_n_2692_);
v___x_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
lean_ctor_set(v___x_2696_, 1, v___y_2694_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed(lean_object* v_env_2697_, lean_object* v_opts_2698_, lean_object* v_currNamespace_2699_, lean_object* v_openDecls_2700_, lean_object* v_n_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(v_env_2697_, v_opts_2698_, v_currNamespace_2699_, v_openDecls_2700_, v_n_2701_, v___y_2702_, v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec_ref(v_opts_2698_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(lean_object* v_x_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v___x_2710_; lean_object* v_env_2711_; lean_object* v___f_2712_; lean_object* v___f_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v_scopes_2716_; lean_object* v___x_2717_; lean_object* v_opts_2718_; lean_object* v___x_2719_; 
v___x_2710_ = lean_st_ref_get(v___y_2708_);
v_env_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc_ref_n(v_env_2711_, 3);
lean_dec(v___x_2710_);
v___f_2712_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2712_, 0, v_env_2711_);
v___f_2713_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2713_, 0, v_env_2711_);
v___x_2714_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2715_ = lean_st_ref_get(v___y_2708_);
v_scopes_2716_ = lean_ctor_get(v___x_2715_, 2);
lean_inc(v_scopes_2716_);
lean_dec(v___x_2715_);
v___x_2717_ = l_List_head_x21___redArg(v___x_2714_, v_scopes_2716_);
lean_dec(v_scopes_2716_);
v_opts_2718_ = lean_ctor_get(v___x_2717_, 1);
lean_inc_ref(v_opts_2718_);
lean_dec(v___x_2717_);
v___x_2719_ = l_Lean_Elab_Command_getScope___redArg(v___y_2708_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; lean_object* v_currNamespace_2721_; lean_object* v___f_2722_; lean_object* v___x_2723_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___x_2719_, 1);
v_currNamespace_2721_ = lean_ctor_get(v_a_2720_, 2);
lean_inc_n(v_currNamespace_2721_, 2);
lean_dec(v_a_2720_);
v___f_2722_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2722_, 0, v_currNamespace_2721_);
v___x_2723_ = l_Lean_Elab_Command_getScope___redArg(v___y_2708_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; lean_object* v_openDecls_2725_; lean_object* v___f_2726_; lean_object* v___f_2727_; lean_object* v_methods_2728_; lean_object* v___x_2729_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_a_2724_);
lean_dec_ref_known(v___x_2723_, 1);
v_openDecls_2725_ = lean_ctor_get(v_a_2724_, 3);
lean_inc_n(v_openDecls_2725_, 2);
lean_dec(v_a_2724_);
lean_inc(v_currNamespace_2721_);
lean_inc_ref(v_env_2711_);
v___f_2726_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_2726_, 0, v_env_2711_);
lean_closure_set(v___f_2726_, 1, v_currNamespace_2721_);
lean_closure_set(v___f_2726_, 2, v_openDecls_2725_);
v___f_2727_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2727_, 0, v_env_2711_);
lean_closure_set(v___f_2727_, 1, v_opts_2718_);
lean_closure_set(v___f_2727_, 2, v_currNamespace_2721_);
lean_closure_set(v___f_2727_, 3, v_openDecls_2725_);
v_methods_2728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2728_, 0, v___f_2713_);
lean_ctor_set(v_methods_2728_, 1, v___f_2722_);
lean_ctor_set(v_methods_2728_, 2, v___f_2712_);
lean_ctor_set(v_methods_2728_, 3, v___f_2726_);
lean_ctor_set(v_methods_2728_, 4, v___f_2727_);
v___x_2729_ = l_Lean_Elab_Command_getRef___redArg(v___y_2707_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; lean_object* v___x_2731_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
lean_dec_ref_known(v___x_2729_, 1);
v___x_2731_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2707_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v_currRecDepth_2733_; lean_object* v_quotContext_x3f_2734_; lean_object* v_a_2736_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
v_currRecDepth_2733_ = lean_ctor_get(v___y_2707_, 2);
v_quotContext_x3f_2734_ = lean_ctor_get(v___y_2707_, 5);
if (lean_obj_tag(v_quotContext_x3f_2734_) == 0)
{
lean_object* v___x_2810_; lean_object* v_a_2811_; 
v___x_2810_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_2708_);
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref(v___x_2810_);
v_a_2736_ = v_a_2811_;
goto v___jp_2735_;
}
else
{
lean_object* v_val_2812_; 
v_val_2812_ = lean_ctor_get(v_quotContext_x3f_2734_, 0);
lean_inc(v_val_2812_);
v_a_2736_ = v_val_2812_;
goto v___jp_2735_;
}
v___jp_2735_:
{
lean_object* v___x_2737_; lean_object* v_maxRecDepth_2738_; lean_object* v___x_2739_; lean_object* v_nextMacroScope_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2737_ = lean_st_ref_get(v___y_2708_);
v_maxRecDepth_2738_ = lean_ctor_get(v___x_2737_, 5);
lean_inc(v_maxRecDepth_2738_);
lean_dec(v___x_2737_);
v___x_2739_ = lean_st_ref_get(v___y_2708_);
v_nextMacroScope_2740_ = lean_ctor_get(v___x_2739_, 4);
lean_inc(v_nextMacroScope_2740_);
lean_dec(v___x_2739_);
lean_inc(v_currRecDepth_2733_);
v___x_2741_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2741_, 0, v_methods_2728_);
lean_ctor_set(v___x_2741_, 1, v_a_2736_);
lean_ctor_set(v___x_2741_, 2, v_a_2732_);
lean_ctor_set(v___x_2741_, 3, v_currRecDepth_2733_);
lean_ctor_set(v___x_2741_, 4, v_maxRecDepth_2738_);
lean_ctor_set(v___x_2741_, 5, v_a_2730_);
v___x_2742_ = lean_box(0);
v___x_2743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2743_, 0, v_nextMacroScope_2740_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
lean_ctor_set(v___x_2743_, 2, v___x_2742_);
v___x_2744_ = lean_apply_2(v_x_2706_, v___x_2741_, v___x_2743_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v_a_2746_; lean_object* v_macroScope_2747_; lean_object* v_traceMsgs_2748_; lean_object* v_expandedMacroDecls_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 1);
lean_inc(v_a_2745_);
v_a_2746_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2746_);
lean_dec_ref_known(v___x_2744_, 2);
v_macroScope_2747_ = lean_ctor_get(v_a_2745_, 0);
lean_inc(v_macroScope_2747_);
v_traceMsgs_2748_ = lean_ctor_get(v_a_2745_, 1);
lean_inc(v_traceMsgs_2748_);
v_expandedMacroDecls_2749_ = lean_ctor_get(v_a_2745_, 2);
lean_inc(v_expandedMacroDecls_2749_);
lean_dec(v_a_2745_);
v___x_2750_ = lean_box(0);
v___x_2751_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_expandedMacroDecls_2749_, v___x_2750_, v___y_2707_, v___y_2708_);
lean_dec(v_expandedMacroDecls_2749_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v___x_2752_; lean_object* v_env_2753_; lean_object* v_messages_2754_; lean_object* v_scopes_2755_; lean_object* v_usedQuotCtxts_2756_; lean_object* v_maxRecDepth_2757_; lean_object* v_ngen_2758_; lean_object* v_auxDeclNGen_2759_; lean_object* v_infoState_2760_; lean_object* v_traceState_2761_; lean_object* v_snapshotTasks_2762_; lean_object* v_prevLinterStates_2763_; lean_object* v_codeQualityEntryTasks_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2790_; 
lean_dec_ref_known(v___x_2751_, 1);
v___x_2752_ = lean_st_ref_take(v___y_2708_);
v_env_2753_ = lean_ctor_get(v___x_2752_, 0);
v_messages_2754_ = lean_ctor_get(v___x_2752_, 1);
v_scopes_2755_ = lean_ctor_get(v___x_2752_, 2);
v_usedQuotCtxts_2756_ = lean_ctor_get(v___x_2752_, 3);
v_maxRecDepth_2757_ = lean_ctor_get(v___x_2752_, 5);
v_ngen_2758_ = lean_ctor_get(v___x_2752_, 6);
v_auxDeclNGen_2759_ = lean_ctor_get(v___x_2752_, 7);
v_infoState_2760_ = lean_ctor_get(v___x_2752_, 8);
v_traceState_2761_ = lean_ctor_get(v___x_2752_, 9);
v_snapshotTasks_2762_ = lean_ctor_get(v___x_2752_, 10);
v_prevLinterStates_2763_ = lean_ctor_get(v___x_2752_, 11);
v_codeQualityEntryTasks_2764_ = lean_ctor_get(v___x_2752_, 12);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2790_ == 0)
{
lean_object* v_unused_2791_; 
v_unused_2791_ = lean_ctor_get(v___x_2752_, 4);
lean_dec(v_unused_2791_);
v___x_2766_ = v___x_2752_;
v_isShared_2767_ = v_isSharedCheck_2790_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2764_);
lean_inc(v_prevLinterStates_2763_);
lean_inc(v_snapshotTasks_2762_);
lean_inc(v_traceState_2761_);
lean_inc(v_infoState_2760_);
lean_inc(v_auxDeclNGen_2759_);
lean_inc(v_ngen_2758_);
lean_inc(v_maxRecDepth_2757_);
lean_inc(v_usedQuotCtxts_2756_);
lean_inc(v_scopes_2755_);
lean_inc(v_messages_2754_);
lean_inc(v_env_2753_);
lean_dec(v___x_2752_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2790_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 4, v_macroScope_2747_);
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_env_2753_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_messages_2754_);
lean_ctor_set(v_reuseFailAlloc_2789_, 2, v_scopes_2755_);
lean_ctor_set(v_reuseFailAlloc_2789_, 3, v_usedQuotCtxts_2756_);
lean_ctor_set(v_reuseFailAlloc_2789_, 4, v_macroScope_2747_);
lean_ctor_set(v_reuseFailAlloc_2789_, 5, v_maxRecDepth_2757_);
lean_ctor_set(v_reuseFailAlloc_2789_, 6, v_ngen_2758_);
lean_ctor_set(v_reuseFailAlloc_2789_, 7, v_auxDeclNGen_2759_);
lean_ctor_set(v_reuseFailAlloc_2789_, 8, v_infoState_2760_);
lean_ctor_set(v_reuseFailAlloc_2789_, 9, v_traceState_2761_);
lean_ctor_set(v_reuseFailAlloc_2789_, 10, v_snapshotTasks_2762_);
lean_ctor_set(v_reuseFailAlloc_2789_, 11, v_prevLinterStates_2763_);
lean_ctor_set(v_reuseFailAlloc_2789_, 12, v_codeQualityEntryTasks_2764_);
v___x_2769_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2770_ = lean_st_ref_put(v___y_2708_, v___x_2769_);
v___x_2771_ = l_List_reverse___redArg(v_traceMsgs_2748_);
v___x_2772_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v___x_2771_, v___y_2707_, v___y_2708_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2779_ == 0)
{
lean_object* v_unused_2780_; 
v_unused_2780_ = lean_ctor_get(v___x_2772_, 0);
lean_dec(v_unused_2780_);
v___x_2774_ = v___x_2772_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_dec(v___x_2772_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v_a_2746_);
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2746_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec(v_a_2746_);
v_a_2781_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2772_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2772_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec(v_traceMsgs_2748_);
lean_dec(v_macroScope_2747_);
lean_dec(v_a_2746_);
v_a_2792_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2751_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2751_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
else
{
lean_object* v_a_2800_; 
v_a_2800_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2744_, 2);
if (lean_obj_tag(v_a_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v_a_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; 
v_a_2801_ = lean_ctor_get(v_a_2800_, 0);
lean_inc(v_a_2801_);
v_a_2802_ = lean_ctor_get(v_a_2800_, 1);
lean_inc_ref(v_a_2802_);
lean_dec_ref_known(v_a_2800_, 2);
v___x_2803_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0));
v___x_2804_ = lean_string_dec_eq(v_a_2802_, v___x_2803_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2805_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2805_, 0, v_a_2802_);
v___x_2806_ = l_Lean_MessageData_ofFormat(v___x_2805_);
v___x_2807_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_a_2801_, v___x_2806_, v___y_2707_, v___y_2708_);
lean_dec(v_a_2801_);
return v___x_2807_;
}
else
{
lean_object* v___x_2808_; 
lean_dec_ref(v_a_2802_);
v___x_2808_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_a_2801_);
return v___x_2808_;
}
}
else
{
lean_object* v___x_2809_; 
v___x_2809_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_2809_;
}
}
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec(v_a_2730_);
lean_dec_ref_known(v_methods_2728_, 5);
lean_dec_ref(v_x_2706_);
v_a_2813_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2731_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2731_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
lean_dec_ref_known(v_methods_2728_, 5);
lean_dec_ref(v_x_2706_);
v_a_2821_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2823_ = v___x_2729_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2729_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
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
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
lean_dec_ref(v___f_2722_);
lean_dec(v_currNamespace_2721_);
lean_dec_ref(v_opts_2718_);
lean_dec_ref(v___f_2713_);
lean_dec_ref(v___f_2712_);
lean_dec_ref(v_env_2711_);
lean_dec_ref(v_x_2706_);
v_a_2829_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2723_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2723_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec_ref(v_opts_2718_);
lean_dec_ref(v___f_2713_);
lean_dec_ref(v___f_2712_);
lean_dec_ref(v_env_2711_);
lean_dec_ref(v_x_2706_);
v_a_2837_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2719_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2719_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___boxed(lean_object* v_x_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object* v_x_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___x_2935_; uint8_t v___x_2936_; 
v___x_2893_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_2894_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_2935_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
lean_inc(v_x_2889_);
v___x_2936_ = l_Lean_Syntax_isOfKind(v_x_2889_, v___x_2935_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2937_; 
lean_dec(v_x_2889_);
v___x_2937_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_2937_;
}
else
{
lean_object* v___x_2938_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; size_t v___y_3003_; uint8_t v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; size_t v___y_3094_; uint8_t v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; size_t v___y_3132_; uint8_t v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; size_t v___y_3167_; lean_object* v___y_3168_; uint8_t v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; size_t v___y_3204_; uint8_t v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v_expectedType_x3f_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v_prio_x3f_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v_name_x3f_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v_prec_x3f_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v_attrs_x3f_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v_doc_x3f_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___x_3415_; uint8_t v___x_3416_; 
v___x_2938_ = lean_unsigned_to_nat(0u);
v___x_3415_ = l_Lean_Syntax_getArg(v_x_2889_, v___x_2938_);
v___x_3416_ = l_Lean_Syntax_isNone(v___x_3415_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3417_; uint8_t v___x_3418_; 
v___x_3417_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3415_);
v___x_3418_ = l_Lean_Syntax_matchesNull(v___x_3415_, v___x_3417_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3419_; 
lean_dec(v___x_3415_);
lean_dec(v_x_2889_);
v___x_3419_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3419_;
}
else
{
lean_object* v_doc_x3f_3420_; lean_object* v___x_3421_; uint8_t v___x_3422_; 
v_doc_x3f_3420_ = l_Lean_Syntax_getArg(v___x_3415_, v___x_2938_);
lean_dec(v___x_3415_);
v___x_3421_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__6));
lean_inc(v_doc_x3f_3420_);
v___x_3422_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3420_, v___x_3421_);
if (v___x_3422_ == 0)
{
lean_object* v___x_3423_; 
lean_dec(v_doc_x3f_3420_);
lean_dec(v_x_2889_);
v___x_3423_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3423_;
}
else
{
lean_object* v___x_3424_; 
v___x_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3424_, 0, v_doc_x3f_3420_);
v_doc_x3f_3399_ = v___x_3424_;
v___y_3400_ = v_a_2890_;
v___y_3401_ = v_a_2891_;
goto v___jp_3398_;
}
}
}
else
{
lean_object* v___x_3425_; 
lean_dec(v___x_3415_);
v___x_3425_ = lean_box(0);
v_doc_x3f_3399_ = v___x_3425_;
v___y_3400_ = v_a_2890_;
v___y_3401_ = v_a_2891_;
goto v___jp_3398_;
}
v___jp_2939_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
lean_inc_ref_n(v___y_2952_, 2);
v___x_2956_ = l_Array_append___redArg(v___y_2952_, v___y_2955_);
lean_dec_ref(v___y_2955_);
lean_inc_n(v___y_2950_, 3);
lean_inc_n(v___y_2947_, 6);
v___x_2957_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2957_, 0, v___y_2947_);
lean_ctor_set(v___x_2957_, 1, v___y_2950_);
lean_ctor_set(v___x_2957_, 2, v___x_2956_);
v___x_2958_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2958_, 0, v___y_2947_);
lean_ctor_set(v___x_2958_, 1, v___y_2950_);
lean_ctor_set(v___x_2958_, 2, v___y_2952_);
lean_inc_ref(v___x_2958_);
lean_inc(v___y_2942_);
v___x_2959_ = l_Lean_Syntax_node1(v___y_2947_, v___y_2942_, v___x_2958_);
lean_inc_ref(v___y_2954_);
v___x_2960_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___y_2947_);
lean_ctor_set(v___x_2960_, 1, v___y_2954_);
lean_inc_ref(v___y_2953_);
v___x_2961_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___y_2947_);
lean_ctor_set(v___x_2961_, 1, v___y_2953_);
v___x_2962_ = l_Lean_Syntax_node2(v___y_2947_, v___y_2950_, v___x_2961_, v___y_2941_);
if (lean_obj_tag(v___y_2940_) == 1)
{
lean_object* v_val_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_val_2963_ = lean_ctor_get(v___y_2940_, 0);
lean_inc(v_val_2963_);
lean_dec_ref_known(v___y_2940_, 1);
v___x_2964_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___y_2947_);
v___x_2965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___y_2947_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v___x_2966_ = l_Array_mkArray2___redArg(v___x_2965_, v_val_2963_);
v___y_2896_ = v___y_2943_;
v___y_2897_ = v___x_2957_;
v___y_2898_ = v___y_2944_;
v___y_2899_ = v___y_2945_;
v___y_2900_ = v___y_2946_;
v___y_2901_ = v___y_2947_;
v___y_2902_ = v___y_2949_;
v___y_2903_ = v___y_2948_;
v___y_2904_ = v___y_2950_;
v___y_2905_ = v___x_2962_;
v___y_2906_ = v___y_2952_;
v___y_2907_ = v___y_2951_;
v___y_2908_ = v___x_2960_;
v___y_2909_ = v___x_2959_;
v___y_2910_ = v___x_2958_;
v___y_2911_ = v___x_2966_;
goto v___jp_2895_;
}
else
{
lean_object* v___x_2967_; 
lean_dec(v___y_2940_);
v___x_2967_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_2896_ = v___y_2943_;
v___y_2897_ = v___x_2957_;
v___y_2898_ = v___y_2944_;
v___y_2899_ = v___y_2945_;
v___y_2900_ = v___y_2946_;
v___y_2901_ = v___y_2947_;
v___y_2902_ = v___y_2949_;
v___y_2903_ = v___y_2948_;
v___y_2904_ = v___y_2950_;
v___y_2905_ = v___x_2962_;
v___y_2906_ = v___y_2952_;
v___y_2907_ = v___y_2951_;
v___y_2908_ = v___x_2960_;
v___y_2909_ = v___x_2959_;
v___y_2910_ = v___x_2958_;
v___y_2911_ = v___x_2967_;
goto v___jp_2895_;
}
}
v___jp_2968_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___closed__0));
v___x_2984_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
if (lean_obj_tag(v___y_2981_) == 1)
{
lean_object* v_val_2985_; lean_object* v___x_2986_; 
v_val_2985_ = lean_ctor_get(v___y_2981_, 0);
lean_inc(v_val_2985_);
lean_dec_ref_known(v___y_2981_, 1);
v___x_2986_ = l_Array_mkArray1___redArg(v_val_2985_);
v___y_2940_ = v___y_2969_;
v___y_2941_ = v___y_2970_;
v___y_2942_ = v___y_2971_;
v___y_2943_ = v___y_2972_;
v___y_2944_ = v___y_2973_;
v___y_2945_ = v___y_2974_;
v___y_2946_ = v___y_2975_;
v___y_2947_ = v___y_2976_;
v___y_2948_ = v___y_2977_;
v___y_2949_ = v___y_2978_;
v___y_2950_ = v___y_2979_;
v___y_2951_ = v___x_2984_;
v___y_2952_ = v___y_2980_;
v___y_2953_ = v___y_2982_;
v___y_2954_ = v___x_2983_;
v___y_2955_ = v___x_2986_;
goto v___jp_2939_;
}
else
{
lean_object* v___x_2987_; 
lean_dec(v___y_2981_);
v___x_2987_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_2940_ = v___y_2969_;
v___y_2941_ = v___y_2970_;
v___y_2942_ = v___y_2971_;
v___y_2943_ = v___y_2972_;
v___y_2944_ = v___y_2973_;
v___y_2945_ = v___y_2974_;
v___y_2946_ = v___y_2975_;
v___y_2947_ = v___y_2976_;
v___y_2948_ = v___y_2977_;
v___y_2949_ = v___y_2978_;
v___y_2950_ = v___y_2979_;
v___y_2951_ = v___x_2984_;
v___y_2952_ = v___y_2980_;
v___y_2953_ = v___y_2982_;
v___y_2954_ = v___x_2983_;
v___y_2955_ = v___x_2987_;
goto v___jp_2939_;
}
}
v___jp_2988_:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; size_t v_sz_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
lean_inc_ref_n(v___y_3007_, 2);
v___x_3012_ = l_Array_append___redArg(v___y_3007_, v___y_3011_);
lean_dec_ref(v___y_3011_);
lean_inc_n(v___y_3002_, 3);
lean_inc_n(v___y_3010_, 9);
v___x_3013_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3013_, 0, v___y_3010_);
lean_ctor_set(v___x_3013_, 1, v___y_3002_);
lean_ctor_set(v___x_3013_, 2, v___x_3012_);
v___x_3014_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
v___x_3015_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
v___x_3016_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___y_3010_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
v___x_3017_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__6));
v___x_3018_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___y_3010_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_3020_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___y_3010_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
v___x_3021_ = l_Nat_reprFast(v___y_2993_);
v___x_3022_ = lean_box(2);
v___x_3023_ = l_Lean_Syntax_mkNumLit(v___x_3021_, v___x_3022_);
v___x_3024_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_3025_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___y_3010_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = l_Lean_Syntax_node5(v___y_3010_, v___x_3014_, v___x_3016_, v___x_3018_, v___x_3020_, v___x_3023_, v___x_3025_);
v___x_3027_ = l_Lean_Syntax_node1(v___y_3010_, v___y_3002_, v___x_3026_);
v_sz_3028_ = lean_array_size(v___y_3009_);
v___x_3029_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_3028_, v___y_3003_, v___y_3009_);
v___x_3030_ = l_Array_append___redArg(v___y_3007_, v___x_3029_);
lean_dec_ref(v___x_3029_);
v___x_3031_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3031_, 0, v___y_3010_);
lean_ctor_set(v___x_3031_, 1, v___y_3002_);
lean_ctor_set(v___x_3031_, 2, v___x_3030_);
v___x_3032_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_3033_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___y_3010_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
v___x_3034_ = lean_unsigned_to_nat(10u);
v___x_3035_ = lean_mk_empty_array_with_capacity(v___x_3034_);
v___x_3036_ = lean_array_push(v___x_3035_, v___y_2990_);
v___x_3037_ = lean_array_push(v___x_3036_, v___y_3001_);
v___x_3038_ = lean_array_push(v___x_3037_, v___y_3006_);
v___x_3039_ = lean_array_push(v___x_3038_, v___y_3005_);
v___x_3040_ = lean_array_push(v___x_3039_, v___y_2997_);
v___x_3041_ = lean_array_push(v___x_3040_, v___x_3013_);
v___x_3042_ = lean_array_push(v___x_3041_, v___x_3027_);
v___x_3043_ = lean_array_push(v___x_3042_, v___x_3031_);
v___x_3044_ = lean_array_push(v___x_3043_, v___x_3033_);
lean_inc(v___y_2991_);
v___x_3045_ = lean_array_push(v___x_3044_, v___y_2991_);
lean_inc(v___y_2994_);
v___x_3046_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3046_, 0, v___y_3010_);
lean_ctor_set(v___x_3046_, 1, v___y_2994_);
lean_ctor_set(v___x_3046_, 2, v___x_3045_);
v___x_3047_ = l_Lean_Elab_Command_elabSyntax(v___x_3046_, v___y_3000_, v___y_2996_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref_known(v___x_3047_, 1);
v___x_3049_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3022_);
lean_ctor_set(v___x_3049_, 1, v_a_3048_);
lean_ctor_set(v___x_3049_, 2, v___y_2998_);
v___x_3050_ = l_Lean_Elab_Command_getRef___redArg(v___y_3000_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref_known(v___x_3050_, 1);
v___x_3052_ = l_Lean_SourceInfo_fromRef(v_a_3051_, v___y_3004_);
lean_dec(v_a_3051_);
v___x_3053_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3000_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_quotContext_x3f_3054_; 
lean_dec_ref_known(v___x_3053_, 1);
v_quotContext_x3f_3054_ = lean_ctor_get(v___y_3000_, 5);
if (lean_obj_tag(v_quotContext_x3f_3054_) == 0)
{
lean_object* v___x_3055_; 
v___x_3055_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_2996_);
lean_dec_ref(v___x_3055_);
v___y_2969_ = v___y_2989_;
v___y_2970_ = v___y_2991_;
v___y_2971_ = v___y_2992_;
v___y_2972_ = v___x_3049_;
v___y_2973_ = v___y_2995_;
v___y_2974_ = v___x_3024_;
v___y_2975_ = v___y_2996_;
v___y_2976_ = v___x_3052_;
v___y_2977_ = v___y_2999_;
v___y_2978_ = v___y_3000_;
v___y_2979_ = v___y_3002_;
v___y_2980_ = v___y_3007_;
v___y_2981_ = v___y_3008_;
v___y_2982_ = v___x_3032_;
goto v___jp_2968_;
}
else
{
v___y_2969_ = v___y_2989_;
v___y_2970_ = v___y_2991_;
v___y_2971_ = v___y_2992_;
v___y_2972_ = v___x_3049_;
v___y_2973_ = v___y_2995_;
v___y_2974_ = v___x_3024_;
v___y_2975_ = v___y_2996_;
v___y_2976_ = v___x_3052_;
v___y_2977_ = v___y_2999_;
v___y_2978_ = v___y_3000_;
v___y_2979_ = v___y_3002_;
v___y_2980_ = v___y_3007_;
v___y_2981_ = v___y_3008_;
v___y_2982_ = v___x_3032_;
goto v___jp_2968_;
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec(v___x_3052_);
lean_dec_ref_known(v___x_3049_, 3);
lean_dec(v___y_3008_);
lean_dec(v___y_2999_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
v_a_3056_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3053_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3053_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec_ref_known(v___x_3049_, 3);
lean_dec(v___y_3008_);
lean_dec(v___y_2999_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
v_a_3064_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3050_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3050_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_dec(v___y_3008_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
v_a_3072_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_3047_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3047_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3072_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
v___jp_3080_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
lean_inc_ref(v___y_3098_);
v___x_3104_ = l_Array_append___redArg(v___y_3098_, v___y_3103_);
lean_dec_ref(v___y_3103_);
lean_inc(v___y_3093_);
lean_inc(v___y_3102_);
v___x_3105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3105_, 0, v___y_3102_);
lean_ctor_set(v___x_3105_, 1, v___y_3093_);
lean_ctor_set(v___x_3105_, 2, v___x_3104_);
if (lean_obj_tag(v___y_3099_) == 1)
{
lean_object* v_val_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v_val_3106_ = lean_ctor_get(v___y_3099_, 0);
lean_inc(v_val_3106_);
lean_dec_ref_known(v___y_3099_, 1);
v___x_3107_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
v___x_3108_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc_n(v___y_3102_, 5);
v___x_3109_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___y_3102_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
v___x_3110_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__9));
v___x_3111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___y_3102_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
v___x_3112_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_3113_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___y_3102_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_3115_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3115_, 0, v___y_3102_);
lean_ctor_set(v___x_3115_, 1, v___x_3114_);
v___x_3116_ = l_Lean_Syntax_node5(v___y_3102_, v___x_3107_, v___x_3109_, v___x_3111_, v___x_3113_, v_val_3106_, v___x_3115_);
v___x_3117_ = l_Array_mkArray1___redArg(v___x_3116_);
v___y_2989_ = v___y_3081_;
v___y_2990_ = v___y_3082_;
v___y_2991_ = v___y_3083_;
v___y_2992_ = v___y_3084_;
v___y_2993_ = v___y_3085_;
v___y_2994_ = v___y_3086_;
v___y_2995_ = v___y_3087_;
v___y_2996_ = v___y_3088_;
v___y_2997_ = v___x_3105_;
v___y_2998_ = v___y_3089_;
v___y_2999_ = v___y_3091_;
v___y_3000_ = v___y_3090_;
v___y_3001_ = v___y_3092_;
v___y_3002_ = v___y_3093_;
v___y_3003_ = v___y_3094_;
v___y_3004_ = v___y_3095_;
v___y_3005_ = v___y_3096_;
v___y_3006_ = v___y_3097_;
v___y_3007_ = v___y_3098_;
v___y_3008_ = v___y_3100_;
v___y_3009_ = v___y_3101_;
v___y_3010_ = v___y_3102_;
v___y_3011_ = v___x_3117_;
goto v___jp_2988_;
}
else
{
lean_object* v___x_3118_; 
lean_dec(v___y_3099_);
v___x_3118_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_2989_ = v___y_3081_;
v___y_2990_ = v___y_3082_;
v___y_2991_ = v___y_3083_;
v___y_2992_ = v___y_3084_;
v___y_2993_ = v___y_3085_;
v___y_2994_ = v___y_3086_;
v___y_2995_ = v___y_3087_;
v___y_2996_ = v___y_3088_;
v___y_2997_ = v___x_3105_;
v___y_2998_ = v___y_3089_;
v___y_2999_ = v___y_3091_;
v___y_3000_ = v___y_3090_;
v___y_3001_ = v___y_3092_;
v___y_3002_ = v___y_3093_;
v___y_3003_ = v___y_3094_;
v___y_3004_ = v___y_3095_;
v___y_3005_ = v___y_3096_;
v___y_3006_ = v___y_3097_;
v___y_3007_ = v___y_3098_;
v___y_3008_ = v___y_3100_;
v___y_3009_ = v___y_3101_;
v___y_3010_ = v___y_3102_;
v___y_3011_ = v___x_3118_;
goto v___jp_2988_;
}
}
v___jp_3119_:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
lean_inc_ref(v___y_3137_);
v___x_3144_ = l_Array_append___redArg(v___y_3137_, v___y_3143_);
lean_dec_ref(v___y_3143_);
lean_inc(v___y_3131_);
lean_inc(v___y_3142_);
v___x_3145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3145_, 0, v___y_3142_);
lean_ctor_set(v___x_3145_, 1, v___y_3131_);
lean_ctor_set(v___x_3145_, 2, v___x_3144_);
v___x_3146_ = l_Lean_SourceInfo_fromRef(v___y_3135_, v___x_2936_);
lean_dec(v___y_3135_);
lean_inc_ref(v___y_3134_);
v___x_3147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
lean_ctor_set(v___x_3147_, 1, v___y_3134_);
if (lean_obj_tag(v___y_3140_) == 1)
{
lean_object* v_val_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v_val_3148_ = lean_ctor_get(v___y_3140_, 0);
lean_inc(v_val_3148_);
lean_dec_ref_known(v___y_3140_, 1);
v___x_3149_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
v___x_3150_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc_n(v___y_3142_, 2);
v___x_3151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___y_3142_);
lean_ctor_set(v___x_3151_, 1, v___x_3150_);
v___x_3152_ = l_Lean_Syntax_node2(v___y_3142_, v___x_3149_, v___x_3151_, v_val_3148_);
v___x_3153_ = l_Array_mkArray1___redArg(v___x_3152_);
v___y_3081_ = v___y_3120_;
v___y_3082_ = v___y_3121_;
v___y_3083_ = v___y_3122_;
v___y_3084_ = v___y_3123_;
v___y_3085_ = v___y_3124_;
v___y_3086_ = v___y_3125_;
v___y_3087_ = v___y_3126_;
v___y_3088_ = v___y_3127_;
v___y_3089_ = v___y_3128_;
v___y_3090_ = v___y_3130_;
v___y_3091_ = v___y_3129_;
v___y_3092_ = v___x_3145_;
v___y_3093_ = v___y_3131_;
v___y_3094_ = v___y_3132_;
v___y_3095_ = v___y_3133_;
v___y_3096_ = v___x_3147_;
v___y_3097_ = v___y_3136_;
v___y_3098_ = v___y_3137_;
v___y_3099_ = v___y_3138_;
v___y_3100_ = v___y_3139_;
v___y_3101_ = v___y_3141_;
v___y_3102_ = v___y_3142_;
v___y_3103_ = v___x_3153_;
goto v___jp_3080_;
}
else
{
lean_object* v___x_3154_; 
lean_dec(v___y_3140_);
v___x_3154_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_3081_ = v___y_3120_;
v___y_3082_ = v___y_3121_;
v___y_3083_ = v___y_3122_;
v___y_3084_ = v___y_3123_;
v___y_3085_ = v___y_3124_;
v___y_3086_ = v___y_3125_;
v___y_3087_ = v___y_3126_;
v___y_3088_ = v___y_3127_;
v___y_3089_ = v___y_3128_;
v___y_3090_ = v___y_3130_;
v___y_3091_ = v___y_3129_;
v___y_3092_ = v___x_3145_;
v___y_3093_ = v___y_3131_;
v___y_3094_ = v___y_3132_;
v___y_3095_ = v___y_3133_;
v___y_3096_ = v___x_3147_;
v___y_3097_ = v___y_3136_;
v___y_3098_ = v___y_3137_;
v___y_3099_ = v___y_3138_;
v___y_3100_ = v___y_3139_;
v___y_3101_ = v___y_3141_;
v___y_3102_ = v___y_3142_;
v___y_3103_ = v___x_3154_;
goto v___jp_3080_;
}
}
v___jp_3155_:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
lean_inc_ref(v___y_3172_);
v___x_3180_ = l_Array_append___redArg(v___y_3172_, v___y_3179_);
lean_dec_ref(v___y_3179_);
lean_inc(v___y_3166_);
lean_inc(v___y_3178_);
v___x_3181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3181_, 0, v___y_3178_);
lean_ctor_set(v___x_3181_, 1, v___y_3166_);
lean_ctor_set(v___x_3181_, 2, v___x_3180_);
if (lean_obj_tag(v___y_3177_) == 1)
{
lean_object* v_val_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v_val_3182_ = lean_ctor_get(v___y_3177_, 0);
lean_inc(v_val_3182_);
lean_dec_ref_known(v___y_3177_, 1);
v___x_3183_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(v___y_3161_);
v___x_3184_ = l_Lean_Name_mkStr4(v___x_2893_, v___x_2894_, v___y_3161_, v___x_3183_);
v___x_3185_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc_n(v___y_3178_, 4);
v___x_3186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___y_3178_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
lean_inc_ref(v___y_3172_);
v___x_3187_ = l_Array_append___redArg(v___y_3172_, v_val_3182_);
lean_dec(v_val_3182_);
lean_inc(v___y_3166_);
v___x_3188_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3188_, 0, v___y_3178_);
lean_ctor_set(v___x_3188_, 1, v___y_3166_);
lean_ctor_set(v___x_3188_, 2, v___x_3187_);
v___x_3189_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_3190_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___y_3178_);
lean_ctor_set(v___x_3190_, 1, v___x_3189_);
v___x_3191_ = l_Lean_Syntax_node3(v___y_3178_, v___x_3184_, v___x_3186_, v___x_3188_, v___x_3190_);
v___x_3192_ = l_Array_mkArray1___redArg(v___x_3191_);
v___y_3120_ = v___y_3156_;
v___y_3121_ = v___x_3181_;
v___y_3122_ = v___y_3157_;
v___y_3123_ = v___y_3158_;
v___y_3124_ = v___y_3159_;
v___y_3125_ = v___y_3160_;
v___y_3126_ = v___y_3161_;
v___y_3127_ = v___y_3162_;
v___y_3128_ = v___y_3163_;
v___y_3129_ = v___y_3165_;
v___y_3130_ = v___y_3164_;
v___y_3131_ = v___y_3166_;
v___y_3132_ = v___y_3167_;
v___y_3133_ = v___y_3169_;
v___y_3134_ = v___y_3168_;
v___y_3135_ = v___y_3170_;
v___y_3136_ = v___y_3171_;
v___y_3137_ = v___y_3172_;
v___y_3138_ = v___y_3173_;
v___y_3139_ = v___y_3174_;
v___y_3140_ = v___y_3176_;
v___y_3141_ = v___y_3175_;
v___y_3142_ = v___y_3178_;
v___y_3143_ = v___x_3192_;
goto v___jp_3119_;
}
else
{
lean_object* v___x_3193_; 
lean_dec(v___y_3177_);
v___x_3193_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_3120_ = v___y_3156_;
v___y_3121_ = v___x_3181_;
v___y_3122_ = v___y_3157_;
v___y_3123_ = v___y_3158_;
v___y_3124_ = v___y_3159_;
v___y_3125_ = v___y_3160_;
v___y_3126_ = v___y_3161_;
v___y_3127_ = v___y_3162_;
v___y_3128_ = v___y_3163_;
v___y_3129_ = v___y_3165_;
v___y_3130_ = v___y_3164_;
v___y_3131_ = v___y_3166_;
v___y_3132_ = v___y_3167_;
v___y_3133_ = v___y_3169_;
v___y_3134_ = v___y_3168_;
v___y_3135_ = v___y_3170_;
v___y_3136_ = v___y_3171_;
v___y_3137_ = v___y_3172_;
v___y_3138_ = v___y_3173_;
v___y_3139_ = v___y_3174_;
v___y_3140_ = v___y_3176_;
v___y_3141_ = v___y_3175_;
v___y_3142_ = v___y_3178_;
v___y_3143_ = v___x_3193_;
goto v___jp_3119_;
}
}
v___jp_3194_:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3214_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__12));
v___x_3215_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__13));
v___x_3216_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_3217_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__36, &l_Lean_Elab_Command_elabElabRulesAux___closed__36_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__36);
if (lean_obj_tag(v___y_3209_) == 1)
{
lean_object* v_val_3218_; lean_object* v___x_3219_; 
v_val_3218_ = lean_ctor_get(v___y_3209_, 0);
lean_inc(v_val_3218_);
v___x_3219_ = l_Array_mkArray1___redArg(v_val_3218_);
v___y_3156_ = v___y_3195_;
v___y_3157_ = v___y_3196_;
v___y_3158_ = v___y_3197_;
v___y_3159_ = v___y_3198_;
v___y_3160_ = v___x_3215_;
v___y_3161_ = v___y_3199_;
v___y_3162_ = v___y_3200_;
v___y_3163_ = v___y_3201_;
v___y_3164_ = v___y_3202_;
v___y_3165_ = v___y_3203_;
v___y_3166_ = v___x_3216_;
v___y_3167_ = v___y_3204_;
v___y_3168_ = v___x_3214_;
v___y_3169_ = v___y_3205_;
v___y_3170_ = v___y_3206_;
v___y_3171_ = v___y_3207_;
v___y_3172_ = v___x_3217_;
v___y_3173_ = v___y_3208_;
v___y_3174_ = v___y_3209_;
v___y_3175_ = v___y_3211_;
v___y_3176_ = v___y_3210_;
v___y_3177_ = v___y_3212_;
v___y_3178_ = v___y_3213_;
v___y_3179_ = v___x_3219_;
goto v___jp_3155_;
}
else
{
lean_object* v___x_3220_; 
v___x_3220_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___y_3156_ = v___y_3195_;
v___y_3157_ = v___y_3196_;
v___y_3158_ = v___y_3197_;
v___y_3159_ = v___y_3198_;
v___y_3160_ = v___x_3215_;
v___y_3161_ = v___y_3199_;
v___y_3162_ = v___y_3200_;
v___y_3163_ = v___y_3201_;
v___y_3164_ = v___y_3202_;
v___y_3165_ = v___y_3203_;
v___y_3166_ = v___x_3216_;
v___y_3167_ = v___y_3204_;
v___y_3168_ = v___x_3214_;
v___y_3169_ = v___y_3205_;
v___y_3170_ = v___y_3206_;
v___y_3171_ = v___y_3207_;
v___y_3172_ = v___x_3217_;
v___y_3173_ = v___y_3208_;
v___y_3174_ = v___y_3209_;
v___y_3175_ = v___y_3211_;
v___y_3176_ = v___y_3210_;
v___y_3177_ = v___y_3212_;
v___y_3178_ = v___y_3213_;
v___y_3179_ = v___x_3220_;
goto v___jp_3155_;
}
}
v___jp_3221_:
{
lean_object* v___x_3238_; lean_object* v_args_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3238_ = l_Lean_Syntax_getArg(v___y_3233_, v___y_3224_);
lean_dec(v___y_3233_);
v_args_3239_ = l_Lean_Syntax_getArgs(v___y_3225_);
lean_dec(v___y_3225_);
v___x_3240_ = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(v___x_3240_, 0, v___y_3227_);
v___x_3241_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v___x_3240_, v___y_3236_, v___y_3237_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; size_t v_sz_3243_; size_t v___x_3244_; lean_object* v___x_3245_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3242_);
lean_dec_ref_known(v___x_3241_, 1);
v_sz_3243_ = lean_array_size(v_args_3239_);
v___x_3244_ = ((size_t)0ULL);
v___x_3245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_3243_, v___x_3244_, v_args_3239_, v___y_3236_, v___y_3237_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v_a_3246_; lean_object* v___x_3247_; lean_object* v_fst_3248_; lean_object* v_snd_3249_; lean_object* v___x_3250_; 
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc(v_a_3246_);
lean_dec_ref_known(v___x_3245_, 1);
v___x_3247_ = l_Array_unzip___redArg(v_a_3246_);
lean_dec(v_a_3246_);
v_fst_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_fst_3248_);
v_snd_3249_ = lean_ctor_get(v___x_3247_, 1);
lean_inc(v_snd_3249_);
lean_dec_ref(v___x_3247_);
v___x_3250_ = l_Lean_Elab_Command_getRef___redArg(v___y_3236_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; uint8_t v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
lean_dec_ref_known(v___x_3250_, 1);
v___x_3252_ = 0;
v___x_3253_ = l_Lean_SourceInfo_fromRef(v_a_3251_, v___x_3252_);
lean_dec(v_a_3251_);
v___x_3254_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3236_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_quotContext_x3f_3255_; 
lean_dec_ref_known(v___x_3254_, 1);
v_quotContext_x3f_3255_ = lean_ctor_get(v___y_3236_, 5);
if (lean_obj_tag(v_quotContext_x3f_3255_) == 0)
{
lean_object* v___x_3256_; 
v___x_3256_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3237_);
lean_dec_ref(v___x_3256_);
v___y_3195_ = v_expectedType_x3f_3235_;
v___y_3196_ = v___y_3222_;
v___y_3197_ = v___y_3223_;
v___y_3198_ = v_a_3242_;
v___y_3199_ = v___y_3226_;
v___y_3200_ = v___y_3237_;
v___y_3201_ = v_snd_3249_;
v___y_3202_ = v___y_3236_;
v___y_3203_ = v___x_3238_;
v___y_3204_ = v___x_3244_;
v___y_3205_ = v___x_3252_;
v___y_3206_ = v___y_3228_;
v___y_3207_ = v___y_3229_;
v___y_3208_ = v___y_3230_;
v___y_3209_ = v___y_3231_;
v___y_3210_ = v___y_3232_;
v___y_3211_ = v_fst_3248_;
v___y_3212_ = v___y_3234_;
v___y_3213_ = v___x_3253_;
goto v___jp_3194_;
}
else
{
v___y_3195_ = v_expectedType_x3f_3235_;
v___y_3196_ = v___y_3222_;
v___y_3197_ = v___y_3223_;
v___y_3198_ = v_a_3242_;
v___y_3199_ = v___y_3226_;
v___y_3200_ = v___y_3237_;
v___y_3201_ = v_snd_3249_;
v___y_3202_ = v___y_3236_;
v___y_3203_ = v___x_3238_;
v___y_3204_ = v___x_3244_;
v___y_3205_ = v___x_3252_;
v___y_3206_ = v___y_3228_;
v___y_3207_ = v___y_3229_;
v___y_3208_ = v___y_3230_;
v___y_3209_ = v___y_3231_;
v___y_3210_ = v___y_3232_;
v___y_3211_ = v_fst_3248_;
v___y_3212_ = v___y_3234_;
v___y_3213_ = v___x_3253_;
goto v___jp_3194_;
}
}
else
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
lean_dec(v___x_3253_);
lean_dec(v_snd_3249_);
lean_dec(v_fst_3248_);
lean_dec(v_a_3242_);
lean_dec(v___x_3238_);
lean_dec(v_expectedType_x3f_3235_);
lean_dec(v___y_3234_);
lean_dec(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec(v___y_3222_);
v_a_3257_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3254_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3254_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
lean_dec(v_snd_3249_);
lean_dec(v_fst_3248_);
lean_dec(v_a_3242_);
lean_dec(v___x_3238_);
lean_dec(v_expectedType_x3f_3235_);
lean_dec(v___y_3234_);
lean_dec(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec(v___y_3222_);
v_a_3265_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v___x_3250_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3250_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
lean_dec(v_a_3242_);
lean_dec(v___x_3238_);
lean_dec(v_expectedType_x3f_3235_);
lean_dec(v___y_3234_);
lean_dec(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec(v___y_3222_);
v_a_3273_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3245_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3245_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
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
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_dec_ref(v_args_3239_);
lean_dec(v___x_3238_);
lean_dec(v_expectedType_x3f_3235_);
lean_dec(v___y_3234_);
lean_dec(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec(v___y_3222_);
v_a_3281_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3241_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3241_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
v___jp_3289_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___x_3304_ = lean_unsigned_to_nat(8u);
v___x_3305_ = l_Lean_Syntax_getArg(v_x_2889_, v___x_3304_);
v___x_3306_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__15));
lean_inc(v___x_3305_);
v___x_3307_ = l_Lean_Syntax_isOfKind(v___x_3305_, v___x_3306_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; 
lean_dec(v___x_3305_);
lean_dec(v_prio_x3f_3301_);
lean_dec(v___y_3300_);
lean_dec(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec(v_x_2889_);
v___x_3308_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3308_;
}
else
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; uint8_t v___x_3313_; 
v___x_3309_ = lean_unsigned_to_nat(7u);
v___x_3310_ = l_Lean_Syntax_getArg(v_x_2889_, v___x_3309_);
lean_dec(v_x_2889_);
v___x_3311_ = l_Lean_Syntax_getArg(v___x_3305_, v___y_3299_);
v___x_3312_ = l_Lean_Syntax_getArg(v___x_3305_, v___y_3290_);
v___x_3313_ = l_Lean_Syntax_isNone(v___x_3312_);
if (v___x_3313_ == 0)
{
uint8_t v___x_3314_; 
lean_inc(v___x_3312_);
v___x_3314_ = l_Lean_Syntax_matchesNull(v___x_3312_, v___y_3290_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; 
lean_dec(v___x_3312_);
lean_dec(v___x_3311_);
lean_dec(v___x_3310_);
lean_dec(v___x_3305_);
lean_dec(v_prio_x3f_3301_);
lean_dec(v___y_3300_);
lean_dec(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
v___x_3315_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3315_;
}
else
{
lean_object* v_expectedType_x3f_3316_; lean_object* v___x_3317_; 
v_expectedType_x3f_3316_ = l_Lean_Syntax_getArg(v___x_3312_, v___y_3299_);
lean_dec(v___x_3312_);
v___x_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3317_, 0, v_expectedType_x3f_3316_);
v___y_3222_ = v___x_3311_;
v___y_3223_ = v___y_3291_;
v___y_3224_ = v___y_3294_;
v___y_3225_ = v___x_3310_;
v___y_3226_ = v___y_3295_;
v___y_3227_ = v_prio_x3f_3301_;
v___y_3228_ = v___y_3292_;
v___y_3229_ = v___y_3293_;
v___y_3230_ = v___y_3296_;
v___y_3231_ = v___y_3297_;
v___y_3232_ = v___y_3298_;
v___y_3233_ = v___x_3305_;
v___y_3234_ = v___y_3300_;
v_expectedType_x3f_3235_ = v___x_3317_;
v___y_3236_ = v___y_3302_;
v___y_3237_ = v___y_3303_;
goto v___jp_3221_;
}
}
else
{
lean_object* v___x_3318_; 
lean_dec(v___x_3312_);
v___x_3318_ = lean_box(0);
v___y_3222_ = v___x_3311_;
v___y_3223_ = v___y_3291_;
v___y_3224_ = v___y_3294_;
v___y_3225_ = v___x_3310_;
v___y_3226_ = v___y_3295_;
v___y_3227_ = v_prio_x3f_3301_;
v___y_3228_ = v___y_3292_;
v___y_3229_ = v___y_3293_;
v___y_3230_ = v___y_3296_;
v___y_3231_ = v___y_3297_;
v___y_3232_ = v___y_3298_;
v___y_3233_ = v___x_3305_;
v___y_3234_ = v___y_3300_;
v_expectedType_x3f_3235_ = v___x_3318_;
v___y_3236_ = v___y_3302_;
v___y_3237_ = v___y_3303_;
goto v___jp_3221_;
}
}
}
v___jp_3319_:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; uint8_t v___x_3336_; 
v___x_3334_ = lean_unsigned_to_nat(6u);
v___x_3335_ = l_Lean_Syntax_getArg(v_x_2889_, v___x_3334_);
v___x_3336_ = l_Lean_Syntax_isNone(v___x_3335_);
if (v___x_3336_ == 0)
{
uint8_t v___x_3337_; 
lean_inc(v___x_3335_);
v___x_3337_ = l_Lean_Syntax_matchesNull(v___x_3335_, v___y_3328_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; 
lean_dec(v___x_3335_);
lean_dec(v_name_x3f_3331_);
lean_dec(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec(v___y_3327_);
lean_dec(v___y_3324_);
lean_dec(v___y_3322_);
lean_dec(v_x_2889_);
v___x_3338_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3338_;
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3340_; uint8_t v___x_3341_; 
v___x_3339_ = l_Lean_Syntax_getArg(v___x_3335_, v___x_2938_);
lean_dec(v___x_3335_);
v___x_3340_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
lean_inc(v___x_3339_);
v___x_3341_ = l_Lean_Syntax_isOfKind(v___x_3339_, v___x_3340_);
if (v___x_3341_ == 0)
{
lean_object* v___x_3342_; 
lean_dec(v___x_3339_);
lean_dec(v_name_x3f_3331_);
lean_dec(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec(v___y_3327_);
lean_dec(v___y_3324_);
lean_dec(v___y_3322_);
lean_dec(v_x_2889_);
v___x_3342_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3342_;
}
else
{
lean_object* v_prio_x3f_3343_; lean_object* v___x_3344_; 
v_prio_x3f_3343_ = l_Lean_Syntax_getArg(v___x_3339_, v___y_3326_);
lean_dec(v___x_3339_);
v___x_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3344_, 0, v_prio_x3f_3343_);
v___y_3290_ = v___y_3321_;
v___y_3291_ = v___y_3320_;
v___y_3292_ = v___y_3322_;
v___y_3293_ = v___y_3324_;
v___y_3294_ = v___y_3323_;
v___y_3295_ = v___y_3325_;
v___y_3296_ = v_name_x3f_3331_;
v___y_3297_ = v___y_3327_;
v___y_3298_ = v___y_3329_;
v___y_3299_ = v___y_3328_;
v___y_3300_ = v___y_3330_;
v_prio_x3f_3301_ = v___x_3344_;
v___y_3302_ = v___y_3332_;
v___y_3303_ = v___y_3333_;
goto v___jp_3289_;
}
}
}
else
{
lean_object* v___x_3345_; 
lean_dec(v___x_3335_);
v___x_3345_ = lean_box(0);
v___y_3290_ = v___y_3321_;
v___y_3291_ = v___y_3320_;
v___y_3292_ = v___y_3322_;
v___y_3293_ = v___y_3324_;
v___y_3294_ = v___y_3323_;
v___y_3295_ = v___y_3325_;
v___y_3296_ = v_name_x3f_3331_;
v___y_3297_ = v___y_3327_;
v___y_3298_ = v___y_3329_;
v___y_3299_ = v___y_3328_;
v___y_3300_ = v___y_3330_;
v_prio_x3f_3301_ = v___x_3345_;
v___y_3302_ = v___y_3332_;
v___y_3303_ = v___y_3333_;
goto v___jp_3289_;
}
}
v___jp_3346_:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
v___x_3360_ = lean_unsigned_to_nat(5u);
v___x_3361_ = l_Lean_Syntax_getArg(v_x_2889_, v___x_3360_);
v___x_3362_ = l_Lean_Syntax_isNone(v___x_3361_);
if (v___x_3362_ == 0)
{
uint8_t v___x_3363_; 
lean_inc(v___x_3361_);
v___x_3363_ = l_Lean_Syntax_matchesNull(v___x_3361_, v___y_3355_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; 
lean_dec(v___x_3361_);
lean_dec(v_prec_x3f_3357_);
lean_dec(v___y_3356_);
lean_dec(v___y_3354_);
lean_dec(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec(v_x_2889_);
v___x_3364_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3364_;
}
else
{
lean_object* v___x_3365_; lean_object* v___x_3366_; uint8_t v___x_3367_; 
v___x_3365_ = l_Lean_Syntax_getArg(v___x_3361_, v___x_2938_);
lean_dec(v___x_3361_);
v___x_3366_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
lean_inc(v___x_3365_);
v___x_3367_ = l_Lean_Syntax_isOfKind(v___x_3365_, v___x_3366_);
if (v___x_3367_ == 0)
{
lean_object* v___x_3368_; 
lean_dec(v___x_3365_);
lean_dec(v_prec_x3f_3357_);
lean_dec(v___y_3356_);
lean_dec(v___y_3354_);
lean_dec(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec(v_x_2889_);
v___x_3368_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3368_;
}
else
{
lean_object* v_name_x3f_3369_; lean_object* v___x_3370_; 
v_name_x3f_3369_ = l_Lean_Syntax_getArg(v___x_3365_, v___y_3353_);
lean_dec(v___x_3365_);
v___x_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3370_, 0, v_name_x3f_3369_);
v___y_3320_ = v___y_3348_;
v___y_3321_ = v___y_3347_;
v___y_3322_ = v___y_3349_;
v___y_3323_ = v___y_3351_;
v___y_3324_ = v___y_3350_;
v___y_3325_ = v___y_3352_;
v___y_3326_ = v___y_3353_;
v___y_3327_ = v___y_3354_;
v___y_3328_ = v___y_3355_;
v___y_3329_ = v_prec_x3f_3357_;
v___y_3330_ = v___y_3356_;
v_name_x3f_3331_ = v___x_3370_;
v___y_3332_ = v___y_3358_;
v___y_3333_ = v___y_3359_;
goto v___jp_3319_;
}
}
}
else
{
lean_object* v___x_3371_; 
lean_dec(v___x_3361_);
v___x_3371_ = lean_box(0);
v___y_3320_ = v___y_3348_;
v___y_3321_ = v___y_3347_;
v___y_3322_ = v___y_3349_;
v___y_3323_ = v___y_3351_;
v___y_3324_ = v___y_3350_;
v___y_3325_ = v___y_3352_;
v___y_3326_ = v___y_3353_;
v___y_3327_ = v___y_3354_;
v___y_3328_ = v___y_3355_;
v___y_3329_ = v_prec_x3f_3357_;
v___y_3330_ = v___y_3356_;
v_name_x3f_3331_ = v___x_3371_;
v___y_3332_ = v___y_3358_;
v___y_3333_ = v___y_3359_;
goto v___jp_3319_;
}
}
v___jp_3372_:
{
lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; 
v___x_3378_ = lean_unsigned_to_nat(2u);
v___x_3379_ = l_Lean_Syntax_getArg(v_x_2889_, v___x_3378_);
v___x_3380_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_3381_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__3));
lean_inc(v___x_3379_);
v___x_3382_ = l_Lean_Syntax_isOfKind(v___x_3379_, v___x_3381_);
if (v___x_3382_ == 0)
{
lean_object* v___x_3383_; 
lean_dec(v___x_3379_);
lean_dec(v_attrs_x3f_3375_);
lean_dec(v___y_3373_);
lean_dec(v_x_2889_);
v___x_3383_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3383_;
}
else
{
lean_object* v___x_3384_; lean_object* v_tk_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; uint8_t v___x_3388_; 
v___x_3384_ = lean_unsigned_to_nat(3u);
v_tk_3385_ = l_Lean_Syntax_getArg(v_x_2889_, v___x_3384_);
v___x_3386_ = lean_unsigned_to_nat(4u);
v___x_3387_ = l_Lean_Syntax_getArg(v_x_2889_, v___x_3386_);
v___x_3388_ = l_Lean_Syntax_isNone(v___x_3387_);
if (v___x_3388_ == 0)
{
uint8_t v___x_3389_; 
lean_inc(v___x_3387_);
v___x_3389_ = l_Lean_Syntax_matchesNull(v___x_3387_, v___y_3374_);
if (v___x_3389_ == 0)
{
lean_object* v___x_3390_; 
lean_dec(v___x_3387_);
lean_dec(v_tk_3385_);
lean_dec(v___x_3379_);
lean_dec(v_attrs_x3f_3375_);
lean_dec(v___y_3373_);
lean_dec(v_x_2889_);
v___x_3390_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3390_;
}
else
{
lean_object* v___x_3391_; lean_object* v___x_3392_; uint8_t v___x_3393_; 
v___x_3391_ = l_Lean_Syntax_getArg(v___x_3387_, v___x_2938_);
lean_dec(v___x_3387_);
v___x_3392_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
lean_inc(v___x_3391_);
v___x_3393_ = l_Lean_Syntax_isOfKind(v___x_3391_, v___x_3392_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3394_; 
lean_dec(v___x_3391_);
lean_dec(v_tk_3385_);
lean_dec(v___x_3379_);
lean_dec(v_attrs_x3f_3375_);
lean_dec(v___y_3373_);
lean_dec(v_x_2889_);
v___x_3394_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3394_;
}
else
{
lean_object* v_prec_x3f_3395_; lean_object* v___x_3396_; 
v_prec_x3f_3395_ = l_Lean_Syntax_getArg(v___x_3391_, v___y_3374_);
lean_dec(v___x_3391_);
v___x_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3396_, 0, v_prec_x3f_3395_);
v___y_3347_ = v___x_3378_;
v___y_3348_ = v___x_3381_;
v___y_3349_ = v_tk_3385_;
v___y_3350_ = v___x_3379_;
v___y_3351_ = v___x_3386_;
v___y_3352_ = v___x_3380_;
v___y_3353_ = v___x_3384_;
v___y_3354_ = v___y_3373_;
v___y_3355_ = v___y_3374_;
v___y_3356_ = v_attrs_x3f_3375_;
v_prec_x3f_3357_ = v___x_3396_;
v___y_3358_ = v___y_3376_;
v___y_3359_ = v___y_3377_;
goto v___jp_3346_;
}
}
}
else
{
lean_object* v___x_3397_; 
lean_dec(v___x_3387_);
v___x_3397_ = lean_box(0);
v___y_3347_ = v___x_3378_;
v___y_3348_ = v___x_3381_;
v___y_3349_ = v_tk_3385_;
v___y_3350_ = v___x_3379_;
v___y_3351_ = v___x_3386_;
v___y_3352_ = v___x_3380_;
v___y_3353_ = v___x_3384_;
v___y_3354_ = v___y_3373_;
v___y_3355_ = v___y_3374_;
v___y_3356_ = v_attrs_x3f_3375_;
v_prec_x3f_3357_ = v___x_3397_;
v___y_3358_ = v___y_3376_;
v___y_3359_ = v___y_3377_;
goto v___jp_3346_;
}
}
}
v___jp_3398_:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; uint8_t v___x_3404_; 
v___x_3402_ = lean_unsigned_to_nat(1u);
v___x_3403_ = l_Lean_Syntax_getArg(v_x_2889_, v___x_3402_);
v___x_3404_ = l_Lean_Syntax_isNone(v___x_3403_);
if (v___x_3404_ == 0)
{
uint8_t v___x_3405_; 
lean_inc(v___x_3403_);
v___x_3405_ = l_Lean_Syntax_matchesNull(v___x_3403_, v___x_3402_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; 
lean_dec(v___x_3403_);
lean_dec(v_doc_x3f_3399_);
lean_dec(v_x_2889_);
v___x_3406_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3406_;
}
else
{
lean_object* v___x_3407_; lean_object* v___x_3408_; uint8_t v___x_3409_; 
v___x_3407_ = l_Lean_Syntax_getArg(v___x_3403_, v___x_2938_);
lean_dec(v___x_3403_);
v___x_3408_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v___x_3407_);
v___x_3409_ = l_Lean_Syntax_isOfKind(v___x_3407_, v___x_3408_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3410_; 
lean_dec(v___x_3407_);
lean_dec(v_doc_x3f_3399_);
lean_dec(v_x_2889_);
v___x_3410_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRules_spec__0___redArg();
return v___x_3410_;
}
else
{
lean_object* v___x_3411_; lean_object* v_attrs_x3f_3412_; lean_object* v___x_3413_; 
v___x_3411_ = l_Lean_Syntax_getArg(v___x_3407_, v___x_3402_);
lean_dec(v___x_3407_);
v_attrs_x3f_3412_ = l_Lean_Syntax_getArgs(v___x_3411_);
lean_dec(v___x_3411_);
v___x_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3413_, 0, v_attrs_x3f_3412_);
v___y_3373_ = v_doc_x3f_3399_;
v___y_3374_ = v___x_3402_;
v_attrs_x3f_3375_ = v___x_3413_;
v___y_3376_ = v___y_3400_;
v___y_3377_ = v___y_3401_;
goto v___jp_3372_;
}
}
}
else
{
lean_object* v___x_3414_; 
lean_dec(v___x_3403_);
v___x_3414_ = lean_box(0);
v___y_3373_ = v_doc_x3f_3399_;
v___y_3374_ = v___x_3402_;
v_attrs_x3f_3375_ = v___x_3414_;
v___y_3376_ = v___y_3400_;
v___y_3377_ = v___y_3401_;
goto v___jp_3372_;
}
}
}
v___jp_2895_:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
lean_inc_ref(v___y_2906_);
v___x_2912_ = l_Array_append___redArg(v___y_2906_, v___y_2911_);
lean_dec_ref(v___y_2911_);
lean_inc_n(v___y_2904_, 4);
lean_inc_n(v___y_2901_, 11);
v___x_2913_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2913_, 0, v___y_2901_);
lean_ctor_set(v___x_2913_, 1, v___y_2904_);
lean_ctor_set(v___x_2913_, 2, v___x_2912_);
v___x_2914_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref_n(v___y_2898_, 3);
v___x_2915_ = l_Lean_Name_mkStr4(v___x_2893_, v___x_2894_, v___y_2898_, v___x_2914_);
v___x_2916_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_2917_ = l_Lean_Name_mkStr4(v___x_2893_, v___x_2894_, v___y_2898_, v___x_2916_);
v___x_2918_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_2919_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___y_2901_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
v___x_2920_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__0));
v___x_2921_ = l_Lean_Name_mkStr4(v___x_2893_, v___x_2894_, v___y_2898_, v___x_2920_);
v___x_2922_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__1));
v___x_2923_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___y_2901_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
lean_inc_ref(v___y_2899_);
v___x_2924_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___y_2901_);
lean_ctor_set(v___x_2924_, 1, v___y_2899_);
v___x_2925_ = l_Lean_Syntax_node3(v___y_2901_, v___x_2921_, v___x_2923_, v___y_2896_, v___x_2924_);
v___x_2926_ = l_Lean_Syntax_node1(v___y_2901_, v___y_2904_, v___x_2925_);
v___x_2927_ = l_Lean_Syntax_node1(v___y_2901_, v___y_2904_, v___x_2926_);
v___x_2928_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_2929_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2929_, 0, v___y_2901_);
lean_ctor_set(v___x_2929_, 1, v___x_2928_);
v___x_2930_ = l_Lean_Syntax_node4(v___y_2901_, v___x_2917_, v___x_2919_, v___x_2927_, v___x_2929_, v___y_2903_);
v___x_2931_ = l_Lean_Syntax_node1(v___y_2901_, v___y_2904_, v___x_2930_);
v___x_2932_ = l_Lean_Syntax_node1(v___y_2901_, v___x_2915_, v___x_2931_);
lean_inc(v___y_2910_);
lean_inc(v___y_2907_);
v___x_2933_ = l_Lean_Syntax_node8(v___y_2901_, v___y_2907_, v___y_2897_, v___y_2910_, v___y_2909_, v___y_2908_, v___y_2910_, v___y_2905_, v___x_2913_, v___x_2932_);
v___x_2934_ = l_Lean_Elab_Command_elabCommand(v___x_2933_, v___y_2902_, v___y_2900_);
return v___x_2934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___boxed(lean_object* v_x_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Lean_Elab_Command_elabElab(v_x_3426_, v_a_3427_, v_a_3428_);
lean_dec(v_a_3428_);
lean_dec_ref(v_a_3427_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(lean_object* v_00_u03b1_3431_, lean_object* v_x_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v___x_3435_; 
v___x_3435_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_3432_, v___y_3434_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3436_, lean_object* v_x_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(v_00_u03b1_3436_, v_x_3437_, v___y_3438_, v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec_ref(v_x_3437_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(lean_object* v_00_u03b1_3441_, lean_object* v_ref_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v___x_3446_; 
v___x_3446_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_3442_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___boxed(lean_object* v_00_u03b1_3447_, lean_object* v_ref_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(v_00_u03b1_3447_, v_ref_3448_, v___y_3449_, v___y_3450_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(lean_object* v_00_u03b1_3453_, lean_object* v_x_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_3454_, v___y_3455_, v___y_3456_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___boxed(lean_object* v_00_u03b1_3459_, lean_object* v_x_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(v_00_u03b1_3459_, v_x_3460_, v___y_3461_, v___y_3462_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(lean_object* v_as_3465_, lean_object* v_as_x27_3466_, lean_object* v_b_3467_, lean_object* v_a_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v___x_3472_; 
v___x_3472_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_3466_, v_b_3467_, v___y_3469_, v___y_3470_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___boxed(lean_object* v_as_3473_, lean_object* v_as_x27_3474_, lean_object* v_b_3475_, lean_object* v_a_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(v_as_3473_, v_as_x27_3474_, v_b_3475_, v_a_3476_, v___y_3477_, v___y_3478_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec(v_as_x27_3474_);
lean_dec(v_as_3473_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3481_, lean_object* v_m_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_3482_, v_a_3483_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3485_, lean_object* v_m_3486_, lean_object* v_a_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(v_00_u03b2_3485_, v_m_3486_, v_a_3487_);
lean_dec(v_a_3487_);
lean_dec_ref(v_m_3486_);
return v_res_3488_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_3489_, lean_object* v_x_3490_, lean_object* v_x_3491_){
_start:
{
uint8_t v___x_3492_; 
v___x_3492_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_3490_, v_x_3491_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3493_, lean_object* v_x_3494_, lean_object* v_x_3495_){
_start:
{
uint8_t v_res_3496_; lean_object* v_r_3497_; 
v_res_3496_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(v_00_u03b2_3493_, v_x_3494_, v_x_3495_);
lean_dec_ref(v_x_3495_);
lean_dec_ref(v_x_3494_);
v_r_3497_ = lean_box(v_res_3496_);
return v_r_3497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_3498_, lean_object* v_a_3499_, lean_object* v_x_3500_){
_start:
{
lean_object* v___x_3501_; 
v___x_3501_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_3499_, v_x_3500_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___boxed(lean_object* v_00_u03b2_3502_, lean_object* v_a_3503_, lean_object* v_x_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(v_00_u03b2_3502_, v_a_3503_, v_x_3504_);
lean_dec(v_x_3504_);
lean_dec(v_a_3503_);
return v_res_3505_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(lean_object* v_00_u03b2_3506_, lean_object* v_x_3507_, size_t v_x_3508_, lean_object* v_x_3509_){
_start:
{
uint8_t v___x_3510_; 
v___x_3510_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_3507_, v_x_3508_, v_x_3509_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3511_, lean_object* v_x_3512_, lean_object* v_x_3513_, lean_object* v_x_3514_){
_start:
{
size_t v_x_19029__boxed_3515_; uint8_t v_res_3516_; lean_object* v_r_3517_; 
v_x_19029__boxed_3515_ = lean_unbox_usize(v_x_3513_);
lean_dec(v_x_3513_);
v_res_3516_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(v_00_u03b2_3511_, v_x_3512_, v_x_19029__boxed_3515_, v_x_3514_);
lean_dec_ref(v_x_3514_);
lean_dec_ref(v_x_3512_);
v_r_3517_ = lean_box(v_res_3516_);
return v_r_3517_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(lean_object* v_00_u03b2_3518_, lean_object* v_keys_3519_, lean_object* v_vals_3520_, lean_object* v_heq_3521_, lean_object* v_i_3522_, lean_object* v_k_3523_){
_start:
{
uint8_t v___x_3524_; 
v___x_3524_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_3519_, v_i_3522_, v_k_3523_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___boxed(lean_object* v_00_u03b2_3525_, lean_object* v_keys_3526_, lean_object* v_vals_3527_, lean_object* v_heq_3528_, lean_object* v_i_3529_, lean_object* v_k_3530_){
_start:
{
uint8_t v_res_3531_; lean_object* v_r_3532_; 
v_res_3531_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(v_00_u03b2_3525_, v_keys_3526_, v_vals_3527_, v_heq_3528_, v_i_3529_, v_k_3530_);
lean_dec_ref(v_k_3530_);
lean_dec_ref(v_vals_3527_);
lean_dec_ref(v_keys_3526_);
v_r_3532_ = lean_box(v_res_3531_);
return v_r_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1(){
_start:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3540_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3541_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
v___x_3542_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3543_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElab___boxed), 4, 0);
v___x_3544_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3540_, v___x_3541_, v___x_3542_, v___x_3543_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___boxed(lean_object* v_a_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3(){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3574_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6));
v___x_3575_ = l_Lean_addBuiltinDeclarationRanges(v___x_3573_, v___x_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___boxed(lean_object* v_a_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
return v_res_3577_;
}
}
lean_object* runtime_initialize_Lean_Elab_MacroArgUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_AuxDef(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ElabRules(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_MacroArgUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_AuxDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_ElabRules(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_MacroArgUtil(uint8_t builtin);
lean_object* initialize_Lean_Elab_AuxDef(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ElabRules(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_MacroArgUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AuxDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ElabRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_ElabRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_ElabRules(builtin);
}
#ifdef __cplusplus
}
#endif
