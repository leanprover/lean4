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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Elab_Command_resolveSyntaxKind(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t l_Lean_Elab_Command_checkRuleKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isQuot(lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Parser_Command_visibility_ofAttrKind(lean_object*);
lean_object* l_Array_mkArray5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "invalid elab_rules alternative, expected syntax node kind `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "invalid elab_rules alternative, unexpected syntax node kind `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__18 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__18_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__19 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__19_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__20 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__20_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__21 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__21_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__22 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__22_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__23 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__23_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noErrorIfUnused"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__24 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__24_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "no_error_if_unused%"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__25 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__25_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "throwUnsupportedSyntax"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__26 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__26_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__27;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__26_value),LEAN_SCALAR_PTR_LITERAL(225, 251, 194, 35, 13, 152, 147, 184)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__28 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__28_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__29 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__30 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "aux_def"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__31 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value),LEAN_SCALAR_PTR_LITERAL(83, 33, 36, 212, 17, 187, 86, 94)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__32 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value;
static const lean_array_object l_Lean_Elab_Command_elabElabRulesAux___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__33 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.Term.TermElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__34 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__34_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__35;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "TermElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__36 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__36_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expectedType\?"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__37 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__37_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__38;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__37_value),LEAN_SCALAR_PTR_LITERAL(47, 72, 75, 114, 68, 52, 233, 214)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__39 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__39_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__40 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__40_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Elab.Term.withExpectedType"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__41 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__41_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__42;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "withExpectedType"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__43 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__43_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.Tactic.Tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__44 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__44_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__45;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__46 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__46_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cont"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__47 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__47_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__48;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__47_value),LEAN_SCALAR_PTR_LITERAL(53, 231, 177, 147, 174, 255, 200, 174)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__49 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__49_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Elab.Command.CommandElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__50 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__50_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__51;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "CommandElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__52 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__52_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__53 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__53_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__53_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__54 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__54_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doElem"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__55 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__55_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__55_value),LEAN_SCALAR_PTR_LITERAL(224, 169, 39, 82, 97, 101, 60, 174)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__56 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__56_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "syntax category `"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__57 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__57_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__58;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "` does not support expected type specification"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__59 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__59_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__60;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doElem_elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__61 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__61_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__61_value),LEAN_SCALAR_PTR_LITERAL(211, 179, 163, 70, 253, 44, 85, 125)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__62 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__62_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__63 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__63_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__63_value),LEAN_SCALAR_PTR_LITERAL(226, 9, 43, 122, 104, 86, 206, 223)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__64 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__64_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__65 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__65_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__65_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__66 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__66_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__67 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__67_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__67_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__68 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__68_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "conv"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__69 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__69_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__69_value),LEAN_SCALAR_PTR_LITERAL(232, 67, 39, 189, 45, 247, 54, 81)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__70 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__70_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "unsupported syntax category `"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__71 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__71_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__72;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "command_elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__73 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__73_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__73_value),LEAN_SCALAR_PTR_LITERAL(7, 200, 102, 28, 219, 237, 42, 33)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__74 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__74_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "invalid elab_rules command, specify category using `elab_rules : <cat> ...`"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__75 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__75_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__76;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elab_rules"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 70, 226, 250, 127, 121, 118, 247)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__21_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value;
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
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
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
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 177, 45, 203, 60, 20, 245, 118)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedPrio"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__4_value),LEAN_SCALAR_PTR_LITERAL(171, 32, 2, 102, 118, 75, 64, 185)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "priority"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
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
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__12_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabTail"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
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
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
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
lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(lean_object* v_val_1_, uint8_t v_canonical_2_, lean_object* v___y_3_){
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
LEAN_EXPORT void l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1_ = stack[0].m_obj;
uint8_t v_canonical_2_ = stack[1].m_num;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v_res_23_;
v_res_23_ = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(v_val_1_, v_canonical_2_, v___y_3_);
stack->m_obj
 = v_res_23_;
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg___boxed(lean_object* v_val_24_, lean_object* v_canonical_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
uint8_t v_canonical_boxed_28_; lean_object* v_res_29_; 
v_canonical_boxed_28_ = lean_unbox(v_canonical_25_);
v_res_29_ = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(v_val_24_, v_canonical_boxed_28_, v___y_26_);
lean_dec_ref(v___y_26_);
return v_res_29_;
}
}
lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0(lean_object* v_val_30_, uint8_t v_canonical_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(v_val_30_, v_canonical_31_, v___y_32_);
return v___x_35_;
}
}
LEAN_EXPORT void l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_30_ = stack[0].m_obj;
uint8_t v_canonical_31_ = stack[1].m_num;
lean_object* v___y_32_ = stack[2].m_obj;
lean_object* v___y_33_ = stack[3].m_obj;
lean_object* v_res_36_;
v_res_36_ = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0(v_val_30_, v_canonical_31_, v___y_32_, v___y_33_);
stack->m_obj
 = v_res_36_;
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___boxed(lean_object* v_val_37_, lean_object* v_canonical_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
uint8_t v_canonical_boxed_42_; lean_object* v_res_43_; 
v_canonical_boxed_42_ = lean_unbox(v_canonical_38_);
v_res_43_ = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0(v_val_37_, v_canonical_boxed_42_, v___y_39_, v___y_40_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
return v_res_43_;
}
}
lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(lean_object* v___y_44_){
_start:
{
lean_object* v___x_46_; lean_object* v_env_47_; lean_object* v___x_48_; lean_object* v_mainModule_49_; lean_object* v___x_50_; 
v___x_46_ = lean_st_ref_get(v___y_44_);
v_env_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc_ref(v_env_47_);
lean_dec(v___x_46_);
v___x_48_ = l_Lean_Environment_header(v_env_47_);
lean_dec_ref(v_env_47_);
v_mainModule_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc(v_mainModule_49_);
lean_dec_ref(v___x_48_);
v___x_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_50_, 0, v_mainModule_49_);
return v___x_50_;
}
}
LEAN_EXPORT void l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_44_ = stack[0].m_obj;
lean_object* v_res_51_;
v_res_51_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_44_);
stack->m_obj
 = v_res_51_;
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg___boxed(lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_52_);
lean_dec(v___y_52_);
return v_res_54_;
}
}
lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1(lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_56_);
return v___x_58_;
}
}
LEAN_EXPORT void l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_55_ = stack[0].m_obj;
lean_object* v___y_56_ = stack[1].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1(v___y_55_, v___y_56_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___boxed(lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1(v___y_60_, v___y_61_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
return v_res_63_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_box(0);
v___x_65_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_66_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
return v___x_66_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg(){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0);
v___x_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_70_;
v_res_70_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
stack->m_obj
 = v_res_70_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___boxed(lean_object* v___y_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v_res_72_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(lean_object* v_00_u03b1_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_77_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_74_ = stack[1].m_obj;
lean_object* v___y_75_ = stack[2].m_obj;
lean_object* v_res_78_;
v_res_78_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(lean_box(0), v___y_74_, v___y_75_);
stack->m_obj
 = v_res_78_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___boxed(lean_object* v_00_u03b1_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(v_00_u03b1_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_83_;
}
}
lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0(lean_object* v_k_103_, lean_object* v_attrKind_104_, lean_object* v_attrs_x3f_105_, lean_object* v_kind_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
uint8_t v___x_110_; lean_object* v___x_111_; 
v___x_110_ = 0;
v___x_111_ = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(v_k_103_, v___x_110_, v___y_107_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_113_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_112_);
lean_dec_ref_known(v___x_111_, 1);
v___x_113_ = l_Lean_Elab_Command_getRef___redArg(v___y_107_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_150_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_150_ == 0)
{
v___x_116_ = v___x_113_;
v_isShared_117_ = v_isSharedCheck_150_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_113_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_150_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v___x_139_; 
v___x_118_ = l_Lean_SourceInfo_fromRef(v_a_114_, v___x_110_);
lean_dec(v_a_114_);
v___x_139_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_107_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_quotContext_x3f_140_; 
lean_dec_ref_known(v___x_139_, 1);
v_quotContext_x3f_140_ = lean_ctor_get(v___y_107_, 5);
if (lean_obj_tag(v_quotContext_x3f_140_) == 0)
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_108_);
lean_dec_ref(v___x_141_);
goto v___jp_119_;
}
else
{
goto v___jp_119_;
}
}
else
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
lean_dec(v___x_118_);
lean_del_object(v___x_116_);
lean_dec(v_a_112_);
lean_dec(v_kind_106_);
lean_dec(v_attrKind_104_);
v_a_142_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_139_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_139_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
v___jp_119_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_120_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4));
v___x_121_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7));
v___x_122_ = l_Lean_mkIdent(v_kind_106_);
v___x_123_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
lean_inc_n(v___x_118_, 2);
v___x_124_ = l_Lean_Syntax_node1(v___x_118_, v___x_123_, v_a_112_);
v___x_125_ = l_Lean_Syntax_node2(v___x_118_, v___x_121_, v___x_122_, v___x_124_);
v___x_126_ = l_Lean_Syntax_node2(v___x_118_, v___x_120_, v_attrKind_104_, v___x_125_);
if (lean_obj_tag(v_attrs_x3f_105_) == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = lean_mk_empty_array_with_capacity(v___x_127_);
v___x_129_ = lean_array_push(v___x_128_, v___x_126_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_129_);
v___x_131_ = v___x_116_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
else
{
lean_object* v_val_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v_val_133_ = lean_ctor_get(v_attrs_x3f_105_, 0);
v___x_134_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_133_);
v___x_135_ = lean_array_push(v___x_134_, v___x_126_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_135_);
v___x_137_ = v___x_116_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_dec(v_a_112_);
lean_dec(v_kind_106_);
lean_dec(v_attrKind_104_);
v_a_151_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_113_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_113_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
lean_dec(v_kind_106_);
lean_dec(v_attrKind_104_);
v_a_159_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_111_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_111_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_elabElabRulesAux___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_103_ = stack[0].m_obj;
lean_object* v_attrKind_104_ = stack[1].m_obj;
lean_object* v_attrs_x3f_105_ = stack[2].m_obj;
lean_object* v_kind_106_ = stack[3].m_obj;
lean_object* v___y_107_ = stack[4].m_obj;
lean_object* v___y_108_ = stack[5].m_obj;
lean_object* v_res_167_;
v_res_167_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_103_, v_attrKind_104_, v_attrs_x3f_105_, v_kind_106_, v___y_107_, v___y_108_);
stack->m_obj
 = v_res_167_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___boxed(lean_object* v_k_168_, lean_object* v_attrKind_169_, lean_object* v_attrs_x3f_170_, lean_object* v_kind_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_168_, v_attrKind_169_, v_attrs_x3f_170_, v_kind_171_, v___y_172_, v___y_173_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v_attrs_x3f_170_);
return v_res_175_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(lean_object* v_opts_176_, lean_object* v_opt_177_){
_start:
{
lean_object* v_name_178_; lean_object* v_defValue_179_; lean_object* v_map_180_; lean_object* v___x_181_; 
v_name_178_ = lean_ctor_get(v_opt_177_, 0);
v_defValue_179_ = lean_ctor_get(v_opt_177_, 1);
v_map_180_ = lean_ctor_get(v_opts_176_, 0);
v___x_181_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_180_, v_name_178_);
if (lean_obj_tag(v___x_181_) == 0)
{
uint8_t v___x_182_; 
v___x_182_ = lean_unbox(v_defValue_179_);
return v___x_182_;
}
else
{
lean_object* v_val_183_; 
v_val_183_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_val_183_);
lean_dec_ref_known(v___x_181_, 1);
if (lean_obj_tag(v_val_183_) == 1)
{
uint8_t v_v_184_; 
v_v_184_ = lean_ctor_get_uint8(v_val_183_, 0);
lean_dec_ref_known(v_val_183_, 0);
return v_v_184_;
}
else
{
uint8_t v___x_185_; 
lean_dec(v_val_183_);
v___x_185_ = lean_unbox(v_defValue_179_);
return v___x_185_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_176_ = stack[0].m_obj;
lean_object* v_opt_177_ = stack[1].m_obj;
uint8_t v_res_186_;
v_res_186_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(v_opts_176_, v_opt_177_);
stack->m_num = v_res_186_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8___boxed(lean_object* v_opts_187_, lean_object* v_opt_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(v_opts_187_, v_opt_188_);
lean_dec_ref(v_opt_188_);
lean_dec_ref(v_opts_187_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_box(1);
v___x_192_ = l_Lean_MessageData_ofFormat(v___x_191_);
return v___x_192_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2));
v___x_197_ = l_Lean_MessageData_ofFormat(v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(lean_object* v_x_198_, lean_object* v_x_199_){
_start:
{
if (lean_obj_tag(v_x_199_) == 0)
{
return v_x_198_;
}
else
{
lean_object* v_head_200_; lean_object* v_tail_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_223_; 
v_head_200_ = lean_ctor_get(v_x_199_, 0);
v_tail_201_ = lean_ctor_get(v_x_199_, 1);
v_isSharedCheck_223_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_223_ == 0)
{
v___x_203_ = v_x_199_;
v_isShared_204_ = v_isSharedCheck_223_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_tail_201_);
lean_inc(v_head_200_);
lean_dec(v_x_199_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_223_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v_before_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_221_; 
v_before_205_ = lean_ctor_get(v_head_200_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v_head_200_);
if (v_isSharedCheck_221_ == 0)
{
lean_object* v_unused_222_; 
v_unused_222_ = lean_ctor_get(v_head_200_, 1);
lean_dec(v_unused_222_);
v___x_207_ = v_head_200_;
v_isShared_208_ = v_isSharedCheck_221_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_before_205_);
lean_dec(v_head_200_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_221_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_209_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_208_ == 0)
{
lean_ctor_set_tag(v___x_207_, 7);
lean_ctor_set(v___x_207_, 1, v___x_209_);
lean_ctor_set(v___x_207_, 0, v_x_198_);
v___x_211_ = v___x_207_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_x_198_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_209_);
v___x_211_ = v_reuseFailAlloc_220_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_212_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3);
if (v_isShared_204_ == 0)
{
lean_ctor_set_tag(v___x_203_, 7);
lean_ctor_set(v___x_203_, 1, v___x_212_);
lean_ctor_set(v___x_203_, 0, v___x_211_);
v___x_214_ = v___x_203_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v___x_212_);
v___x_214_ = v_reuseFailAlloc_219_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = l_Lean_MessageData_ofSyntax(v_before_205_);
v___x_216_ = l_Lean_indentD(v___x_215_);
v___x_217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_214_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v_x_198_ = v___x_217_;
v_x_199_ = v_tail_201_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1));
v___x_228_ = l_Lean_MessageData_ofFormat(v___x_227_);
return v___x_228_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(lean_object* v_msgData_229_, lean_object* v_macroStack_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_scopes_235_; lean_object* v___x_236_; lean_object* v_opts_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_233_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_234_ = lean_st_ref_get(v___y_231_);
v_scopes_235_ = lean_ctor_get(v___x_234_, 2);
lean_inc(v_scopes_235_);
lean_dec(v___x_234_);
v___x_236_ = l_List_head_x21___redArg(v___x_233_, v_scopes_235_);
lean_dec(v_scopes_235_);
v_opts_237_ = lean_ctor_get(v___x_236_, 1);
lean_inc_ref(v_opts_237_);
lean_dec(v___x_236_);
v___x_238_ = l_Lean_Elab_pp_macroStack;
v___x_239_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(v_opts_237_, v___x_238_);
lean_dec_ref(v_opts_237_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; 
lean_dec(v_macroStack_230_);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v_msgData_229_);
return v___x_240_;
}
else
{
if (lean_obj_tag(v_macroStack_230_) == 0)
{
lean_object* v___x_241_; 
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v_msgData_229_);
return v___x_241_;
}
else
{
lean_object* v_head_242_; lean_object* v_after_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_258_; 
v_head_242_ = lean_ctor_get(v_macroStack_230_, 0);
lean_inc(v_head_242_);
v_after_243_ = lean_ctor_get(v_head_242_, 1);
v_isSharedCheck_258_ = !lean_is_exclusive(v_head_242_);
if (v_isSharedCheck_258_ == 0)
{
lean_object* v_unused_259_; 
v_unused_259_ = lean_ctor_get(v_head_242_, 0);
lean_dec(v_unused_259_);
v___x_245_ = v_head_242_;
v_isShared_246_ = v_isSharedCheck_258_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_after_243_);
lean_dec(v_head_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_258_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_246_ == 0)
{
lean_ctor_set_tag(v___x_245_, 7);
lean_ctor_set(v___x_245_, 1, v___x_247_);
lean_ctor_set(v___x_245_, 0, v_msgData_229_);
v___x_249_ = v___x_245_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_msgData_229_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v___x_247_);
v___x_249_ = v_reuseFailAlloc_257_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v_msgData_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_250_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2);
v___x_251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = l_Lean_MessageData_ofSyntax(v_after_243_);
v___x_253_ = l_Lean_indentD(v___x_252_);
v_msgData_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_254_, 0, v___x_251_);
lean_ctor_set(v_msgData_254_, 1, v___x_253_);
v___x_255_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(v_msgData_254_, v_macroStack_230_);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_229_ = stack[0].m_obj;
lean_object* v_macroStack_230_ = stack[1].m_obj;
lean_object* v___y_231_ = stack[2].m_obj;
lean_object* v_res_260_;
v_res_260_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_msgData_229_, v_macroStack_230_, v___y_231_);
stack->m_obj
 = v_res_260_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___boxed(lean_object* v_msgData_261_, lean_object* v_macroStack_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_msgData_261_, v_macroStack_262_, v___y_263_);
lean_dec(v___y_263_);
return v_res_265_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_266_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_269_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_270_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
lean_ctor_set(v___x_272_, 2, v___x_271_);
lean_ctor_set(v___x_272_, 3, v___x_271_);
lean_ctor_set(v___x_272_, 4, v___x_270_);
lean_ctor_set(v___x_272_, 5, v___x_270_);
lean_ctor_set(v___x_272_, 6, v___x_270_);
lean_ctor_set(v___x_272_, 7, v___x_270_);
lean_ctor_set(v___x_272_, 8, v___x_270_);
lean_ctor_set(v___x_272_, 9, v___x_270_);
lean_ctor_set(v___x_272_, 10, v___x_270_);
lean_ctor_set(v___x_272_, 11, v___x_269_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_unsigned_to_nat(32u);
v___x_274_ = lean_mk_empty_array_with_capacity(v___x_273_);
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_276_ = ((size_t)5ULL);
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_unsigned_to_nat(32u);
v___x_279_ = lean_mk_empty_array_with_capacity(v___x_278_);
v___x_280_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3);
v___x_281_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v___x_279_);
lean_ctor_set(v___x_281_, 2, v___x_277_);
lean_ctor_set(v___x_281_, 3, v___x_277_);
lean_ctor_set_usize(v___x_281_, 4, v___x_276_);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_282_ = lean_box(1);
v___x_283_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4);
v___x_284_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1);
v___x_285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
lean_ctor_set(v___x_285_, 2, v___x_282_);
return v___x_285_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(lean_object* v_msgData_286_, lean_object* v___y_287_){
_start:
{
lean_object* v___x_289_; lean_object* v_env_290_; uint8_t v___x_291_; lean_object* v_env_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v_scopes_295_; lean_object* v___x_296_; lean_object* v_opts_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_289_ = lean_st_ref_get(v___y_287_);
v_env_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc_ref(v_env_290_);
lean_dec(v___x_289_);
v___x_291_ = 0;
v_env_292_ = l_Lean_Environment_setRecordingDeps(v_env_290_, v___x_291_);
v___x_293_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_294_ = lean_st_ref_get(v___y_287_);
v_scopes_295_ = lean_ctor_get(v___x_294_, 2);
lean_inc(v_scopes_295_);
lean_dec(v___x_294_);
v___x_296_ = l_List_head_x21___redArg(v___x_293_, v_scopes_295_);
lean_dec(v_scopes_295_);
v_opts_297_ = lean_ctor_get(v___x_296_, 1);
lean_inc_ref(v_opts_297_);
lean_dec(v___x_296_);
v___x_298_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2);
v___x_299_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5);
v___x_300_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_300_, 0, v_env_292_);
lean_ctor_set(v___x_300_, 1, v___x_298_);
lean_ctor_set(v___x_300_, 2, v___x_299_);
lean_ctor_set(v___x_300_, 3, v_opts_297_);
v___x_301_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v_msgData_286_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_286_ = stack[0].m_obj;
lean_object* v___y_287_ = stack[1].m_obj;
lean_object* v_res_303_;
v_res_303_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msgData_286_, v___y_287_);
stack->m_obj
 = v_res_303_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___boxed(lean_object* v_msgData_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msgData_304_, v___y_305_);
lean_dec(v___y_305_);
return v_res_307_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(lean_object* v_msg_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_Elab_Command_getRef___redArg(v___y_309_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v_macroStack_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v_a_317_; lean_object* v___x_318_; lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_327_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref_known(v___x_312_, 1);
v_macroStack_314_ = lean_ctor_get(v___y_309_, 4);
v___x_315_ = l_Lean_Elab_getBetterRef(v_a_313_, v_macroStack_314_);
lean_dec(v_a_313_);
v___x_316_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msg_308_, v___y_310_);
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
lean_dec_ref(v___x_316_);
lean_inc(v_macroStack_314_);
v___x_318_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_a_317_, v_macroStack_314_, v___y_310_);
v_a_319_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_327_ == 0)
{
v___x_321_ = v___x_318_;
v_isShared_322_ = v_isSharedCheck_327_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_318_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_327_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_315_);
lean_ctor_set(v___x_323_, 1, v_a_319_);
if (v_isShared_322_ == 0)
{
lean_ctor_set_tag(v___x_321_, 1);
lean_ctor_set(v___x_321_, 0, v___x_323_);
v___x_325_ = v___x_321_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec_ref(v_msg_308_);
v_a_328_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_312_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_312_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_308_ = stack[0].m_obj;
lean_object* v___y_309_ = stack[1].m_obj;
lean_object* v___y_310_ = stack[2].m_obj;
lean_object* v_res_336_;
v_res_336_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_308_, v___y_309_, v___y_310_);
stack->m_obj
 = v_res_336_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg___boxed(lean_object* v_msg_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_341_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(lean_object* v_ref_342_, lean_object* v_msg_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_Elab_Command_getRef___redArg(v___y_344_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v_fileName_349_; lean_object* v_fileMap_350_; lean_object* v_currRecDepth_351_; lean_object* v_cmdPos_352_; lean_object* v_macroStack_353_; lean_object* v_quotContext_x3f_354_; lean_object* v_currMacroScope_355_; lean_object* v_snap_x3f_356_; lean_object* v_cancelTk_x3f_357_; uint8_t v_suppressElabErrors_358_; lean_object* v_ref_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
v_fileName_349_ = lean_ctor_get(v___y_344_, 0);
v_fileMap_350_ = lean_ctor_get(v___y_344_, 1);
v_currRecDepth_351_ = lean_ctor_get(v___y_344_, 2);
v_cmdPos_352_ = lean_ctor_get(v___y_344_, 3);
v_macroStack_353_ = lean_ctor_get(v___y_344_, 4);
v_quotContext_x3f_354_ = lean_ctor_get(v___y_344_, 5);
v_currMacroScope_355_ = lean_ctor_get(v___y_344_, 6);
v_snap_x3f_356_ = lean_ctor_get(v___y_344_, 8);
v_cancelTk_x3f_357_ = lean_ctor_get(v___y_344_, 9);
v_suppressElabErrors_358_ = lean_ctor_get_uint8(v___y_344_, sizeof(void*)*10);
v_ref_359_ = l_Lean_replaceRef(v_ref_342_, v_a_348_);
lean_dec(v_a_348_);
lean_inc(v_cancelTk_x3f_357_);
lean_inc(v_snap_x3f_356_);
lean_inc(v_currMacroScope_355_);
lean_inc(v_quotContext_x3f_354_);
lean_inc(v_macroStack_353_);
lean_inc(v_cmdPos_352_);
lean_inc(v_currRecDepth_351_);
lean_inc_ref(v_fileMap_350_);
lean_inc_ref(v_fileName_349_);
v___x_360_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_360_, 0, v_fileName_349_);
lean_ctor_set(v___x_360_, 1, v_fileMap_350_);
lean_ctor_set(v___x_360_, 2, v_currRecDepth_351_);
lean_ctor_set(v___x_360_, 3, v_cmdPos_352_);
lean_ctor_set(v___x_360_, 4, v_macroStack_353_);
lean_ctor_set(v___x_360_, 5, v_quotContext_x3f_354_);
lean_ctor_set(v___x_360_, 6, v_currMacroScope_355_);
lean_ctor_set(v___x_360_, 7, v_ref_359_);
lean_ctor_set(v___x_360_, 8, v_snap_x3f_356_);
lean_ctor_set(v___x_360_, 9, v_cancelTk_x3f_357_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*10, v_suppressElabErrors_358_);
v___x_361_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_343_, v___x_360_, v___y_345_);
lean_dec_ref_known(v___x_360_, 10);
return v___x_361_;
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec_ref(v_msg_343_);
v_a_362_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_347_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_347_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_342_ = stack[0].m_obj;
lean_object* v_msg_343_ = stack[1].m_obj;
lean_object* v___y_344_ = stack[2].m_obj;
lean_object* v___y_345_ = stack[3].m_obj;
lean_object* v_res_370_;
v_res_370_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_342_, v_msg_343_, v___y_344_, v___y_345_);
stack->m_obj
 = v_res_370_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(lean_object* v_ref_371_, lean_object* v_msg_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_371_, v_msg_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v_ref_371_);
return v_res_376_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(lean_object* v_k_380_, lean_object* v_as_381_, size_t v_sz_382_, size_t v_i_383_, lean_object* v_b_384_){
_start:
{
uint8_t v___x_385_; 
v___x_385_ = lean_usize_dec_lt(v_i_383_, v_sz_382_);
if (v___x_385_ == 0)
{
lean_dec(v_k_380_);
lean_inc_ref(v_b_384_);
return v_b_384_;
}
else
{
lean_object* v___x_386_; lean_object* v_a_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_386_ = lean_box(0);
v_a_387_ = lean_array_uget_borrowed(v_as_381_, v_i_383_);
lean_inc(v_a_387_);
v___x_388_ = l_Lean_Syntax_getKind(v_a_387_);
lean_inc(v_k_380_);
v___x_389_ = l_Lean_Elab_Command_checkRuleKind(v___x_388_, v_k_380_);
lean_dec(v___x_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; size_t v___x_391_; size_t v___x_392_; 
v___x_390_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0));
v___x_391_ = ((size_t)1ULL);
v___x_392_ = lean_usize_add(v_i_383_, v___x_391_);
v_i_383_ = v___x_392_;
v_b_384_ = v___x_390_;
goto _start;
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
lean_dec(v_k_380_);
lean_inc(v_a_387_);
v___x_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_394_, 0, v_a_387_);
v___x_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___x_386_);
return v___x_396_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_380_ = stack[0].m_obj;
lean_object* v_as_381_ = stack[1].m_obj;
size_t v_sz_382_ = stack[2].m_num;
size_t v_i_383_ = stack[3].m_num;
lean_object* v_b_384_ = stack[4].m_obj;
lean_object* v_res_397_;
v_res_397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_k_380_, v_as_381_, v_sz_382_, v_i_383_, v_b_384_);
stack->m_obj
 = v_res_397_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(lean_object* v_k_398_, lean_object* v_as_399_, lean_object* v_sz_400_, lean_object* v_i_401_, lean_object* v_b_402_){
_start:
{
size_t v_sz_boxed_403_; size_t v_i_boxed_404_; lean_object* v_res_405_; 
v_sz_boxed_403_ = lean_unbox_usize(v_sz_400_);
lean_dec(v_sz_400_);
v_i_boxed_404_ = lean_unbox_usize(v_i_401_);
lean_dec(v_i_401_);
v_res_405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_k_398_, v_as_399_, v_sz_boxed_403_, v_i_boxed_404_, v_b_402_);
lean_dec_ref(v_b_402_);
lean_dec_ref(v_as_399_);
return v_res_405_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0));
v___x_408_ = l_Lean_stringToMessageData(v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2));
v___x_411_ = l_Lean_stringToMessageData(v___x_410_);
return v___x_411_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7(void){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Array_mkArray0___redArg();
return v___x_419_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11));
v___x_426_ = l_Lean_stringToMessageData(v___x_425_);
return v___x_426_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(lean_object* v_k_427_, size_t v_sz_428_, size_t v_i_429_, lean_object* v_bs_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
uint8_t v___x_434_; 
v___x_434_ = lean_usize_dec_lt(v_i_429_, v_sz_428_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
lean_dec(v_k_427_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v_bs_430_);
return v___x_435_;
}
else
{
lean_object* v_v_436_; lean_object* v___x_437_; lean_object* v_bs_x27_438_; lean_object* v_a_440_; lean_object* v___y_446_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___x_465_; uint8_t v___x_466_; 
v_v_436_ = lean_array_uget(v_bs_430_, v_i_429_);
v___x_437_ = lean_unsigned_to_nat(0u);
v_bs_x27_438_ = lean_array_uset(v_bs_430_, v_i_429_, v___x_437_);
v___x_465_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5));
lean_inc(v_v_436_);
v___x_466_ = l_Lean_Syntax_isOfKind(v_v_436_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
lean_dec(v_v_436_);
v___x_467_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
v___y_446_ = v___x_467_;
goto v___jp_445_;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = l_Lean_Syntax_getArg(v_v_436_, v___x_468_);
lean_inc(v___x_469_);
v___x_470_ = l_Lean_Syntax_matchesNull(v___x_469_, v___x_468_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; 
lean_dec(v___x_469_);
lean_dec(v_v_436_);
v___x_471_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
v___y_446_ = v___x_471_;
goto v___jp_445_;
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___x_489_; lean_object* v_pat_490_; lean_object* v___y_492_; lean_object* v___y_493_; uint8_t v___x_545_; 
v___x_472_ = lean_box(0);
v___x_473_ = l_Lean_Syntax_getArg(v___x_469_, v___x_437_);
lean_dec(v___x_469_);
v___x_474_ = lean_unsigned_to_nat(3u);
v___x_475_ = l_Lean_Syntax_getArg(v_v_436_, v___x_474_);
v___x_489_ = l_Lean_Syntax_getArgs(v___x_473_);
lean_dec(v___x_473_);
v_pat_490_ = lean_array_get_borrowed(v___x_472_, v___x_489_, v___x_437_);
v___x_545_ = l_Lean_Syntax_isQuot(v_pat_490_);
if (v___x_545_ == 0)
{
if (v___x_470_ == 0)
{
v___y_492_ = v___y_431_;
v___y_493_ = v___y_432_;
goto v___jp_491_;
}
else
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
if (lean_obj_tag(v___x_546_) == 0)
{
lean_dec_ref_known(v___x_546_, 1);
v___y_492_ = v___y_431_;
v___y_493_ = v___y_432_;
goto v___jp_491_;
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec_ref(v___x_489_);
lean_dec(v___x_475_);
lean_dec_ref(v_bs_x27_438_);
lean_dec(v_v_436_);
lean_dec(v_k_427_);
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
else
{
v___y_492_ = v___y_431_;
v___y_493_ = v___y_432_;
goto v___jp_491_;
}
v___jp_476_:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_479_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc_n(v___y_478_, 4);
v___x_480_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_480_, 0, v___y_478_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v___x_481_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_482_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
v___x_483_ = l_Array_append___redArg(v___x_482_, v___y_477_);
lean_dec_ref(v___y_477_);
v___x_484_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_484_, 0, v___y_478_);
lean_ctor_set(v___x_484_, 1, v___x_481_);
lean_ctor_set(v___x_484_, 2, v___x_483_);
v___x_485_ = l_Lean_Syntax_node1(v___y_478_, v___x_481_, v___x_484_);
v___x_486_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_487_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_487_, 0, v___y_478_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = l_Lean_Syntax_node4(v___y_478_, v___x_465_, v___x_480_, v___x_485_, v___x_487_, v___x_475_);
v_a_440_ = v___x_488_;
goto v___jp_439_;
}
v___jp_491_:
{
lean_object* v_quoted_494_; lean_object* v_k_x27_495_; uint8_t v___x_496_; 
lean_inc(v_pat_490_);
v_quoted_494_ = l_Lean_Syntax_getQuotContent(v_pat_490_);
lean_inc(v_quoted_494_);
v_k_x27_495_ = l_Lean_Syntax_getKind(v_quoted_494_);
lean_inc(v_k_427_);
v___x_496_ = l_Lean_Elab_Command_checkRuleKind(v_k_x27_495_, v_k_427_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10));
v___x_498_ = lean_name_eq(v_k_x27_495_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec(v_quoted_494_);
lean_dec_ref(v___x_489_);
lean_dec(v___x_475_);
v___x_499_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12);
v___x_500_ = l_Lean_MessageData_ofName(v_k_x27_495_);
v___x_501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_501_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v___x_504_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_v_436_, v___x_503_, v___y_492_, v___y_493_);
lean_dec(v_v_436_);
v___y_446_ = v___x_504_;
goto v___jp_445_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; size_t v_sz_507_; size_t v___x_508_; lean_object* v___x_509_; lean_object* v_fst_510_; 
lean_dec(v_k_x27_495_);
v___x_505_ = l_Lean_Syntax_getArgs(v_quoted_494_);
lean_dec(v_quoted_494_);
v___x_506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0));
v_sz_507_ = lean_array_size(v___x_505_);
v___x_508_ = ((size_t)0ULL);
lean_inc(v_k_427_);
v___x_509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_k_427_, v___x_505_, v_sz_507_, v___x_508_, v___x_506_);
lean_dec_ref(v___x_505_);
v_fst_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_fst_510_);
lean_dec_ref(v___x_509_);
if (lean_obj_tag(v_fst_510_) == 0)
{
lean_dec_ref(v___x_489_);
lean_dec(v___x_475_);
v___y_457_ = v___y_492_;
v___y_458_ = v___y_493_;
goto v___jp_456_;
}
else
{
lean_object* v_val_511_; 
v_val_511_ = lean_ctor_get(v_fst_510_, 0);
lean_inc(v_val_511_);
lean_dec_ref_known(v_fst_510_, 1);
if (lean_obj_tag(v_val_511_) == 0)
{
lean_dec_ref(v___x_489_);
lean_dec(v___x_475_);
v___y_457_ = v___y_492_;
v___y_458_ = v___y_493_;
goto v___jp_456_;
}
else
{
lean_object* v_val_512_; lean_object* v_pat_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec(v_v_436_);
v_val_512_ = lean_ctor_get(v_val_511_, 0);
lean_inc(v_val_512_);
lean_dec_ref_known(v_val_511_, 1);
lean_inc(v_pat_490_);
v_pat_513_ = l_Lean_Syntax_setArg(v_pat_490_, v___x_468_, v_val_512_);
v___x_514_ = lean_array_set(v___x_489_, v___x_437_, v_pat_513_);
v___x_515_ = l_Lean_Elab_Command_getRef___redArg(v___y_492_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_515_, 1);
v___x_517_ = l_Lean_SourceInfo_fromRef(v_a_516_, v___x_496_);
lean_dec(v_a_516_);
v___x_518_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_492_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_quotContext_x3f_519_; 
lean_dec_ref_known(v___x_518_, 1);
v_quotContext_x3f_519_ = lean_ctor_get(v___y_492_, 5);
if (lean_obj_tag(v_quotContext_x3f_519_) == 0)
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_493_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_dec_ref_known(v___x_520_, 1);
v___y_477_ = v___x_514_;
v___y_478_ = v___x_517_;
goto v___jp_476_;
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_dec(v___x_517_);
lean_dec_ref(v___x_514_);
lean_dec(v___x_475_);
lean_dec_ref(v_bs_x27_438_);
lean_dec(v_k_427_);
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
v___y_477_ = v___x_514_;
v___y_478_ = v___x_517_;
goto v___jp_476_;
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec(v___x_517_);
lean_dec_ref(v___x_514_);
lean_dec(v___x_475_);
lean_dec_ref(v_bs_x27_438_);
lean_dec(v_k_427_);
v_a_529_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_518_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_518_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec_ref(v___x_514_);
lean_dec(v___x_475_);
lean_dec_ref(v_bs_x27_438_);
lean_dec(v_k_427_);
v_a_537_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_515_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_515_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_x27_495_);
lean_dec(v_quoted_494_);
lean_dec_ref(v___x_489_);
lean_dec(v___x_475_);
v_a_440_ = v_v_436_;
goto v___jp_439_;
}
}
}
}
v___jp_439_:
{
size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; 
v___x_441_ = ((size_t)1ULL);
v___x_442_ = lean_usize_add(v_i_429_, v___x_441_);
v___x_443_ = lean_array_uset(v_bs_x27_438_, v_i_429_, v_a_440_);
v_i_429_ = v___x_442_;
v_bs_430_ = v___x_443_;
goto _start;
}
v___jp_445_:
{
if (lean_obj_tag(v___y_446_) == 0)
{
lean_object* v_a_447_; 
v_a_447_ = lean_ctor_get(v___y_446_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v___y_446_, 1);
v_a_440_ = v_a_447_;
goto v___jp_439_;
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec_ref(v_bs_x27_438_);
lean_dec(v_k_427_);
v_a_448_ = lean_ctor_get(v___y_446_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___y_446_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___y_446_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___y_446_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
v___jp_456_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_459_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1);
lean_inc(v_k_427_);
v___x_460_ = l_Lean_MessageData_ofName(v_k_427_);
v___x_461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_v_436_, v___x_463_, v___y_457_, v___y_458_);
lean_dec(v_v_436_);
v___y_446_ = v___x_464_;
goto v___jp_445_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_427_ = stack[0].m_obj;
size_t v_sz_428_ = stack[1].m_num;
size_t v_i_429_ = stack[2].m_num;
lean_object* v_bs_430_ = stack[3].m_obj;
lean_object* v___y_431_ = stack[4].m_obj;
lean_object* v___y_432_ = stack[5].m_obj;
lean_object* v_res_555_;
v_res_555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(v_k_427_, v_sz_428_, v_i_429_, v_bs_430_, v___y_431_, v___y_432_);
stack->m_obj
 = v_res_555_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___boxed(lean_object* v_k_556_, lean_object* v_sz_557_, lean_object* v_i_558_, lean_object* v_bs_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
size_t v_sz_boxed_563_; size_t v_i_boxed_564_; lean_object* v_res_565_; 
v_sz_boxed_563_ = lean_unbox_usize(v_sz_557_);
lean_dec(v_sz_557_);
v_i_boxed_564_ = lean_unbox_usize(v_i_558_);
lean_dec(v_i_558_);
v_res_565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(v_k_556_, v_sz_boxed_563_, v_i_boxed_564_, v_bs_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
return v_res_565_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__4));
v___x_572_ = l_String_toRawSubstring_x27(v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__8));
v___x_578_ = l_String_toRawSubstring_x27(v___x_577_);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__15));
v___x_586_ = l_String_toRawSubstring_x27(v___x_585_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_599_ = l_String_toRawSubstring_x27(v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__35(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_614_ = l_String_toRawSubstring_x27(v___x_613_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__38(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___x_618_ = l_String_toRawSubstring_x27(v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__42(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__41));
v___x_624_ = l_String_toRawSubstring_x27(v___x_623_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__45(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__44));
v___x_628_ = l_String_toRawSubstring_x27(v___x_627_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__48(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__47));
v___x_632_ = l_String_toRawSubstring_x27(v___x_631_);
return v___x_632_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__51(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__50));
v___x_637_ = l_String_toRawSubstring_x27(v___x_636_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__58(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__57));
v___x_647_ = l_Lean_stringToMessageData(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__60(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__59));
v___x_650_ = l_Lean_stringToMessageData(v___x_649_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__72(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__71));
v___x_668_ = l_Lean_stringToMessageData(v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__75));
v___x_674_ = l_Lean_stringToMessageData(v___x_673_);
return v___x_674_;
}
}
lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object* v_doc_x3f_675_, lean_object* v_attrs_x3f_676_, lean_object* v_attrKind_677_, lean_object* v_k_678_, lean_object* v_cat_x3f_679_, lean_object* v_expty_x3f_680_, lean_object* v_alts_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
size_t v_sz_685_; size_t v___x_686_; lean_object* v___x_687_; 
v_sz_685_ = lean_array_size(v_alts_681_);
v___x_686_ = ((size_t)0ULL);
lean_inc(v_k_678_);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(v_k_678_, v_sz_685_, v___x_686_, v_alts_681_, v_a_682_, v_a_683_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_1704_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_1704_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_1704_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v_a_819_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v_a_971_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v_a_1084_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; uint8_t v___y_1099_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v_a_1255_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v_a_1369_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v_a_1502_; lean_object* v_catName_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; 
if (lean_obj_tag(v_cat_x3f_679_) == 1)
{
lean_object* v_val_1691_; lean_object* v___x_1692_; 
v_val_1691_ = lean_ctor_get(v_cat_x3f_679_, 0);
v___x_1692_ = l_Lean_TSyntax_getId(v_val_1691_);
v_catName_1513_ = v___x_1692_;
v___y_1514_ = v_a_682_;
v___y_1515_ = v_a_683_;
goto v___jp_1512_;
}
else
{
if (lean_obj_tag(v_expty_x3f_680_) == 1)
{
lean_object* v___x_1693_; 
v___x_1693_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v_catName_1513_ = v___x_1693_;
v___y_1514_ = v_a_682_;
v___y_1515_ = v_a_683_;
goto v___jp_1512_;
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_del_object(v___x_690_);
lean_dec(v_a_688_);
lean_dec(v_expty_x3f_680_);
lean_dec(v_k_678_);
lean_dec(v_attrKind_677_);
lean_dec(v_doc_x3f_675_);
v___x_1694_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__76, &l_Lean_Elab_Command_elabElabRulesAux___closed__76_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76);
v___x_1695_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v___x_1694_, v_a_682_, v_a_683_);
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1695_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1695_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
v___jp_692_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
lean_inc_ref_n(v___y_693_, 4);
v___x_706_ = l_Array_append___redArg(v___y_693_, v___y_705_);
lean_dec_ref(v___y_705_);
lean_inc_n(v___y_701_, 10);
lean_inc_n(v___y_697_, 35);
v___x_707_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_707_, 0, v___y_697_);
lean_ctor_set(v___x_707_, 1, v___y_701_);
lean_ctor_set(v___x_707_, 2, v___x_706_);
v___x_708_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_709_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_710_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_700_, 11);
v___x_711_ = l_Lean_Name_mkStr4(v___y_700_, v___x_708_, v___x_709_, v___x_710_);
v___x_712_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_713_, 0, v___y_697_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_715_ = l_Lean_Syntax_SepArray_ofElems(v___x_714_, v___y_694_);
lean_dec_ref(v___y_694_);
v___x_716_ = l_Array_append___redArg(v___y_693_, v___x_715_);
lean_dec_ref(v___x_715_);
v___x_717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_717_, 0, v___y_697_);
lean_ctor_set(v___x_717_, 1, v___y_701_);
lean_ctor_set(v___x_717_, 2, v___x_716_);
v___x_718_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_719_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_719_, 0, v___y_697_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = l_Lean_Syntax_node3(v___y_697_, v___x_711_, v___x_713_, v___x_717_, v___x_719_);
v___x_721_ = l_Lean_Syntax_node1(v___y_697_, v___y_701_, v___x_720_);
lean_inc_ref(v___y_702_);
v___x_722_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_722_, 0, v___y_697_);
lean_ctor_set(v___x_722_, 1, v___y_702_);
v___x_723_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_724_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_703_, 3);
lean_inc_n(v___y_698_, 3);
v___x_725_ = l_Lean_addMacroScope(v___y_698_, v___x_724_, v___y_703_);
v___x_726_ = lean_box(0);
v___x_727_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_727_, 0, v___y_697_);
lean_ctor_set(v___x_727_, 1, v___x_723_);
lean_ctor_set(v___x_727_, 2, v___x_725_);
lean_ctor_set(v___x_727_, 3, v___x_726_);
v___x_728_ = l_Lean_mkIdent(v_k_678_);
v___x_729_ = l_Lean_Syntax_node2(v___y_697_, v___y_701_, v___x_727_, v___x_728_);
v___x_730_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_731_, 0, v___y_697_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_733_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
v___x_734_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc_ref_n(v___y_704_, 2);
v___x_735_ = l_Lean_Name_mkStr4(v___y_700_, v___y_704_, v___x_733_, v___x_734_);
lean_inc(v___x_735_);
v___x_736_ = l_Lean_addMacroScope(v___y_698_, v___x_735_, v___y_703_);
v___x_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set(v___x_737_, 1, v___x_726_);
v___x_738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v___x_726_);
v___x_739_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_739_, 0, v___y_697_);
lean_ctor_set(v___x_739_, 1, v___x_732_);
lean_ctor_set(v___x_739_, 2, v___x_736_);
lean_ctor_set(v___x_739_, 3, v___x_738_);
v___x_740_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_741_, 0, v___y_697_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_743_ = l_Lean_Name_mkStr4(v___y_700_, v___x_708_, v___x_709_, v___x_742_);
v___x_744_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_744_, 0, v___y_697_);
lean_ctor_set(v___x_744_, 1, v___x_742_);
v___x_745_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_746_ = l_Lean_Name_mkStr4(v___y_700_, v___x_708_, v___x_709_, v___x_745_);
v___x_747_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_748_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_749_ = l_Lean_addMacroScope(v___y_698_, v___x_748_, v___y_703_);
v___x_750_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_750_, 0, v___y_697_);
lean_ctor_set(v___x_750_, 1, v___x_747_);
lean_ctor_set(v___x_750_, 2, v___x_749_);
lean_ctor_set(v___x_750_, 3, v___x_726_);
lean_inc_ref(v___x_750_);
v___x_751_ = l_Lean_Syntax_node2(v___y_697_, v___y_701_, v___x_750_, v___y_699_);
v___x_752_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_752_, 0, v___y_697_);
lean_ctor_set(v___x_752_, 1, v___y_701_);
lean_ctor_set(v___x_752_, 2, v___y_693_);
v___x_753_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_754_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_754_, 0, v___y_697_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_756_ = l_Lean_Name_mkStr4(v___y_700_, v___x_708_, v___x_709_, v___x_755_);
v___x_757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_757_, 0, v___y_697_);
lean_ctor_set(v___x_757_, 1, v___x_755_);
v___x_758_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_759_ = l_Lean_Name_mkStr4(v___y_700_, v___x_708_, v___x_709_, v___x_758_);
lean_inc_ref_n(v___x_752_, 3);
v___x_760_ = l_Lean_Syntax_node2(v___y_697_, v___x_759_, v___x_752_, v___x_750_);
v___x_761_ = l_Lean_Syntax_node1(v___y_697_, v___y_701_, v___x_760_);
v___x_762_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_763_, 0, v___y_697_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_765_ = l_Lean_Name_mkStr4(v___y_700_, v___x_708_, v___x_709_, v___x_764_);
v___x_766_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_767_ = l_Lean_Name_mkStr4(v___y_700_, v___x_708_, v___x_709_, v___x_766_);
v___x_768_ = l_Array_append___redArg(v___y_693_, v_a_688_);
lean_dec(v_a_688_);
v___x_769_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_770_, 0, v___y_697_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_772_ = l_Lean_Name_mkStr4(v___y_700_, v___x_708_, v___x_709_, v___x_771_);
v___x_773_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_774_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_774_, 0, v___y_697_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = l_Lean_Syntax_node1(v___y_697_, v___x_772_, v___x_774_);
v___x_776_ = l_Lean_Syntax_node1(v___y_697_, v___y_701_, v___x_775_);
v___x_777_ = l_Lean_Syntax_node1(v___y_697_, v___y_701_, v___x_776_);
v___x_778_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_779_ = l_Lean_Name_mkStr4(v___y_700_, v___x_708_, v___x_709_, v___x_778_);
v___x_780_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_781_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_781_, 0, v___y_697_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_783_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_784_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_785_ = l_Lean_addMacroScope(v___y_698_, v___x_784_, v___y_703_);
v___x_786_ = l_Lean_Name_mkStr3(v___y_700_, v___y_704_, v___x_782_);
v___x_787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
lean_ctor_set(v___x_787_, 1, v___x_726_);
v___x_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v___x_726_);
v___x_789_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_789_, 0, v___y_697_);
lean_ctor_set(v___x_789_, 1, v___x_783_);
lean_ctor_set(v___x_789_, 2, v___x_785_);
lean_ctor_set(v___x_789_, 3, v___x_788_);
v___x_790_ = l_Lean_Syntax_node2(v___y_697_, v___x_779_, v___x_781_, v___x_789_);
lean_inc_ref(v___x_754_);
v___x_791_ = l_Lean_Syntax_node4(v___y_697_, v___x_767_, v___x_770_, v___x_777_, v___x_754_, v___x_790_);
v___x_792_ = lean_array_push(v___x_768_, v___x_791_);
v___x_793_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_793_, 0, v___y_697_);
lean_ctor_set(v___x_793_, 1, v___y_701_);
lean_ctor_set(v___x_793_, 2, v___x_792_);
v___x_794_ = l_Lean_Syntax_node1(v___y_697_, v___x_765_, v___x_793_);
v___x_795_ = l_Lean_Syntax_node6(v___y_697_, v___x_756_, v___x_757_, v___x_752_, v___x_752_, v___x_761_, v___x_763_, v___x_794_);
v___x_796_ = l_Lean_Syntax_node4(v___y_697_, v___x_746_, v___x_751_, v___x_752_, v___x_754_, v___x_795_);
v___x_797_ = l_Lean_Syntax_node2(v___y_697_, v___x_743_, v___x_744_, v___x_796_);
v___x_798_ = lean_unsigned_to_nat(9u);
v___x_799_ = lean_mk_empty_array_with_capacity(v___x_798_);
v___x_800_ = lean_array_push(v___x_799_, v___x_707_);
v___x_801_ = lean_array_push(v___x_800_, v___x_721_);
v___x_802_ = lean_array_push(v___x_801_, v___y_696_);
v___x_803_ = lean_array_push(v___x_802_, v___x_722_);
v___x_804_ = lean_array_push(v___x_803_, v___x_729_);
v___x_805_ = lean_array_push(v___x_804_, v___x_731_);
v___x_806_ = lean_array_push(v___x_805_, v___x_739_);
v___x_807_ = lean_array_push(v___x_806_, v___x_741_);
v___x_808_ = lean_array_push(v___x_807_, v___x_797_);
lean_inc(v___y_695_);
v___x_809_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_809_, 0, v___y_697_);
lean_ctor_set(v___x_809_, 1, v___y_695_);
lean_ctor_set(v___x_809_, 2, v___x_808_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_809_);
v___x_811_ = v___x_690_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
v___jp_813_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_820_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_821_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_822_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_823_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_824_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_825_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_675_) == 1)
{
lean_object* v_val_826_; lean_object* v___x_827_; 
v_val_826_ = lean_ctor_get(v_doc_x3f_675_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v_doc_x3f_675_, 1);
v___x_827_ = l_Array_mkArray1___redArg(v_val_826_);
v___y_693_ = v___x_825_;
v___y_694_ = v___y_815_;
v___y_695_ = v___x_823_;
v___y_696_ = v___y_817_;
v___y_697_ = v___y_814_;
v___y_698_ = v_a_819_;
v___y_699_ = v___y_816_;
v___y_700_ = v___x_820_;
v___y_701_ = v___x_824_;
v___y_702_ = v___x_822_;
v___y_703_ = v___y_818_;
v___y_704_ = v___x_821_;
v___y_705_ = v___x_827_;
goto v___jp_692_;
}
else
{
lean_object* v___x_828_; 
lean_dec(v_doc_x3f_675_);
v___x_828_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_693_ = v___x_825_;
v___y_694_ = v___y_815_;
v___y_695_ = v___x_823_;
v___y_696_ = v___y_817_;
v___y_697_ = v___y_814_;
v___y_698_ = v_a_819_;
v___y_699_ = v___y_816_;
v___y_700_ = v___x_820_;
v___y_701_ = v___x_824_;
v___y_702_ = v___x_822_;
v___y_703_ = v___y_818_;
v___y_704_ = v___x_821_;
v___y_705_ = v___x_828_;
goto v___jp_692_;
}
}
v___jp_829_:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
lean_inc_ref_n(v___y_839_, 4);
v___x_843_ = l_Array_append___redArg(v___y_839_, v___y_842_);
lean_dec_ref(v___y_842_);
lean_inc_n(v___y_840_, 12);
lean_inc_n(v___y_831_, 42);
v___x_844_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_844_, 0, v___y_831_);
lean_ctor_set(v___x_844_, 1, v___y_840_);
lean_ctor_set(v___x_844_, 2, v___x_843_);
v___x_845_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_846_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_847_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_836_, 13);
v___x_848_ = l_Lean_Name_mkStr4(v___y_836_, v___x_845_, v___x_846_, v___x_847_);
v___x_849_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_850_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_850_, 0, v___y_831_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_852_ = l_Lean_Syntax_SepArray_ofElems(v___x_851_, v___y_834_);
lean_dec_ref(v___y_834_);
v___x_853_ = l_Array_append___redArg(v___y_839_, v___x_852_);
lean_dec_ref(v___x_852_);
v___x_854_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_854_, 0, v___y_831_);
lean_ctor_set(v___x_854_, 1, v___y_840_);
lean_ctor_set(v___x_854_, 2, v___x_853_);
v___x_855_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_856_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_856_, 0, v___y_831_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = l_Lean_Syntax_node3(v___y_831_, v___x_848_, v___x_850_, v___x_854_, v___x_856_);
v___x_858_ = l_Lean_Syntax_node1(v___y_831_, v___y_840_, v___x_857_);
lean_inc_ref(v___y_835_);
v___x_859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_859_, 0, v___y_831_);
lean_ctor_set(v___x_859_, 1, v___y_835_);
v___x_860_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_861_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_841_, 5);
lean_inc_n(v___y_830_, 5);
v___x_862_ = l_Lean_addMacroScope(v___y_830_, v___x_861_, v___y_841_);
v___x_863_ = lean_box(0);
v___x_864_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_864_, 0, v___y_831_);
lean_ctor_set(v___x_864_, 1, v___x_860_);
lean_ctor_set(v___x_864_, 2, v___x_862_);
lean_ctor_set(v___x_864_, 3, v___x_863_);
v___x_865_ = l_Lean_mkIdent(v_k_678_);
v___x_866_ = l_Lean_Syntax_node2(v___y_831_, v___y_840_, v___x_864_, v___x_865_);
v___x_867_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_868_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_868_, 0, v___y_831_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__35, &l_Lean_Elab_Command_elabElabRulesAux___closed__35_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__35);
v___x_870_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__36));
lean_inc_ref_n(v___y_833_, 3);
v___x_871_ = l_Lean_Name_mkStr4(v___y_836_, v___y_833_, v___x_846_, v___x_870_);
lean_inc(v___x_871_);
v___x_872_ = l_Lean_addMacroScope(v___y_830_, v___x_871_, v___y_841_);
v___x_873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_863_);
v___x_874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
lean_ctor_set(v___x_874_, 1, v___x_863_);
v___x_875_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_875_, 0, v___y_831_);
lean_ctor_set(v___x_875_, 1, v___x_869_);
lean_ctor_set(v___x_875_, 2, v___x_872_);
lean_ctor_set(v___x_875_, 3, v___x_874_);
v___x_876_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_877_, 0, v___y_831_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_879_ = l_Lean_Name_mkStr4(v___y_836_, v___x_845_, v___x_846_, v___x_878_);
v___x_880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_880_, 0, v___y_831_);
lean_ctor_set(v___x_880_, 1, v___x_878_);
v___x_881_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_882_ = l_Lean_Name_mkStr4(v___y_836_, v___x_845_, v___x_846_, v___x_881_);
v___x_883_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_884_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_885_ = l_Lean_addMacroScope(v___y_830_, v___x_884_, v___y_841_);
v___x_886_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_886_, 0, v___y_831_);
lean_ctor_set(v___x_886_, 1, v___x_883_);
lean_ctor_set(v___x_886_, 2, v___x_885_);
lean_ctor_set(v___x_886_, 3, v___x_863_);
v___x_887_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__38, &l_Lean_Elab_Command_elabElabRulesAux___closed__38_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__38);
v___x_888_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__39));
v___x_889_ = l_Lean_addMacroScope(v___y_830_, v___x_888_, v___y_841_);
v___x_890_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_890_, 0, v___y_831_);
lean_ctor_set(v___x_890_, 1, v___x_887_);
lean_ctor_set(v___x_890_, 2, v___x_889_);
lean_ctor_set(v___x_890_, 3, v___x_863_);
lean_inc_ref(v___x_890_);
lean_inc_ref(v___x_886_);
v___x_891_ = l_Lean_Syntax_node2(v___y_831_, v___y_840_, v___x_886_, v___x_890_);
v___x_892_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_892_, 0, v___y_831_);
lean_ctor_set(v___x_892_, 1, v___y_840_);
lean_ctor_set(v___x_892_, 2, v___y_839_);
v___x_893_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_894_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_894_, 0, v___y_831_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__40));
v___x_896_ = l_Lean_Name_mkStr4(v___y_836_, v___x_845_, v___x_846_, v___x_895_);
v___x_897_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__42, &l_Lean_Elab_Command_elabElabRulesAux___closed__42_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__42);
v___x_898_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__43));
v___x_899_ = l_Lean_Name_mkStr4(v___y_836_, v___y_833_, v___x_846_, v___x_898_);
lean_inc(v___x_899_);
v___x_900_ = l_Lean_addMacroScope(v___y_830_, v___x_899_, v___y_841_);
v___x_901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_863_);
v___x_902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
lean_ctor_set(v___x_902_, 1, v___x_863_);
v___x_903_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_903_, 0, v___y_831_);
lean_ctor_set(v___x_903_, 1, v___x_897_);
lean_ctor_set(v___x_903_, 2, v___x_900_);
lean_ctor_set(v___x_903_, 3, v___x_902_);
v___x_904_ = l_Lean_Syntax_node1(v___y_831_, v___y_840_, v___y_837_);
v___x_905_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_906_ = l_Lean_Name_mkStr4(v___y_836_, v___x_845_, v___x_846_, v___x_905_);
v___x_907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_907_, 0, v___y_831_);
lean_ctor_set(v___x_907_, 1, v___x_905_);
v___x_908_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_909_ = l_Lean_Name_mkStr4(v___y_836_, v___x_845_, v___x_846_, v___x_908_);
lean_inc_ref_n(v___x_892_, 4);
v___x_910_ = l_Lean_Syntax_node2(v___y_831_, v___x_909_, v___x_892_, v___x_886_);
v___x_911_ = l_Lean_Syntax_node1(v___y_831_, v___y_840_, v___x_910_);
v___x_912_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_913_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_913_, 0, v___y_831_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_915_ = l_Lean_Name_mkStr4(v___y_836_, v___x_845_, v___x_846_, v___x_914_);
v___x_916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_917_ = l_Lean_Name_mkStr4(v___y_836_, v___x_845_, v___x_846_, v___x_916_);
v___x_918_ = l_Array_append___redArg(v___y_839_, v_a_688_);
lean_dec(v_a_688_);
v___x_919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_920_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_920_, 0, v___y_831_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_922_ = l_Lean_Name_mkStr4(v___y_836_, v___x_845_, v___x_846_, v___x_921_);
v___x_923_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_924_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_924_, 0, v___y_831_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l_Lean_Syntax_node1(v___y_831_, v___x_922_, v___x_924_);
v___x_926_ = l_Lean_Syntax_node1(v___y_831_, v___y_840_, v___x_925_);
v___x_927_ = l_Lean_Syntax_node1(v___y_831_, v___y_840_, v___x_926_);
v___x_928_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_929_ = l_Lean_Name_mkStr4(v___y_836_, v___x_845_, v___x_846_, v___x_928_);
v___x_930_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_931_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_931_, 0, v___y_831_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_933_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_934_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_935_ = l_Lean_addMacroScope(v___y_830_, v___x_934_, v___y_841_);
v___x_936_ = l_Lean_Name_mkStr3(v___y_836_, v___y_833_, v___x_932_);
v___x_937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_863_);
v___x_938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___x_863_);
v___x_939_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_939_, 0, v___y_831_);
lean_ctor_set(v___x_939_, 1, v___x_933_);
lean_ctor_set(v___x_939_, 2, v___x_935_);
lean_ctor_set(v___x_939_, 3, v___x_938_);
v___x_940_ = l_Lean_Syntax_node2(v___y_831_, v___x_929_, v___x_931_, v___x_939_);
lean_inc_ref_n(v___x_894_, 2);
v___x_941_ = l_Lean_Syntax_node4(v___y_831_, v___x_917_, v___x_920_, v___x_927_, v___x_894_, v___x_940_);
v___x_942_ = lean_array_push(v___x_918_, v___x_941_);
v___x_943_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_943_, 0, v___y_831_);
lean_ctor_set(v___x_943_, 1, v___y_840_);
lean_ctor_set(v___x_943_, 2, v___x_942_);
v___x_944_ = l_Lean_Syntax_node1(v___y_831_, v___x_915_, v___x_943_);
v___x_945_ = l_Lean_Syntax_node6(v___y_831_, v___x_906_, v___x_907_, v___x_892_, v___x_892_, v___x_911_, v___x_913_, v___x_944_);
lean_inc(v___x_882_);
v___x_946_ = l_Lean_Syntax_node4(v___y_831_, v___x_882_, v___x_904_, v___x_892_, v___x_894_, v___x_945_);
lean_inc_ref(v___x_880_);
lean_inc(v___x_879_);
v___x_947_ = l_Lean_Syntax_node2(v___y_831_, v___x_879_, v___x_880_, v___x_946_);
v___x_948_ = l_Lean_Syntax_node2(v___y_831_, v___y_840_, v___x_890_, v___x_947_);
v___x_949_ = l_Lean_Syntax_node2(v___y_831_, v___x_896_, v___x_903_, v___x_948_);
v___x_950_ = l_Lean_Syntax_node4(v___y_831_, v___x_882_, v___x_891_, v___x_892_, v___x_894_, v___x_949_);
v___x_951_ = l_Lean_Syntax_node2(v___y_831_, v___x_879_, v___x_880_, v___x_950_);
v___x_952_ = lean_unsigned_to_nat(9u);
v___x_953_ = lean_mk_empty_array_with_capacity(v___x_952_);
v___x_954_ = lean_array_push(v___x_953_, v___x_844_);
v___x_955_ = lean_array_push(v___x_954_, v___x_858_);
v___x_956_ = lean_array_push(v___x_955_, v___y_832_);
v___x_957_ = lean_array_push(v___x_956_, v___x_859_);
v___x_958_ = lean_array_push(v___x_957_, v___x_866_);
v___x_959_ = lean_array_push(v___x_958_, v___x_868_);
v___x_960_ = lean_array_push(v___x_959_, v___x_875_);
v___x_961_ = lean_array_push(v___x_960_, v___x_877_);
v___x_962_ = lean_array_push(v___x_961_, v___x_951_);
lean_inc(v___y_838_);
v___x_963_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_963_, 0, v___y_831_);
lean_ctor_set(v___x_963_, 1, v___y_838_);
lean_ctor_set(v___x_963_, 2, v___x_962_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
v___jp_965_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_972_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_973_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_974_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_975_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_976_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_977_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_675_) == 1)
{
lean_object* v_val_978_; lean_object* v___x_979_; 
v_val_978_ = lean_ctor_get(v_doc_x3f_675_, 0);
lean_inc(v_val_978_);
lean_dec_ref_known(v_doc_x3f_675_, 1);
v___x_979_ = l_Array_mkArray1___redArg(v_val_978_);
v___y_830_ = v_a_971_;
v___y_831_ = v___y_968_;
v___y_832_ = v___y_967_;
v___y_833_ = v___x_973_;
v___y_834_ = v___y_970_;
v___y_835_ = v___x_974_;
v___y_836_ = v___x_972_;
v___y_837_ = v___y_966_;
v___y_838_ = v___x_975_;
v___y_839_ = v___x_977_;
v___y_840_ = v___x_976_;
v___y_841_ = v___y_969_;
v___y_842_ = v___x_979_;
goto v___jp_829_;
}
else
{
lean_object* v___x_980_; 
lean_dec(v_doc_x3f_675_);
v___x_980_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_830_ = v_a_971_;
v___y_831_ = v___y_968_;
v___y_832_ = v___y_967_;
v___y_833_ = v___x_973_;
v___y_834_ = v___y_970_;
v___y_835_ = v___x_974_;
v___y_836_ = v___x_972_;
v___y_837_ = v___y_966_;
v___y_838_ = v___x_975_;
v___y_839_ = v___x_977_;
v___y_840_ = v___x_976_;
v___y_841_ = v___y_969_;
v___y_842_ = v___x_980_;
goto v___jp_829_;
}
}
v___jp_981_:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_inc_ref_n(v___y_986_, 3);
v___x_994_ = l_Array_append___redArg(v___y_986_, v___y_993_);
lean_dec_ref(v___y_993_);
lean_inc_n(v___y_990_, 7);
lean_inc_n(v___y_988_, 26);
v___x_995_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_995_, 0, v___y_988_);
lean_ctor_set(v___x_995_, 1, v___y_990_);
lean_ctor_set(v___x_995_, 2, v___x_994_);
v___x_996_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_997_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_998_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_985_, 8);
v___x_999_ = l_Lean_Name_mkStr4(v___y_985_, v___x_996_, v___x_997_, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___y_988_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1003_ = l_Lean_Syntax_SepArray_ofElems(v___x_1002_, v___y_989_);
lean_dec_ref(v___y_989_);
v___x_1004_ = l_Array_append___redArg(v___y_986_, v___x_1003_);
lean_dec_ref(v___x_1003_);
v___x_1005_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1005_, 0, v___y_988_);
lean_ctor_set(v___x_1005_, 1, v___y_990_);
lean_ctor_set(v___x_1005_, 2, v___x_1004_);
v___x_1006_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___y_988_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = l_Lean_Syntax_node3(v___y_988_, v___x_999_, v___x_1001_, v___x_1005_, v___x_1007_);
v___x_1009_ = l_Lean_Syntax_node1(v___y_988_, v___y_990_, v___x_1008_);
lean_inc_ref(v___y_992_);
v___x_1010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___y_988_);
lean_ctor_set(v___x_1010_, 1, v___y_992_);
v___x_1011_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1012_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_991_, 2);
lean_inc_n(v___y_987_, 2);
v___x_1013_ = l_Lean_addMacroScope(v___y_987_, v___x_1012_, v___y_991_);
v___x_1014_ = lean_box(0);
v___x_1015_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1015_, 0, v___y_988_);
lean_ctor_set(v___x_1015_, 1, v___x_1011_);
lean_ctor_set(v___x_1015_, 2, v___x_1013_);
lean_ctor_set(v___x_1015_, 3, v___x_1014_);
v___x_1016_ = l_Lean_mkIdent(v_k_678_);
v___x_1017_ = l_Lean_Syntax_node2(v___y_988_, v___y_990_, v___x_1015_, v___x_1016_);
v___x_1018_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1019_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___y_988_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__45, &l_Lean_Elab_Command_elabElabRulesAux___closed__45_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__45);
v___x_1021_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__46));
lean_inc_ref_n(v___y_983_, 2);
v___x_1022_ = l_Lean_Name_mkStr4(v___y_985_, v___y_983_, v___x_1021_, v___x_1021_);
lean_inc(v___x_1022_);
v___x_1023_ = l_Lean_addMacroScope(v___y_987_, v___x_1022_, v___y_991_);
v___x_1024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1014_);
v___x_1025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___x_1014_);
v___x_1026_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1026_, 0, v___y_988_);
lean_ctor_set(v___x_1026_, 1, v___x_1020_);
lean_ctor_set(v___x_1026_, 2, v___x_1023_);
lean_ctor_set(v___x_1026_, 3, v___x_1025_);
v___x_1027_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1028_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___y_988_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1030_ = l_Lean_Name_mkStr4(v___y_985_, v___x_996_, v___x_997_, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___y_988_);
lean_ctor_set(v___x_1031_, 1, v___x_1029_);
v___x_1032_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1033_ = l_Lean_Name_mkStr4(v___y_985_, v___x_996_, v___x_997_, v___x_1032_);
v___x_1034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1035_ = l_Lean_Name_mkStr4(v___y_985_, v___x_996_, v___x_997_, v___x_1034_);
v___x_1036_ = l_Array_append___redArg(v___y_986_, v_a_688_);
lean_dec(v_a_688_);
v___x_1037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1038_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___y_988_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1040_ = l_Lean_Name_mkStr4(v___y_985_, v___x_996_, v___x_997_, v___x_1039_);
v___x_1041_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___y_988_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = l_Lean_Syntax_node1(v___y_988_, v___x_1040_, v___x_1042_);
v___x_1044_ = l_Lean_Syntax_node1(v___y_988_, v___y_990_, v___x_1043_);
v___x_1045_ = l_Lean_Syntax_node1(v___y_988_, v___y_990_, v___x_1044_);
v___x_1046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1047_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___y_988_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1049_ = l_Lean_Name_mkStr4(v___y_985_, v___x_996_, v___x_997_, v___x_1048_);
v___x_1050_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1051_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___y_988_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1053_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_1054_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1055_ = l_Lean_addMacroScope(v___y_987_, v___x_1054_, v___y_991_);
v___x_1056_ = l_Lean_Name_mkStr3(v___y_985_, v___y_983_, v___x_1052_);
v___x_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v___x_1014_);
v___x_1058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v___x_1014_);
v___x_1059_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1059_, 0, v___y_988_);
lean_ctor_set(v___x_1059_, 1, v___x_1053_);
lean_ctor_set(v___x_1059_, 2, v___x_1055_);
lean_ctor_set(v___x_1059_, 3, v___x_1058_);
v___x_1060_ = l_Lean_Syntax_node2(v___y_988_, v___x_1049_, v___x_1051_, v___x_1059_);
v___x_1061_ = l_Lean_Syntax_node4(v___y_988_, v___x_1035_, v___x_1038_, v___x_1045_, v___x_1047_, v___x_1060_);
v___x_1062_ = lean_array_push(v___x_1036_, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1063_, 0, v___y_988_);
lean_ctor_set(v___x_1063_, 1, v___y_990_);
lean_ctor_set(v___x_1063_, 2, v___x_1062_);
v___x_1064_ = l_Lean_Syntax_node1(v___y_988_, v___x_1033_, v___x_1063_);
v___x_1065_ = l_Lean_Syntax_node2(v___y_988_, v___x_1030_, v___x_1031_, v___x_1064_);
v___x_1066_ = lean_unsigned_to_nat(9u);
v___x_1067_ = lean_mk_empty_array_with_capacity(v___x_1066_);
v___x_1068_ = lean_array_push(v___x_1067_, v___x_995_);
v___x_1069_ = lean_array_push(v___x_1068_, v___x_1009_);
v___x_1070_ = lean_array_push(v___x_1069_, v___y_984_);
v___x_1071_ = lean_array_push(v___x_1070_, v___x_1010_);
v___x_1072_ = lean_array_push(v___x_1071_, v___x_1017_);
v___x_1073_ = lean_array_push(v___x_1072_, v___x_1019_);
v___x_1074_ = lean_array_push(v___x_1073_, v___x_1026_);
v___x_1075_ = lean_array_push(v___x_1074_, v___x_1028_);
v___x_1076_ = lean_array_push(v___x_1075_, v___x_1065_);
lean_inc(v___y_982_);
v___x_1077_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1077_, 0, v___y_988_);
lean_ctor_set(v___x_1077_, 1, v___y_982_);
lean_ctor_set(v___x_1077_, 2, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
v___jp_1079_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1085_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1086_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1087_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1088_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1089_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1090_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_675_) == 1)
{
lean_object* v_val_1091_; lean_object* v___x_1092_; 
v_val_1091_ = lean_ctor_get(v_doc_x3f_675_, 0);
lean_inc(v_val_1091_);
lean_dec_ref_known(v_doc_x3f_675_, 1);
v___x_1092_ = l_Array_mkArray1___redArg(v_val_1091_);
v___y_982_ = v___x_1088_;
v___y_983_ = v___x_1086_;
v___y_984_ = v___y_1080_;
v___y_985_ = v___x_1085_;
v___y_986_ = v___x_1090_;
v___y_987_ = v_a_1084_;
v___y_988_ = v___y_1081_;
v___y_989_ = v___y_1082_;
v___y_990_ = v___x_1089_;
v___y_991_ = v___y_1083_;
v___y_992_ = v___x_1087_;
v___y_993_ = v___x_1092_;
goto v___jp_981_;
}
else
{
lean_object* v___x_1093_; 
lean_dec(v_doc_x3f_675_);
v___x_1093_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_982_ = v___x_1088_;
v___y_983_ = v___x_1086_;
v___y_984_ = v___y_1080_;
v___y_985_ = v___x_1085_;
v___y_986_ = v___x_1090_;
v___y_987_ = v_a_1084_;
v___y_988_ = v___y_1081_;
v___y_989_ = v___y_1082_;
v___y_990_ = v___x_1089_;
v___y_991_ = v___y_1083_;
v___y_992_ = v___x_1087_;
v___y_993_ = v___x_1093_;
goto v___jp_981_;
}
}
v___jp_1094_:
{
lean_object* v___x_1100_; 
lean_inc(v___y_1095_);
lean_inc(v_k_678_);
v___x_1100_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_678_, v_attrKind_677_, v_attrs_x3f_676_, v___y_1095_, v___y_1097_, v___y_1096_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v___x_1102_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1100_, 1);
v___x_1102_ = l_Lean_Elab_Command_getRef___redArg(v___y_1097_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v___x_1102_, 1);
v___x_1104_ = l_Lean_SourceInfo_fromRef(v_a_1103_, v___y_1099_);
lean_dec(v_a_1103_);
v___x_1105_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1097_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_quotContext_x3f_1106_; 
v_quotContext_x3f_1106_ = lean_ctor_get(v___y_1097_, 5);
if (lean_obj_tag(v_quotContext_x3f_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1108_; lean_object* v_a_1109_; 
v_a_1107_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___x_1105_, 1);
v___x_1108_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1096_);
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
lean_dec_ref(v___x_1108_);
v___y_1080_ = v___y_1098_;
v___y_1081_ = v___x_1104_;
v___y_1082_ = v_a_1101_;
v___y_1083_ = v_a_1107_;
v_a_1084_ = v_a_1109_;
goto v___jp_1079_;
}
else
{
lean_object* v_a_1110_; lean_object* v_val_1111_; 
v_a_1110_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1105_, 1);
v_val_1111_ = lean_ctor_get(v_quotContext_x3f_1106_, 0);
lean_inc(v_val_1111_);
v___y_1080_ = v___y_1098_;
v___y_1081_ = v___x_1104_;
v___y_1082_ = v_a_1101_;
v___y_1083_ = v_a_1110_;
v_a_1084_ = v_val_1111_;
goto v___jp_1079_;
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec(v___x_1104_);
lean_dec(v_a_1101_);
lean_dec(v___y_1098_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_doc_x3f_675_);
v_a_1112_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1105_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1105_);
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
else
{
lean_dec(v_a_1101_);
lean_dec(v___y_1098_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_doc_x3f_675_);
return v___x_1102_;
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v___y_1098_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_doc_x3f_675_);
v_a_1120_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1100_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1100_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
v___jp_1128_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
lean_inc_ref_n(v___y_1134_, 4);
v___x_1141_ = l_Array_append___redArg(v___y_1134_, v___y_1140_);
lean_dec_ref(v___y_1140_);
lean_inc_n(v___y_1138_, 10);
lean_inc_n(v___y_1132_, 36);
v___x_1142_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1142_, 0, v___y_1132_);
lean_ctor_set(v___x_1142_, 1, v___y_1138_);
lean_ctor_set(v___x_1142_, 2, v___x_1141_);
v___x_1143_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1144_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1145_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1136_, 11);
v___x_1146_ = l_Lean_Name_mkStr4(v___y_1136_, v___x_1143_, v___x_1144_, v___x_1145_);
v___x_1147_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___y_1132_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1150_ = l_Lean_Syntax_SepArray_ofElems(v___x_1149_, v___y_1131_);
lean_dec_ref(v___y_1131_);
v___x_1151_ = l_Array_append___redArg(v___y_1134_, v___x_1150_);
lean_dec_ref(v___x_1150_);
v___x_1152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1152_, 0, v___y_1132_);
lean_ctor_set(v___x_1152_, 1, v___y_1138_);
lean_ctor_set(v___x_1152_, 2, v___x_1151_);
v___x_1153_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___y_1132_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = l_Lean_Syntax_node3(v___y_1132_, v___x_1146_, v___x_1148_, v___x_1152_, v___x_1154_);
v___x_1156_ = l_Lean_Syntax_node1(v___y_1132_, v___y_1138_, v___x_1155_);
lean_inc_ref(v___y_1135_);
v___x_1157_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___y_1132_);
lean_ctor_set(v___x_1157_, 1, v___y_1135_);
v___x_1158_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1159_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1129_, 4);
lean_inc_n(v___y_1139_, 4);
v___x_1160_ = l_Lean_addMacroScope(v___y_1139_, v___x_1159_, v___y_1129_);
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1162_, 0, v___y_1132_);
lean_ctor_set(v___x_1162_, 1, v___x_1158_);
lean_ctor_set(v___x_1162_, 2, v___x_1160_);
lean_ctor_set(v___x_1162_, 3, v___x_1161_);
v___x_1163_ = l_Lean_mkIdent(v_k_678_);
v___x_1164_ = l_Lean_Syntax_node2(v___y_1132_, v___y_1138_, v___x_1162_, v___x_1163_);
v___x_1165_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1166_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___y_1132_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_1168_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
v___x_1169_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc_ref_n(v___y_1130_, 2);
v___x_1170_ = l_Lean_Name_mkStr4(v___y_1136_, v___y_1130_, v___x_1168_, v___x_1169_);
lean_inc(v___x_1170_);
v___x_1171_ = l_Lean_addMacroScope(v___y_1139_, v___x_1170_, v___y_1129_);
v___x_1172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1161_);
v___x_1173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v___x_1161_);
v___x_1174_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1174_, 0, v___y_1132_);
lean_ctor_set(v___x_1174_, 1, v___x_1167_);
lean_ctor_set(v___x_1174_, 2, v___x_1171_);
lean_ctor_set(v___x_1174_, 3, v___x_1173_);
v___x_1175_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___y_1132_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1178_ = l_Lean_Name_mkStr4(v___y_1136_, v___x_1143_, v___x_1144_, v___x_1177_);
v___x_1179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___y_1132_);
lean_ctor_set(v___x_1179_, 1, v___x_1177_);
v___x_1180_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_1181_ = l_Lean_Name_mkStr4(v___y_1136_, v___x_1143_, v___x_1144_, v___x_1180_);
v___x_1182_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_1183_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1184_ = l_Lean_addMacroScope(v___y_1139_, v___x_1183_, v___y_1129_);
v___x_1185_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1185_, 0, v___y_1132_);
lean_ctor_set(v___x_1185_, 1, v___x_1182_);
lean_ctor_set(v___x_1185_, 2, v___x_1184_);
lean_ctor_set(v___x_1185_, 3, v___x_1161_);
v___x_1186_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__48, &l_Lean_Elab_Command_elabElabRulesAux___closed__48_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__48);
v___x_1187_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__49));
v___x_1188_ = l_Lean_addMacroScope(v___y_1139_, v___x_1187_, v___y_1129_);
v___x_1189_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1189_, 0, v___y_1132_);
lean_ctor_set(v___x_1189_, 1, v___x_1186_);
lean_ctor_set(v___x_1189_, 2, v___x_1188_);
lean_ctor_set(v___x_1189_, 3, v___x_1161_);
lean_inc_ref(v___x_1185_);
v___x_1190_ = l_Lean_Syntax_node2(v___y_1132_, v___y_1138_, v___x_1185_, v___x_1189_);
v___x_1191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1191_, 0, v___y_1132_);
lean_ctor_set(v___x_1191_, 1, v___y_1138_);
lean_ctor_set(v___x_1191_, 2, v___y_1134_);
v___x_1192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___y_1132_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1195_ = l_Lean_Name_mkStr4(v___y_1136_, v___x_1143_, v___x_1144_, v___x_1194_);
v___x_1196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___y_1132_);
lean_ctor_set(v___x_1196_, 1, v___x_1194_);
v___x_1197_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_1198_ = l_Lean_Name_mkStr4(v___y_1136_, v___x_1143_, v___x_1144_, v___x_1197_);
lean_inc_ref_n(v___x_1191_, 3);
v___x_1199_ = l_Lean_Syntax_node2(v___y_1132_, v___x_1198_, v___x_1191_, v___x_1185_);
v___x_1200_ = l_Lean_Syntax_node1(v___y_1132_, v___y_1138_, v___x_1199_);
v___x_1201_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_1202_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___y_1132_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1204_ = l_Lean_Name_mkStr4(v___y_1136_, v___x_1143_, v___x_1144_, v___x_1203_);
v___x_1205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1206_ = l_Lean_Name_mkStr4(v___y_1136_, v___x_1143_, v___x_1144_, v___x_1205_);
v___x_1207_ = l_Array_append___redArg(v___y_1134_, v_a_688_);
lean_dec(v_a_688_);
v___x_1208_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___y_1132_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1211_ = l_Lean_Name_mkStr4(v___y_1136_, v___x_1143_, v___x_1144_, v___x_1210_);
v___x_1212_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___y_1132_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = l_Lean_Syntax_node1(v___y_1132_, v___x_1211_, v___x_1213_);
v___x_1215_ = l_Lean_Syntax_node1(v___y_1132_, v___y_1138_, v___x_1214_);
v___x_1216_ = l_Lean_Syntax_node1(v___y_1132_, v___y_1138_, v___x_1215_);
v___x_1217_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1218_ = l_Lean_Name_mkStr4(v___y_1136_, v___x_1143_, v___x_1144_, v___x_1217_);
v___x_1219_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1220_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___y_1132_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v___x_1221_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1222_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_1223_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1224_ = l_Lean_addMacroScope(v___y_1139_, v___x_1223_, v___y_1129_);
v___x_1225_ = l_Lean_Name_mkStr3(v___y_1136_, v___y_1130_, v___x_1221_);
v___x_1226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v___x_1161_);
v___x_1227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v___x_1161_);
v___x_1228_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1228_, 0, v___y_1132_);
lean_ctor_set(v___x_1228_, 1, v___x_1222_);
lean_ctor_set(v___x_1228_, 2, v___x_1224_);
lean_ctor_set(v___x_1228_, 3, v___x_1227_);
v___x_1229_ = l_Lean_Syntax_node2(v___y_1132_, v___x_1218_, v___x_1220_, v___x_1228_);
lean_inc_ref(v___x_1193_);
v___x_1230_ = l_Lean_Syntax_node4(v___y_1132_, v___x_1206_, v___x_1209_, v___x_1216_, v___x_1193_, v___x_1229_);
v___x_1231_ = lean_array_push(v___x_1207_, v___x_1230_);
v___x_1232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1232_, 0, v___y_1132_);
lean_ctor_set(v___x_1232_, 1, v___y_1138_);
lean_ctor_set(v___x_1232_, 2, v___x_1231_);
v___x_1233_ = l_Lean_Syntax_node1(v___y_1132_, v___x_1204_, v___x_1232_);
v___x_1234_ = l_Lean_Syntax_node6(v___y_1132_, v___x_1195_, v___x_1196_, v___x_1191_, v___x_1191_, v___x_1200_, v___x_1202_, v___x_1233_);
v___x_1235_ = l_Lean_Syntax_node4(v___y_1132_, v___x_1181_, v___x_1190_, v___x_1191_, v___x_1193_, v___x_1234_);
v___x_1236_ = l_Lean_Syntax_node2(v___y_1132_, v___x_1178_, v___x_1179_, v___x_1235_);
v___x_1237_ = lean_unsigned_to_nat(9u);
v___x_1238_ = lean_mk_empty_array_with_capacity(v___x_1237_);
v___x_1239_ = lean_array_push(v___x_1238_, v___x_1142_);
v___x_1240_ = lean_array_push(v___x_1239_, v___x_1156_);
v___x_1241_ = lean_array_push(v___x_1240_, v___y_1133_);
v___x_1242_ = lean_array_push(v___x_1241_, v___x_1157_);
v___x_1243_ = lean_array_push(v___x_1242_, v___x_1164_);
v___x_1244_ = lean_array_push(v___x_1243_, v___x_1166_);
v___x_1245_ = lean_array_push(v___x_1244_, v___x_1174_);
v___x_1246_ = lean_array_push(v___x_1245_, v___x_1176_);
v___x_1247_ = lean_array_push(v___x_1246_, v___x_1236_);
lean_inc(v___y_1137_);
v___x_1248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1248_, 0, v___y_1132_);
lean_ctor_set(v___x_1248_, 1, v___y_1137_);
lean_ctor_set(v___x_1248_, 2, v___x_1247_);
v___x_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
return v___x_1249_;
}
v___jp_1250_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1256_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1257_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1258_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1259_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1260_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1261_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_675_) == 1)
{
lean_object* v_val_1262_; lean_object* v___x_1263_; 
v_val_1262_ = lean_ctor_get(v_doc_x3f_675_, 0);
lean_inc(v_val_1262_);
lean_dec_ref_known(v_doc_x3f_675_, 1);
v___x_1263_ = l_Array_mkArray1___redArg(v_val_1262_);
v___y_1129_ = v___y_1251_;
v___y_1130_ = v___x_1257_;
v___y_1131_ = v___y_1253_;
v___y_1132_ = v___y_1252_;
v___y_1133_ = v___y_1254_;
v___y_1134_ = v___x_1261_;
v___y_1135_ = v___x_1258_;
v___y_1136_ = v___x_1256_;
v___y_1137_ = v___x_1259_;
v___y_1138_ = v___x_1260_;
v___y_1139_ = v_a_1255_;
v___y_1140_ = v___x_1263_;
goto v___jp_1128_;
}
else
{
lean_object* v___x_1264_; 
lean_dec(v_doc_x3f_675_);
v___x_1264_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_1129_ = v___y_1251_;
v___y_1130_ = v___x_1257_;
v___y_1131_ = v___y_1253_;
v___y_1132_ = v___y_1252_;
v___y_1133_ = v___y_1254_;
v___y_1134_ = v___x_1261_;
v___y_1135_ = v___x_1258_;
v___y_1136_ = v___x_1256_;
v___y_1137_ = v___x_1259_;
v___y_1138_ = v___x_1260_;
v___y_1139_ = v_a_1255_;
v___y_1140_ = v___x_1264_;
goto v___jp_1128_;
}
}
v___jp_1265_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_inc_ref_n(v___y_1277_, 3);
v___x_1279_ = l_Array_append___redArg(v___y_1277_, v___y_1278_);
lean_dec_ref(v___y_1278_);
lean_inc_n(v___y_1274_, 7);
lean_inc_n(v___y_1273_, 26);
v___x_1280_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1280_, 0, v___y_1273_);
lean_ctor_set(v___x_1280_, 1, v___y_1274_);
lean_ctor_set(v___x_1280_, 2, v___x_1279_);
v___x_1281_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1282_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1283_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1272_, 8);
v___x_1284_ = l_Lean_Name_mkStr4(v___y_1272_, v___x_1281_, v___x_1282_, v___x_1283_);
v___x_1285_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___y_1273_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1288_ = l_Lean_Syntax_SepArray_ofElems(v___x_1287_, v___y_1267_);
lean_dec_ref(v___y_1267_);
v___x_1289_ = l_Array_append___redArg(v___y_1277_, v___x_1288_);
lean_dec_ref(v___x_1288_);
v___x_1290_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1290_, 0, v___y_1273_);
lean_ctor_set(v___x_1290_, 1, v___y_1274_);
lean_ctor_set(v___x_1290_, 2, v___x_1289_);
v___x_1291_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___y_1273_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
v___x_1293_ = l_Lean_Syntax_node3(v___y_1273_, v___x_1284_, v___x_1286_, v___x_1290_, v___x_1292_);
v___x_1294_ = l_Lean_Syntax_node1(v___y_1273_, v___y_1274_, v___x_1293_);
lean_inc_ref(v___y_1266_);
v___x_1295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___y_1273_);
lean_ctor_set(v___x_1295_, 1, v___y_1266_);
v___x_1296_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1297_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1276_, 2);
lean_inc_n(v___y_1268_, 2);
v___x_1298_ = l_Lean_addMacroScope(v___y_1268_, v___x_1297_, v___y_1276_);
v___x_1299_ = lean_box(0);
v___x_1300_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1300_, 0, v___y_1273_);
lean_ctor_set(v___x_1300_, 1, v___x_1296_);
lean_ctor_set(v___x_1300_, 2, v___x_1298_);
lean_ctor_set(v___x_1300_, 3, v___x_1299_);
v___x_1301_ = l_Lean_mkIdent(v_k_678_);
v___x_1302_ = l_Lean_Syntax_node2(v___y_1273_, v___y_1274_, v___x_1300_, v___x_1301_);
v___x_1303_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___y_1273_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__51, &l_Lean_Elab_Command_elabElabRulesAux___closed__51_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__51);
v___x_1306_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__52));
lean_inc_ref(v___y_1269_);
lean_inc_ref_n(v___y_1271_, 2);
v___x_1307_ = l_Lean_Name_mkStr4(v___y_1272_, v___y_1271_, v___y_1269_, v___x_1306_);
lean_inc(v___x_1307_);
v___x_1308_ = l_Lean_addMacroScope(v___y_1268_, v___x_1307_, v___y_1276_);
v___x_1309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1307_);
lean_ctor_set(v___x_1309_, 1, v___x_1299_);
v___x_1310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v___x_1299_);
v___x_1311_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1311_, 0, v___y_1273_);
lean_ctor_set(v___x_1311_, 1, v___x_1305_);
lean_ctor_set(v___x_1311_, 2, v___x_1308_);
lean_ctor_set(v___x_1311_, 3, v___x_1310_);
v___x_1312_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___y_1273_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1315_ = l_Lean_Name_mkStr4(v___y_1272_, v___x_1281_, v___x_1282_, v___x_1314_);
v___x_1316_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___y_1273_);
lean_ctor_set(v___x_1316_, 1, v___x_1314_);
v___x_1317_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1318_ = l_Lean_Name_mkStr4(v___y_1272_, v___x_1281_, v___x_1282_, v___x_1317_);
v___x_1319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1320_ = l_Lean_Name_mkStr4(v___y_1272_, v___x_1281_, v___x_1282_, v___x_1319_);
v___x_1321_ = l_Array_append___redArg(v___y_1277_, v_a_688_);
lean_dec(v_a_688_);
v___x_1322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___y_1273_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1325_ = l_Lean_Name_mkStr4(v___y_1272_, v___x_1281_, v___x_1282_, v___x_1324_);
v___x_1326_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___y_1273_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v___x_1328_ = l_Lean_Syntax_node1(v___y_1273_, v___x_1325_, v___x_1327_);
v___x_1329_ = l_Lean_Syntax_node1(v___y_1273_, v___y_1274_, v___x_1328_);
v___x_1330_ = l_Lean_Syntax_node1(v___y_1273_, v___y_1274_, v___x_1329_);
v___x_1331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1332_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___y_1273_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1334_ = l_Lean_Name_mkStr4(v___y_1272_, v___x_1281_, v___x_1282_, v___x_1333_);
v___x_1335_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___y_1273_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___x_1337_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1338_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_1339_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1340_ = l_Lean_addMacroScope(v___y_1268_, v___x_1339_, v___y_1276_);
v___x_1341_ = l_Lean_Name_mkStr3(v___y_1272_, v___y_1271_, v___x_1337_);
v___x_1342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
lean_ctor_set(v___x_1342_, 1, v___x_1299_);
v___x_1343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
lean_ctor_set(v___x_1343_, 1, v___x_1299_);
v___x_1344_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1344_, 0, v___y_1273_);
lean_ctor_set(v___x_1344_, 1, v___x_1338_);
lean_ctor_set(v___x_1344_, 2, v___x_1340_);
lean_ctor_set(v___x_1344_, 3, v___x_1343_);
v___x_1345_ = l_Lean_Syntax_node2(v___y_1273_, v___x_1334_, v___x_1336_, v___x_1344_);
v___x_1346_ = l_Lean_Syntax_node4(v___y_1273_, v___x_1320_, v___x_1323_, v___x_1330_, v___x_1332_, v___x_1345_);
v___x_1347_ = lean_array_push(v___x_1321_, v___x_1346_);
v___x_1348_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1348_, 0, v___y_1273_);
lean_ctor_set(v___x_1348_, 1, v___y_1274_);
lean_ctor_set(v___x_1348_, 2, v___x_1347_);
v___x_1349_ = l_Lean_Syntax_node1(v___y_1273_, v___x_1318_, v___x_1348_);
v___x_1350_ = l_Lean_Syntax_node2(v___y_1273_, v___x_1315_, v___x_1316_, v___x_1349_);
v___x_1351_ = lean_unsigned_to_nat(9u);
v___x_1352_ = lean_mk_empty_array_with_capacity(v___x_1351_);
v___x_1353_ = lean_array_push(v___x_1352_, v___x_1280_);
v___x_1354_ = lean_array_push(v___x_1353_, v___x_1294_);
v___x_1355_ = lean_array_push(v___x_1354_, v___y_1270_);
v___x_1356_ = lean_array_push(v___x_1355_, v___x_1295_);
v___x_1357_ = lean_array_push(v___x_1356_, v___x_1302_);
v___x_1358_ = lean_array_push(v___x_1357_, v___x_1304_);
v___x_1359_ = lean_array_push(v___x_1358_, v___x_1311_);
v___x_1360_ = lean_array_push(v___x_1359_, v___x_1313_);
v___x_1361_ = lean_array_push(v___x_1360_, v___x_1350_);
lean_inc(v___y_1275_);
v___x_1362_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1362_, 0, v___y_1273_);
lean_ctor_set(v___x_1362_, 1, v___y_1275_);
lean_ctor_set(v___x_1362_, 2, v___x_1361_);
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
return v___x_1363_;
}
v___jp_1364_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1370_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1371_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1372_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_1373_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1374_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1375_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1376_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_675_) == 1)
{
lean_object* v_val_1377_; lean_object* v___x_1378_; 
v_val_1377_ = lean_ctor_get(v_doc_x3f_675_, 0);
lean_inc(v_val_1377_);
lean_dec_ref_known(v_doc_x3f_675_, 1);
v___x_1378_ = l_Array_mkArray1___redArg(v_val_1377_);
v___y_1266_ = v___x_1373_;
v___y_1267_ = v___y_1366_;
v___y_1268_ = v_a_1369_;
v___y_1269_ = v___x_1372_;
v___y_1270_ = v___y_1368_;
v___y_1271_ = v___x_1371_;
v___y_1272_ = v___x_1370_;
v___y_1273_ = v___y_1365_;
v___y_1274_ = v___x_1375_;
v___y_1275_ = v___x_1374_;
v___y_1276_ = v___y_1367_;
v___y_1277_ = v___x_1376_;
v___y_1278_ = v___x_1378_;
goto v___jp_1265_;
}
else
{
lean_object* v___x_1379_; 
lean_dec(v_doc_x3f_675_);
v___x_1379_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_1266_ = v___x_1373_;
v___y_1267_ = v___y_1366_;
v___y_1268_ = v_a_1369_;
v___y_1269_ = v___x_1372_;
v___y_1270_ = v___y_1368_;
v___y_1271_ = v___x_1371_;
v___y_1272_ = v___x_1370_;
v___y_1273_ = v___y_1365_;
v___y_1274_ = v___x_1375_;
v___y_1275_ = v___x_1374_;
v___y_1276_ = v___y_1367_;
v___y_1277_ = v___x_1376_;
v___y_1278_ = v___x_1379_;
goto v___jp_1265_;
}
}
v___jp_1380_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_inc_ref_n(v___y_1385_, 4);
v___x_1393_ = l_Array_append___redArg(v___y_1385_, v___y_1392_);
lean_dec_ref(v___y_1392_);
lean_inc_n(v___y_1391_, 10);
lean_inc_n(v___y_1381_, 35);
v___x_1394_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1394_, 0, v___y_1381_);
lean_ctor_set(v___x_1394_, 1, v___y_1391_);
lean_ctor_set(v___x_1394_, 2, v___x_1393_);
v___x_1395_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1396_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1397_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1384_, 11);
v___x_1398_ = l_Lean_Name_mkStr4(v___y_1384_, v___x_1395_, v___x_1396_, v___x_1397_);
v___x_1399_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1400_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___y_1381_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
v___x_1401_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1402_ = l_Lean_Syntax_SepArray_ofElems(v___x_1401_, v___y_1388_);
lean_dec_ref(v___y_1388_);
v___x_1403_ = l_Array_append___redArg(v___y_1385_, v___x_1402_);
lean_dec_ref(v___x_1402_);
v___x_1404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1404_, 0, v___y_1381_);
lean_ctor_set(v___x_1404_, 1, v___y_1391_);
lean_ctor_set(v___x_1404_, 2, v___x_1403_);
v___x_1405_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1406_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___y_1381_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
v___x_1407_ = l_Lean_Syntax_node3(v___y_1381_, v___x_1398_, v___x_1400_, v___x_1404_, v___x_1406_);
v___x_1408_ = l_Lean_Syntax_node1(v___y_1381_, v___y_1391_, v___x_1407_);
lean_inc_ref(v___y_1390_);
v___x_1409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___y_1381_);
lean_ctor_set(v___x_1409_, 1, v___y_1390_);
v___x_1410_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1411_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1383_, 3);
lean_inc_n(v___y_1389_, 3);
v___x_1412_ = l_Lean_addMacroScope(v___y_1389_, v___x_1411_, v___y_1383_);
v___x_1413_ = lean_box(0);
v___x_1414_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1414_, 0, v___y_1381_);
lean_ctor_set(v___x_1414_, 1, v___x_1410_);
lean_ctor_set(v___x_1414_, 2, v___x_1412_);
lean_ctor_set(v___x_1414_, 3, v___x_1413_);
v___x_1415_ = l_Lean_mkIdent(v_k_678_);
v___x_1416_ = l_Lean_Syntax_node2(v___y_1381_, v___y_1391_, v___x_1414_, v___x_1415_);
v___x_1417_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___y_1381_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__35, &l_Lean_Elab_Command_elabElabRulesAux___closed__35_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__35);
v___x_1420_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__36));
lean_inc_ref_n(v___y_1387_, 2);
v___x_1421_ = l_Lean_Name_mkStr4(v___y_1384_, v___y_1387_, v___x_1396_, v___x_1420_);
lean_inc(v___x_1421_);
v___x_1422_ = l_Lean_addMacroScope(v___y_1389_, v___x_1421_, v___y_1383_);
v___x_1423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1421_);
lean_ctor_set(v___x_1423_, 1, v___x_1413_);
v___x_1424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
lean_ctor_set(v___x_1424_, 1, v___x_1413_);
v___x_1425_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1425_, 0, v___y_1381_);
lean_ctor_set(v___x_1425_, 1, v___x_1419_);
lean_ctor_set(v___x_1425_, 2, v___x_1422_);
lean_ctor_set(v___x_1425_, 3, v___x_1424_);
v___x_1426_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1427_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___y_1381_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1429_ = l_Lean_Name_mkStr4(v___y_1384_, v___x_1395_, v___x_1396_, v___x_1428_);
v___x_1430_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___y_1381_);
lean_ctor_set(v___x_1430_, 1, v___x_1428_);
v___x_1431_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_1432_ = l_Lean_Name_mkStr4(v___y_1384_, v___x_1395_, v___x_1396_, v___x_1431_);
v___x_1433_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_1434_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1435_ = l_Lean_addMacroScope(v___y_1389_, v___x_1434_, v___y_1383_);
v___x_1436_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1436_, 0, v___y_1381_);
lean_ctor_set(v___x_1436_, 1, v___x_1433_);
lean_ctor_set(v___x_1436_, 2, v___x_1435_);
lean_ctor_set(v___x_1436_, 3, v___x_1413_);
v___x_1437_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1438_ = l_Lean_Name_mkStr4(v___y_1384_, v___x_1395_, v___x_1396_, v___x_1437_);
v___x_1439_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___y_1381_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
v___x_1441_ = l_Lean_Syntax_node1(v___y_1381_, v___x_1438_, v___x_1440_);
lean_inc(v___x_1441_);
lean_inc_ref(v___x_1436_);
v___x_1442_ = l_Lean_Syntax_node2(v___y_1381_, v___y_1391_, v___x_1436_, v___x_1441_);
v___x_1443_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1443_, 0, v___y_1381_);
lean_ctor_set(v___x_1443_, 1, v___y_1391_);
lean_ctor_set(v___x_1443_, 2, v___y_1385_);
v___x_1444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___y_1381_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1447_ = l_Lean_Name_mkStr4(v___y_1384_, v___x_1395_, v___x_1396_, v___x_1446_);
v___x_1448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___y_1381_);
lean_ctor_set(v___x_1448_, 1, v___x_1446_);
v___x_1449_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_1450_ = l_Lean_Name_mkStr4(v___y_1384_, v___x_1395_, v___x_1396_, v___x_1449_);
lean_inc_ref_n(v___x_1443_, 3);
v___x_1451_ = l_Lean_Syntax_node2(v___y_1381_, v___x_1450_, v___x_1443_, v___x_1436_);
v___x_1452_ = l_Lean_Syntax_node1(v___y_1381_, v___y_1391_, v___x_1451_);
v___x_1453_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_1454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___y_1381_);
lean_ctor_set(v___x_1454_, 1, v___x_1453_);
v___x_1455_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1456_ = l_Lean_Name_mkStr4(v___y_1384_, v___x_1395_, v___x_1396_, v___x_1455_);
v___x_1457_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1458_ = l_Lean_Name_mkStr4(v___y_1384_, v___x_1395_, v___x_1396_, v___x_1457_);
v___x_1459_ = l_Array_append___redArg(v___y_1385_, v_a_688_);
lean_dec(v_a_688_);
v___x_1460_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1461_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___y_1381_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = l_Lean_Syntax_node1(v___y_1381_, v___y_1391_, v___x_1441_);
v___x_1463_ = l_Lean_Syntax_node1(v___y_1381_, v___y_1391_, v___x_1462_);
v___x_1464_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1465_ = l_Lean_Name_mkStr4(v___y_1384_, v___x_1395_, v___x_1396_, v___x_1464_);
v___x_1466_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___y_1381_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1469_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_1470_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1471_ = l_Lean_addMacroScope(v___y_1389_, v___x_1470_, v___y_1383_);
v___x_1472_ = l_Lean_Name_mkStr3(v___y_1384_, v___y_1387_, v___x_1468_);
v___x_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v___x_1413_);
v___x_1474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
lean_ctor_set(v___x_1474_, 1, v___x_1413_);
v___x_1475_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1475_, 0, v___y_1381_);
lean_ctor_set(v___x_1475_, 1, v___x_1469_);
lean_ctor_set(v___x_1475_, 2, v___x_1471_);
lean_ctor_set(v___x_1475_, 3, v___x_1474_);
v___x_1476_ = l_Lean_Syntax_node2(v___y_1381_, v___x_1465_, v___x_1467_, v___x_1475_);
lean_inc_ref(v___x_1445_);
v___x_1477_ = l_Lean_Syntax_node4(v___y_1381_, v___x_1458_, v___x_1461_, v___x_1463_, v___x_1445_, v___x_1476_);
v___x_1478_ = lean_array_push(v___x_1459_, v___x_1477_);
v___x_1479_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1479_, 0, v___y_1381_);
lean_ctor_set(v___x_1479_, 1, v___y_1391_);
lean_ctor_set(v___x_1479_, 2, v___x_1478_);
v___x_1480_ = l_Lean_Syntax_node1(v___y_1381_, v___x_1456_, v___x_1479_);
v___x_1481_ = l_Lean_Syntax_node6(v___y_1381_, v___x_1447_, v___x_1448_, v___x_1443_, v___x_1443_, v___x_1452_, v___x_1454_, v___x_1480_);
v___x_1482_ = l_Lean_Syntax_node4(v___y_1381_, v___x_1432_, v___x_1442_, v___x_1443_, v___x_1445_, v___x_1481_);
v___x_1483_ = l_Lean_Syntax_node2(v___y_1381_, v___x_1429_, v___x_1430_, v___x_1482_);
v___x_1484_ = lean_unsigned_to_nat(9u);
v___x_1485_ = lean_mk_empty_array_with_capacity(v___x_1484_);
v___x_1486_ = lean_array_push(v___x_1485_, v___x_1394_);
v___x_1487_ = lean_array_push(v___x_1486_, v___x_1408_);
v___x_1488_ = lean_array_push(v___x_1487_, v___y_1386_);
v___x_1489_ = lean_array_push(v___x_1488_, v___x_1409_);
v___x_1490_ = lean_array_push(v___x_1489_, v___x_1416_);
v___x_1491_ = lean_array_push(v___x_1490_, v___x_1418_);
v___x_1492_ = lean_array_push(v___x_1491_, v___x_1425_);
v___x_1493_ = lean_array_push(v___x_1492_, v___x_1427_);
v___x_1494_ = lean_array_push(v___x_1493_, v___x_1483_);
lean_inc(v___y_1382_);
v___x_1495_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1495_, 0, v___y_1381_);
lean_ctor_set(v___x_1495_, 1, v___y_1382_);
lean_ctor_set(v___x_1495_, 2, v___x_1494_);
v___x_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
return v___x_1496_;
}
v___jp_1497_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1503_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1504_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1505_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1506_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1507_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1508_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_675_) == 1)
{
lean_object* v_val_1509_; lean_object* v___x_1510_; 
v_val_1509_ = lean_ctor_get(v_doc_x3f_675_, 0);
lean_inc(v_val_1509_);
lean_dec_ref_known(v_doc_x3f_675_, 1);
v___x_1510_ = l_Array_mkArray1___redArg(v_val_1509_);
v___y_1381_ = v___y_1498_;
v___y_1382_ = v___x_1506_;
v___y_1383_ = v___y_1499_;
v___y_1384_ = v___x_1503_;
v___y_1385_ = v___x_1508_;
v___y_1386_ = v___y_1500_;
v___y_1387_ = v___x_1504_;
v___y_1388_ = v___y_1501_;
v___y_1389_ = v_a_1502_;
v___y_1390_ = v___x_1505_;
v___y_1391_ = v___x_1507_;
v___y_1392_ = v___x_1510_;
goto v___jp_1380_;
}
else
{
lean_object* v___x_1511_; 
lean_dec(v_doc_x3f_675_);
v___x_1511_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_1381_ = v___y_1498_;
v___y_1382_ = v___x_1506_;
v___y_1383_ = v___y_1499_;
v___y_1384_ = v___x_1503_;
v___y_1385_ = v___x_1508_;
v___y_1386_ = v___y_1500_;
v___y_1387_ = v___x_1504_;
v___y_1388_ = v___y_1501_;
v___y_1389_ = v_a_1502_;
v___y_1390_ = v___x_1505_;
v___y_1391_ = v___x_1507_;
v___y_1392_ = v___x_1511_;
goto v___jp_1380_;
}
}
v___jp_1512_:
{
lean_object* v___x_1516_; 
lean_inc(v_attrKind_677_);
v___x_1516_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_677_);
if (lean_obj_tag(v_expty_x3f_680_) == 1)
{
lean_object* v_val_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v_val_1517_ = lean_ctor_get(v_expty_x3f_680_, 0);
lean_inc(v_val_1517_);
lean_dec_ref_known(v_expty_x3f_680_, 1);
v___x_1518_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v___x_1519_ = lean_name_eq(v_catName_1513_, v___x_1518_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; uint8_t v___x_1521_; 
v___x_1520_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__56));
v___x_1521_ = lean_name_eq(v_catName_1513_, v___x_1520_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_dec(v___x_1516_);
lean_del_object(v___x_690_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_attrKind_677_);
lean_dec(v_doc_x3f_675_);
v___x_1522_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__58, &l_Lean_Elab_Command_elabElabRulesAux___closed__58_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__58);
v___x_1523_ = l_Lean_MessageData_ofName(v_catName_1513_);
v___x_1524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1522_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__60, &l_Lean_Elab_Command_elabElabRulesAux___closed__60_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__60);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_val_1517_, v___x_1526_, v___y_1514_, v___y_1515_);
lean_dec(v_val_1517_);
return v___x_1527_;
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec(v_catName_1513_);
v___x_1528_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__62));
lean_inc(v_k_678_);
v___x_1529_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_678_, v_attrKind_677_, v_attrs_x3f_676_, v___x_1528_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1531_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v___x_1531_ = l_Lean_Elab_Command_getRef___redArg(v___y_1514_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v___x_1533_ = l_Lean_SourceInfo_fromRef(v_a_1532_, v___x_1519_);
lean_dec(v_a_1532_);
v___x_1534_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1514_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_quotContext_x3f_1535_; 
v_quotContext_x3f_1535_ = lean_ctor_get(v___y_1514_, 5);
if (lean_obj_tag(v_quotContext_x3f_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1537_; lean_object* v_a_1538_; 
v_a_1536_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1534_, 1);
v___x_1537_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1515_);
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref(v___x_1537_);
v___y_814_ = v___x_1533_;
v___y_815_ = v_a_1530_;
v___y_816_ = v_val_1517_;
v___y_817_ = v___x_1516_;
v___y_818_ = v_a_1536_;
v_a_819_ = v_a_1538_;
goto v___jp_813_;
}
else
{
lean_object* v_a_1539_; lean_object* v_val_1540_; 
v_a_1539_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1534_, 1);
v_val_1540_ = lean_ctor_get(v_quotContext_x3f_1535_, 0);
lean_inc(v_val_1540_);
v___y_814_ = v___x_1533_;
v___y_815_ = v_a_1530_;
v___y_816_ = v_val_1517_;
v___y_817_ = v___x_1516_;
v___y_818_ = v_a_1539_;
v_a_819_ = v_val_1540_;
goto v___jp_813_;
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec(v___x_1533_);
lean_dec(v_a_1530_);
lean_dec(v_val_1517_);
lean_dec(v___x_1516_);
lean_del_object(v___x_690_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_doc_x3f_675_);
v_a_1541_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1534_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1534_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
else
{
lean_dec(v_a_1530_);
lean_dec(v_val_1517_);
lean_dec(v___x_1516_);
lean_del_object(v___x_690_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_doc_x3f_675_);
return v___x_1531_;
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec(v_val_1517_);
lean_dec(v___x_1516_);
lean_del_object(v___x_690_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_doc_x3f_675_);
v_a_1549_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1529_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1529_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
else
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_dec(v_catName_1513_);
lean_del_object(v___x_690_);
v___x_1557_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__64));
lean_inc(v_k_678_);
v___x_1558_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_678_, v_attrKind_677_, v_attrs_x3f_676_, v___x_1557_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1560_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1558_, 1);
v___x_1560_ = l_Lean_Elab_Command_getRef___redArg(v___y_1514_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; uint8_t v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
v___x_1562_ = 0;
v___x_1563_ = l_Lean_SourceInfo_fromRef(v_a_1561_, v___x_1562_);
lean_dec(v_a_1561_);
v___x_1564_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1514_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_quotContext_x3f_1565_; 
v_quotContext_x3f_1565_ = lean_ctor_get(v___y_1514_, 5);
if (lean_obj_tag(v_quotContext_x3f_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1567_; lean_object* v_a_1568_; 
v_a_1566_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1564_, 1);
v___x_1567_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1515_);
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref(v___x_1567_);
v___y_966_ = v_val_1517_;
v___y_967_ = v___x_1516_;
v___y_968_ = v___x_1563_;
v___y_969_ = v_a_1566_;
v___y_970_ = v_a_1559_;
v_a_971_ = v_a_1568_;
goto v___jp_965_;
}
else
{
lean_object* v_a_1569_; lean_object* v_val_1570_; 
v_a_1569_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1564_, 1);
v_val_1570_ = lean_ctor_get(v_quotContext_x3f_1565_, 0);
lean_inc(v_val_1570_);
v___y_966_ = v_val_1517_;
v___y_967_ = v___x_1516_;
v___y_968_ = v___x_1563_;
v___y_969_ = v_a_1569_;
v___y_970_ = v_a_1559_;
v_a_971_ = v_val_1570_;
goto v___jp_965_;
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v___x_1563_);
lean_dec(v_a_1559_);
lean_dec(v_val_1517_);
lean_dec(v___x_1516_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_doc_x3f_675_);
v_a_1571_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1564_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1564_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
else
{
lean_dec(v_a_1559_);
lean_dec(v_val_1517_);
lean_dec(v___x_1516_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_doc_x3f_675_);
return v___x_1560_;
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v_val_1517_);
lean_dec(v___x_1516_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_doc_x3f_675_);
v_a_1579_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1558_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1558_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
else
{
lean_object* v___x_1587_; uint8_t v___x_1588_; 
lean_del_object(v___x_690_);
lean_dec(v_expty_x3f_680_);
v___x_1587_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v___x_1588_ = lean_name_eq(v_catName_1513_, v___x_1587_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; uint8_t v___x_1590_; 
v___x_1589_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__66));
v___x_1590_ = lean_name_eq(v_catName_1513_, v___x_1589_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__68));
v___x_1592_ = lean_name_eq(v_catName_1513_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1593_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__70));
v___x_1594_ = lean_name_eq(v_catName_1513_, v___x_1593_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1595_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__56));
v___x_1596_ = lean_name_eq(v_catName_1513_, v___x_1595_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_dec(v___x_1516_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_attrKind_677_);
lean_dec(v_doc_x3f_675_);
v___x_1597_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__72, &l_Lean_Elab_Command_elabElabRulesAux___closed__72_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__72);
v___x_1598_ = l_Lean_MessageData_ofName(v_catName_1513_);
v___x_1599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1597_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_1601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v___x_1601_, v___y_1514_, v___y_1515_);
return v___x_1602_;
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec(v_catName_1513_);
v___x_1603_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__62));
lean_inc(v_k_678_);
v___x_1604_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_678_, v_attrKind_677_, v_attrs_x3f_676_, v___x_1603_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1606_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1604_, 1);
v___x_1606_ = l_Lean_Elab_Command_getRef___redArg(v___y_1514_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1607_);
lean_dec_ref_known(v___x_1606_, 1);
v___x_1608_ = l_Lean_SourceInfo_fromRef(v_a_1607_, v___x_1594_);
lean_dec(v_a_1607_);
v___x_1609_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1514_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_quotContext_x3f_1610_; 
v_quotContext_x3f_1610_ = lean_ctor_get(v___y_1514_, 5);
if (lean_obj_tag(v_quotContext_x3f_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1612_; lean_object* v_a_1613_; 
v_a_1611_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1609_, 1);
v___x_1612_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1515_);
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
lean_dec_ref(v___x_1612_);
v___y_1251_ = v_a_1611_;
v___y_1252_ = v___x_1608_;
v___y_1253_ = v_a_1605_;
v___y_1254_ = v___x_1516_;
v_a_1255_ = v_a_1613_;
goto v___jp_1250_;
}
else
{
lean_object* v_a_1614_; lean_object* v_val_1615_; 
v_a_1614_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1609_, 1);
v_val_1615_ = lean_ctor_get(v_quotContext_x3f_1610_, 0);
lean_inc(v_val_1615_);
v___y_1251_ = v_a_1614_;
v___y_1252_ = v___x_1608_;
v___y_1253_ = v_a_1605_;
v___y_1254_ = v___x_1516_;
v_a_1255_ = v_val_1615_;
goto v___jp_1250_;
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec(v___x_1608_);
lean_dec(v_a_1605_);
lean_dec(v___x_1516_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_doc_x3f_675_);
v_a_1616_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1609_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1609_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
else
{
lean_dec(v_a_1605_);
lean_dec(v___x_1516_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_doc_x3f_675_);
return v___x_1606_;
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec(v___x_1516_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_doc_x3f_675_);
v_a_1624_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1604_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1604_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
else
{
lean_dec(v_catName_1513_);
v___y_1095_ = v___x_1591_;
v___y_1096_ = v___y_1515_;
v___y_1097_ = v___y_1514_;
v___y_1098_ = v___x_1516_;
v___y_1099_ = v___x_1590_;
goto v___jp_1094_;
}
}
else
{
lean_dec(v_catName_1513_);
v___y_1095_ = v___x_1591_;
v___y_1096_ = v___y_1515_;
v___y_1097_ = v___y_1514_;
v___y_1098_ = v___x_1516_;
v___y_1099_ = v___x_1590_;
goto v___jp_1094_;
}
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_dec(v_catName_1513_);
v___x_1632_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__74));
lean_inc(v_k_678_);
v___x_1633_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_678_, v_attrKind_677_, v_attrs_x3f_676_, v___x_1632_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1635_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
v___x_1635_ = l_Lean_Elab_Command_getRef___redArg(v___y_1514_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1637_ = l_Lean_SourceInfo_fromRef(v_a_1636_, v___x_1588_);
lean_dec(v_a_1636_);
v___x_1638_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1514_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_quotContext_x3f_1639_; 
v_quotContext_x3f_1639_ = lean_ctor_get(v___y_1514_, 5);
if (lean_obj_tag(v_quotContext_x3f_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1641_; lean_object* v_a_1642_; 
v_a_1640_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1641_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1515_);
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref(v___x_1641_);
v___y_1365_ = v___x_1637_;
v___y_1366_ = v_a_1634_;
v___y_1367_ = v_a_1640_;
v___y_1368_ = v___x_1516_;
v_a_1369_ = v_a_1642_;
goto v___jp_1364_;
}
else
{
lean_object* v_a_1643_; lean_object* v_val_1644_; 
v_a_1643_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1643_);
lean_dec_ref_known(v___x_1638_, 1);
v_val_1644_ = lean_ctor_get(v_quotContext_x3f_1639_, 0);
lean_inc(v_val_1644_);
v___y_1365_ = v___x_1637_;
v___y_1366_ = v_a_1634_;
v___y_1367_ = v_a_1643_;
v___y_1368_ = v___x_1516_;
v_a_1369_ = v_val_1644_;
goto v___jp_1364_;
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_dec(v___x_1637_);
lean_dec(v_a_1634_);
lean_dec(v___x_1516_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_doc_x3f_675_);
v_a_1645_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1638_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1638_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
else
{
lean_dec(v_a_1634_);
lean_dec(v___x_1516_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_doc_x3f_675_);
return v___x_1635_;
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v___x_1516_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_doc_x3f_675_);
v_a_1653_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1633_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1633_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
lean_dec(v_catName_1513_);
v___x_1661_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__64));
lean_inc(v_k_678_);
v___x_1662_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_678_, v_attrKind_677_, v_attrs_x3f_676_, v___x_1661_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1664_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
lean_dec_ref_known(v___x_1662_, 1);
v___x_1664_ = l_Lean_Elab_Command_getRef___redArg(v___y_1514_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; uint8_t v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref_known(v___x_1664_, 1);
v___x_1666_ = 0;
v___x_1667_ = l_Lean_SourceInfo_fromRef(v_a_1665_, v___x_1666_);
lean_dec(v_a_1665_);
v___x_1668_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1514_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_quotContext_x3f_1669_; 
v_quotContext_x3f_1669_ = lean_ctor_get(v___y_1514_, 5);
if (lean_obj_tag(v_quotContext_x3f_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1671_; lean_object* v_a_1672_; 
v_a_1670_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1670_);
lean_dec_ref_known(v___x_1668_, 1);
v___x_1671_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1515_);
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
lean_dec_ref(v___x_1671_);
v___y_1498_ = v___x_1667_;
v___y_1499_ = v_a_1670_;
v___y_1500_ = v___x_1516_;
v___y_1501_ = v_a_1663_;
v_a_1502_ = v_a_1672_;
goto v___jp_1497_;
}
else
{
lean_object* v_a_1673_; lean_object* v_val_1674_; 
v_a_1673_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1673_);
lean_dec_ref_known(v___x_1668_, 1);
v_val_1674_ = lean_ctor_get(v_quotContext_x3f_1669_, 0);
lean_inc(v_val_1674_);
v___y_1498_ = v___x_1667_;
v___y_1499_ = v_a_1673_;
v___y_1500_ = v___x_1516_;
v___y_1501_ = v_a_1663_;
v_a_1502_ = v_val_1674_;
goto v___jp_1497_;
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
lean_dec(v___x_1667_);
lean_dec(v_a_1663_);
lean_dec(v___x_1516_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_doc_x3f_675_);
v_a_1675_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1668_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1668_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
else
{
lean_dec(v_a_1663_);
lean_dec(v___x_1516_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_doc_x3f_675_);
return v___x_1664_;
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec(v___x_1516_);
lean_dec(v_a_688_);
lean_dec(v_k_678_);
lean_dec(v_doc_x3f_675_);
v_a_1683_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1662_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1662_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
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
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec(v_expty_x3f_680_);
lean_dec(v_k_678_);
lean_dec(v_attrKind_677_);
lean_dec(v_doc_x3f_675_);
v_a_1705_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_687_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_687_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_elabElabRulesAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_doc_x3f_675_ = stack[0].m_obj;
lean_object* v_attrs_x3f_676_ = stack[1].m_obj;
lean_object* v_attrKind_677_ = stack[2].m_obj;
lean_object* v_k_678_ = stack[3].m_obj;
lean_object* v_cat_x3f_679_ = stack[4].m_obj;
lean_object* v_expty_x3f_680_ = stack[5].m_obj;
lean_object* v_alts_681_ = stack[6].m_obj;
lean_object* v_a_682_ = stack[7].m_obj;
lean_object* v_a_683_ = stack[8].m_obj;
lean_object* v_res_1713_;
v_res_1713_ = l_Lean_Elab_Command_elabElabRulesAux(v_doc_x3f_675_, v_attrs_x3f_676_, v_attrKind_677_, v_k_678_, v_cat_x3f_679_, v_expty_x3f_680_, v_alts_681_, v_a_682_, v_a_683_);
stack->m_obj
 = v_res_1713_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object* v_doc_x3f_1714_, lean_object* v_attrs_x3f_1715_, lean_object* v_attrKind_1716_, lean_object* v_k_1717_, lean_object* v_cat_x3f_1718_, lean_object* v_expty_x3f_1719_, lean_object* v_alts_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_Elab_Command_elabElabRulesAux(v_doc_x3f_1714_, v_attrs_x3f_1715_, v_attrKind_1716_, v_k_1717_, v_cat_x3f_1718_, v_expty_x3f_1719_, v_alts_1720_, v_a_1721_, v_a_1722_);
lean_dec(v_a_1722_);
lean_dec_ref(v_a_1721_);
lean_dec(v_cat_x3f_1718_);
lean_dec(v_attrs_x3f_1715_);
return v_res_1724_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(lean_object* v_00_u03b1_1725_, lean_object* v_ref_1726_, lean_object* v_msg_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_1726_, v_msg_1727_, v___y_1728_, v___y_1729_);
return v___x_1731_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1726_ = stack[1].m_obj;
lean_object* v_msg_1727_ = stack[2].m_obj;
lean_object* v___y_1728_ = stack[3].m_obj;
lean_object* v___y_1729_ = stack[4].m_obj;
lean_object* v_res_1732_;
v_res_1732_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(lean_box(0), v_ref_1726_, v_msg_1727_, v___y_1728_, v___y_1729_);
stack->m_obj
 = v_res_1732_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___boxed(lean_object* v_00_u03b1_1733_, lean_object* v_ref_1734_, lean_object* v_msg_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(v_00_u03b1_1733_, v_ref_1734_, v_msg_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v_ref_1734_);
return v_res_1739_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(lean_object* v_msgData_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msgData_1740_, v___y_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1740_ = stack[0].m_obj;
lean_object* v___y_1741_ = stack[1].m_obj;
lean_object* v___y_1742_ = stack[2].m_obj;
lean_object* v_res_1745_;
v_res_1745_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(v_msgData_1740_, v___y_1741_, v___y_1742_);
stack->m_obj
 = v_res_1745_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___boxed(lean_object* v_msgData_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(v_msgData_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
return v_res_1750_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(lean_object* v_00_u03b1_1751_, lean_object* v_msg_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_1752_, v___y_1753_, v___y_1754_);
return v___x_1756_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1752_ = stack[1].m_obj;
lean_object* v___y_1753_ = stack[2].m_obj;
lean_object* v___y_1754_ = stack[3].m_obj;
lean_object* v_res_1757_;
v_res_1757_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(lean_box(0), v_msg_1752_, v___y_1753_, v___y_1754_);
stack->m_obj
 = v_res_1757_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___boxed(lean_object* v_00_u03b1_1758_, lean_object* v_msg_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(v_00_u03b1_1758_, v_msg_1759_, v___y_1760_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
return v_res_1763_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(lean_object* v_msgData_1764_, lean_object* v_macroStack_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_msgData_1764_, v_macroStack_1765_, v___y_1767_);
return v___x_1769_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1764_ = stack[0].m_obj;
lean_object* v_macroStack_1765_ = stack[1].m_obj;
lean_object* v___y_1766_ = stack[2].m_obj;
lean_object* v___y_1767_ = stack[3].m_obj;
lean_object* v_res_1770_;
v_res_1770_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(v_msgData_1764_, v_macroStack_1765_, v___y_1766_, v___y_1767_);
stack->m_obj
 = v_res_1770_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___boxed(lean_object* v_msgData_1771_, lean_object* v_macroStack_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(v_msgData_1771_, v_macroStack_1772_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0(lean_object* v_x_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0___boxed(lean_object* v_x_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_Elab_Command_elabElabRules___lam__0(v_x_1779_);
lean_dec(v_x_1779_);
return v_res_1780_;
}
}
lean_object* l_Lean_Elab_Command_elabElabRules___lam__1(lean_object* v___x_1785_, lean_object* v___x_1786_, lean_object* v_attrKind_1787_, lean_object* v_expty_x3f_1788_, lean_object* v___f_1789_, lean_object* v_cat_x3f_1790_, lean_object* v___x_1791_, lean_object* v___x_1792_, lean_object* v_attrs_x3f_1793_, lean_object* v___x_1794_, lean_object* v___x_1795_, lean_object* v___x_1796_, lean_object* v_doc_x3f_1797_, lean_object* v_kind_x3f_1798_, lean_object* v_alts_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lean_Elab_Command_getRef___redArg(v___y_1800_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1912_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1806_ = v___x_1803_;
v_isShared_1807_ = v_isSharedCheck_1912_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1803_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1912_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
uint8_t v___x_1808_; lean_object* v___x_1809_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___x_1901_; 
v___x_1808_ = 0;
v___x_1809_ = l_Lean_SourceInfo_fromRef(v_a_1804_, v___x_1808_);
lean_dec(v_a_1804_);
v___x_1901_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1800_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_quotContext_x3f_1902_; 
lean_dec_ref_known(v___x_1901_, 1);
v_quotContext_x3f_1902_ = lean_ctor_get(v___y_1800_, 5);
if (lean_obj_tag(v_quotContext_x3f_1902_) == 0)
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1801_);
lean_dec_ref(v___x_1903_);
goto v___jp_1895_;
}
else
{
goto v___jp_1895_;
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v___x_1809_);
lean_del_object(v___x_1806_);
lean_dec(v_kind_x3f_1798_);
lean_dec(v_doc_x3f_1797_);
lean_dec_ref(v___x_1796_);
lean_dec_ref(v___x_1795_);
lean_dec_ref(v___x_1794_);
lean_dec_ref(v___x_1791_);
lean_dec(v_cat_x3f_1790_);
lean_dec_ref(v___f_1789_);
lean_dec(v_expty_x3f_1788_);
lean_dec(v_attrKind_1787_);
lean_dec(v___x_1786_);
lean_dec(v___x_1785_);
v_a_1904_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1901_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1901_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
v___jp_1810_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1826_; 
lean_inc_ref_n(v___y_1812_, 2);
v___x_1819_ = l_Array_append___redArg(v___y_1812_, v___y_1818_);
lean_dec_ref(v___y_1818_);
lean_inc_n(v___y_1816_, 2);
lean_inc_n(v___x_1809_, 3);
v___x_1820_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1809_);
lean_ctor_set(v___x_1820_, 1, v___y_1816_);
lean_ctor_set(v___x_1820_, 2, v___x_1819_);
v___x_1821_ = l_Array_append___redArg(v___y_1812_, v_alts_1799_);
v___x_1822_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1809_);
lean_ctor_set(v___x_1822_, 1, v___y_1816_);
lean_ctor_set(v___x_1822_, 2, v___x_1821_);
v___x_1823_ = l_Lean_Syntax_node1(v___x_1809_, v___x_1785_, v___x_1822_);
v___x_1824_ = l_Lean_Syntax_node8(v___x_1809_, v___x_1786_, v___y_1814_, v___y_1813_, v_attrKind_1787_, v___y_1815_, v___y_1817_, v___y_1811_, v___x_1820_, v___x_1823_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v___x_1824_);
v___x_1826_ = v___x_1806_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
v___jp_1828_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_inc_ref(v___y_1829_);
v___x_1836_ = l_Array_append___redArg(v___y_1829_, v___y_1835_);
lean_dec_ref(v___y_1835_);
lean_inc(v___y_1833_);
lean_inc(v___x_1809_);
v___x_1837_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1809_);
lean_ctor_set(v___x_1837_, 1, v___y_1833_);
lean_ctor_set(v___x_1837_, 2, v___x_1836_);
if (lean_obj_tag(v_expty_x3f_1788_) == 1)
{
lean_object* v_val_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_dec_ref(v___f_1789_);
v_val_1838_ = lean_ctor_get(v_expty_x3f_1788_, 0);
lean_inc(v_val_1838_);
lean_dec_ref_known(v_expty_x3f_1788_, 1);
v___x_1839_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___x_1809_);
v___x_1840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1809_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = l_Array_mkArray2___redArg(v___x_1840_, v_val_1838_);
v___y_1811_ = v___x_1837_;
v___y_1812_ = v___y_1829_;
v___y_1813_ = v___y_1830_;
v___y_1814_ = v___y_1831_;
v___y_1815_ = v___y_1832_;
v___y_1816_ = v___y_1833_;
v___y_1817_ = v___y_1834_;
v___y_1818_ = v___x_1841_;
goto v___jp_1810_;
}
else
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_apply_1(v___f_1789_, v_expty_x3f_1788_);
v___y_1811_ = v___x_1837_;
v___y_1812_ = v___y_1829_;
v___y_1813_ = v___y_1830_;
v___y_1814_ = v___y_1831_;
v___y_1815_ = v___y_1832_;
v___y_1816_ = v___y_1833_;
v___y_1817_ = v___y_1834_;
v___y_1818_ = v___x_1842_;
goto v___jp_1810_;
}
}
v___jp_1843_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_inc_ref(v___y_1844_);
v___x_1850_ = l_Array_append___redArg(v___y_1844_, v___y_1849_);
lean_dec_ref(v___y_1849_);
lean_inc(v___y_1848_);
lean_inc(v___x_1809_);
v___x_1851_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1809_);
lean_ctor_set(v___x_1851_, 1, v___y_1848_);
lean_ctor_set(v___x_1851_, 2, v___x_1850_);
if (lean_obj_tag(v_cat_x3f_1790_) == 1)
{
lean_object* v_val_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v_val_1852_ = lean_ctor_get(v_cat_x3f_1790_, 0);
lean_inc(v_val_1852_);
lean_dec_ref_known(v_cat_x3f_1790_, 1);
v___x_1853_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(v___x_1809_);
v___x_1854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1809_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = l_Array_mkArray2___redArg(v___x_1854_, v_val_1852_);
v___y_1829_ = v___y_1844_;
v___y_1830_ = v___y_1845_;
v___y_1831_ = v___y_1846_;
v___y_1832_ = v___y_1847_;
v___y_1833_ = v___y_1848_;
v___y_1834_ = v___x_1851_;
v___y_1835_ = v___x_1855_;
goto v___jp_1828_;
}
else
{
lean_object* v___x_1856_; 
lean_inc_ref(v___f_1789_);
v___x_1856_ = lean_apply_1(v___f_1789_, v_cat_x3f_1790_);
v___y_1829_ = v___y_1844_;
v___y_1830_ = v___y_1845_;
v___y_1831_ = v___y_1846_;
v___y_1832_ = v___y_1847_;
v___y_1833_ = v___y_1848_;
v___y_1834_ = v___x_1851_;
v___y_1835_ = v___x_1856_;
goto v___jp_1828_;
}
}
v___jp_1857_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_inc_ref(v___y_1858_);
v___x_1862_ = l_Array_append___redArg(v___y_1858_, v___y_1861_);
lean_dec_ref(v___y_1861_);
lean_inc(v___y_1860_);
lean_inc_n(v___x_1809_, 2);
v___x_1863_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1809_);
lean_ctor_set(v___x_1863_, 1, v___y_1860_);
lean_ctor_set(v___x_1863_, 2, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1809_);
lean_ctor_set(v___x_1864_, 1, v___x_1791_);
if (lean_obj_tag(v_kind_x3f_1798_) == 0)
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_mk_empty_array_with_capacity(v___x_1792_);
v___y_1844_ = v___y_1858_;
v___y_1845_ = v___x_1863_;
v___y_1846_ = v___y_1859_;
v___y_1847_ = v___x_1864_;
v___y_1848_ = v___y_1860_;
v___y_1849_ = v___x_1865_;
goto v___jp_1843_;
}
else
{
lean_object* v_val_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v_val_1866_ = lean_ctor_get(v_kind_x3f_1798_, 0);
lean_inc(v_val_1866_);
lean_dec_ref_known(v_kind_x3f_1798_, 1);
v___x_1867_ = l_Lean_mkIdent(v_val_1866_);
v___x_1868_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc_n(v___x_1809_, 4);
v___x_1869_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1809_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__2));
v___x_1871_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1809_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1809_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_1875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1809_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = l_Array_mkArray5___redArg(v___x_1869_, v___x_1871_, v___x_1873_, v___x_1867_, v___x_1875_);
v___y_1844_ = v___y_1858_;
v___y_1845_ = v___x_1863_;
v___y_1846_ = v___y_1859_;
v___y_1847_ = v___x_1864_;
v___y_1848_ = v___y_1860_;
v___y_1849_ = v___x_1876_;
goto v___jp_1843_;
}
}
v___jp_1877_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_inc_ref(v___y_1878_);
v___x_1881_ = l_Array_append___redArg(v___y_1878_, v___y_1880_);
lean_dec_ref(v___y_1880_);
lean_inc(v___y_1879_);
lean_inc(v___x_1809_);
v___x_1882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1809_);
lean_ctor_set(v___x_1882_, 1, v___y_1879_);
lean_ctor_set(v___x_1882_, 2, v___x_1881_);
if (lean_obj_tag(v_attrs_x3f_1793_) == 1)
{
lean_object* v_val_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v_val_1883_ = lean_ctor_get(v_attrs_x3f_1793_, 0);
v___x_1884_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
v___x_1885_ = l_Lean_Name_mkStr4(v___x_1794_, v___x_1795_, v___x_1796_, v___x_1884_);
v___x_1886_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc_n(v___x_1809_, 4);
v___x_1887_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1809_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
lean_inc_ref(v___y_1878_);
v___x_1888_ = l_Array_append___redArg(v___y_1878_, v_val_1883_);
lean_inc(v___y_1879_);
v___x_1889_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1809_);
lean_ctor_set(v___x_1889_, 1, v___y_1879_);
lean_ctor_set(v___x_1889_, 2, v___x_1888_);
v___x_1890_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1891_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1809_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = l_Lean_Syntax_node3(v___x_1809_, v___x_1885_, v___x_1887_, v___x_1889_, v___x_1891_);
v___x_1893_ = l_Array_mkArray1___redArg(v___x_1892_);
v___y_1858_ = v___y_1878_;
v___y_1859_ = v___x_1882_;
v___y_1860_ = v___y_1879_;
v___y_1861_ = v___x_1893_;
goto v___jp_1857_;
}
else
{
lean_object* v___x_1894_; 
lean_dec_ref(v___x_1796_);
lean_dec_ref(v___x_1795_);
lean_dec_ref(v___x_1794_);
v___x_1894_ = lean_mk_empty_array_with_capacity(v___x_1792_);
v___y_1858_ = v___y_1878_;
v___y_1859_ = v___x_1882_;
v___y_1860_ = v___y_1879_;
v___y_1861_ = v___x_1894_;
goto v___jp_1857_;
}
}
v___jp_1895_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1897_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_1797_) == 1)
{
lean_object* v_val_1898_; lean_object* v___x_1899_; 
v_val_1898_ = lean_ctor_get(v_doc_x3f_1797_, 0);
lean_inc(v_val_1898_);
lean_dec_ref_known(v_doc_x3f_1797_, 1);
v___x_1899_ = l_Array_mkArray1___redArg(v_val_1898_);
v___y_1878_ = v___x_1897_;
v___y_1879_ = v___x_1896_;
v___y_1880_ = v___x_1899_;
goto v___jp_1877_;
}
else
{
lean_object* v___x_1900_; 
lean_dec(v_doc_x3f_1797_);
v___x_1900_ = lean_mk_empty_array_with_capacity(v___x_1792_);
v___y_1878_ = v___x_1897_;
v___y_1879_ = v___x_1896_;
v___y_1880_ = v___x_1900_;
goto v___jp_1877_;
}
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec(v_kind_x3f_1798_);
lean_dec(v_doc_x3f_1797_);
lean_dec_ref(v___x_1796_);
lean_dec_ref(v___x_1795_);
lean_dec_ref(v___x_1794_);
lean_dec_ref(v___x_1791_);
lean_dec(v_cat_x3f_1790_);
lean_dec_ref(v___f_1789_);
lean_dec(v_expty_x3f_1788_);
lean_dec(v_attrKind_1787_);
lean_dec(v___x_1786_);
lean_dec(v___x_1785_);
v_a_1913_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1803_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1803_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_elabElabRules___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1785_ = stack[0].m_obj;
lean_object* v___x_1786_ = stack[1].m_obj;
lean_object* v_attrKind_1787_ = stack[2].m_obj;
lean_object* v_expty_x3f_1788_ = stack[3].m_obj;
lean_object* v___f_1789_ = stack[4].m_obj;
lean_object* v_cat_x3f_1790_ = stack[5].m_obj;
lean_object* v___x_1791_ = stack[6].m_obj;
lean_object* v___x_1792_ = stack[7].m_obj;
lean_object* v_attrs_x3f_1793_ = stack[8].m_obj;
lean_object* v___x_1794_ = stack[9].m_obj;
lean_object* v___x_1795_ = stack[10].m_obj;
lean_object* v___x_1796_ = stack[11].m_obj;
lean_object* v_doc_x3f_1797_ = stack[12].m_obj;
lean_object* v_kind_x3f_1798_ = stack[13].m_obj;
lean_object* v_alts_1799_ = stack[14].m_obj;
lean_object* v___y_1800_ = stack[15].m_obj;
lean_object* v___y_1801_ = stack[16].m_obj;
lean_object* v_res_1921_;
v_res_1921_ = l_Lean_Elab_Command_elabElabRules___lam__1(v___x_1785_, v___x_1786_, v_attrKind_1787_, v_expty_x3f_1788_, v___f_1789_, v_cat_x3f_1790_, v___x_1791_, v___x_1792_, v_attrs_x3f_1793_, v___x_1794_, v___x_1795_, v___x_1796_, v_doc_x3f_1797_, v_kind_x3f_1798_, v_alts_1799_, v___y_1800_, v___y_1801_);
stack->m_obj
 = v_res_1921_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___boxed(lean_object** _args){
lean_object* v___x_1922_ = _args[0];
lean_object* v___x_1923_ = _args[1];
lean_object* v_attrKind_1924_ = _args[2];
lean_object* v_expty_x3f_1925_ = _args[3];
lean_object* v___f_1926_ = _args[4];
lean_object* v_cat_x3f_1927_ = _args[5];
lean_object* v___x_1928_ = _args[6];
lean_object* v___x_1929_ = _args[7];
lean_object* v_attrs_x3f_1930_ = _args[8];
lean_object* v___x_1931_ = _args[9];
lean_object* v___x_1932_ = _args[10];
lean_object* v___x_1933_ = _args[11];
lean_object* v_doc_x3f_1934_ = _args[12];
lean_object* v_kind_x3f_1935_ = _args[13];
lean_object* v_alts_1936_ = _args[14];
lean_object* v___y_1937_ = _args[15];
lean_object* v___y_1938_ = _args[16];
lean_object* v___y_1939_ = _args[17];
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_Elab_Command_elabElabRules___lam__1(v___x_1922_, v___x_1923_, v_attrKind_1924_, v_expty_x3f_1925_, v___f_1926_, v_cat_x3f_1927_, v___x_1928_, v___x_1929_, v_attrs_x3f_1930_, v___x_1931_, v___x_1932_, v___x_1933_, v_doc_x3f_1934_, v_kind_x3f_1935_, v_alts_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec_ref(v_alts_1936_);
lean_dec(v_attrs_x3f_1930_);
lean_dec(v___x_1929_);
return v_res_1940_;
}
}
lean_object* l_Lean_Elab_Command_elabElabRules___lam__2(lean_object* v___f_1969_, lean_object* v_stx_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1974_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1975_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1976_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
v___x_1977_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
lean_inc(v_stx_1970_);
v___x_1978_ = l_Lean_Syntax_isOfKind(v_stx_1970_, v___x_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
lean_dec(v_stx_1970_);
lean_dec_ref(v___f_1969_);
v___x_1979_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_1979_;
}
else
{
lean_object* v___x_1980_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v_expty_x3f_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v_cat_x3f_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v_expty_x3f_2037_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v_cat_x3f_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v_attrs_x3f_2086_; lean_object* v_doc_x3f_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_1980_ = lean_unsigned_to_nat(0u);
v___x_2133_ = l_Lean_Syntax_getArg(v_stx_1970_, v___x_1980_);
v___x_2134_ = l_Lean_Syntax_isNone(v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2135_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2133_);
v___x_2136_ = l_Lean_Syntax_matchesNull(v___x_2133_, v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; 
lean_dec(v___x_2133_);
lean_dec(v_stx_1970_);
lean_dec_ref(v___f_1969_);
v___x_2137_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2137_;
}
else
{
lean_object* v_doc_x3f_2138_; 
v_doc_x3f_2138_ = l_Lean_Syntax_getArg(v___x_2133_, v___x_1980_);
lean_dec(v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7));
lean_inc(v_doc_x3f_2138_);
v___x_2142_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2138_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; 
lean_dec(v_doc_x3f_2138_);
lean_dec(v_stx_1970_);
lean_dec_ref(v___f_1969_);
v___x_2143_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2143_;
}
else
{
goto v___jp_2139_;
}
}
else
{
goto v___jp_2139_;
}
v___jp_2139_:
{
lean_object* v___x_2140_; 
v___x_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2140_, 0, v_doc_x3f_2138_);
v_doc_x3f_2117_ = v___x_2140_;
v___y_2118_ = v___y_1971_;
v___y_2119_ = v___y_1972_;
goto v___jp_2116_;
}
}
}
else
{
lean_object* v___x_2144_; 
lean_dec(v___x_2133_);
v___x_2144_ = lean_box(0);
v_doc_x3f_2117_ = v___x_2144_;
v___y_2118_ = v___y_1971_;
v___y_2119_ = v___y_1972_;
goto v___jp_2116_;
}
v___jp_1981_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v___x_1991_ = lean_unsigned_to_nat(7u);
v___x_1992_ = l_Lean_Syntax_getArg(v_stx_1970_, v___x_1991_);
lean_dec(v_stx_1970_);
v___x_1993_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc_ref(v___y_1987_);
v___x_1994_ = l_Lean_Name_mkStr4(v___x_1974_, v___x_1975_, v___y_1987_, v___x_1993_);
lean_inc(v___x_1992_);
v___x_1995_ = l_Lean_Syntax_isOfKind(v___x_1992_, v___x_1994_);
lean_dec(v___x_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; 
lean_dec(v___x_1992_);
lean_dec(v_expty_x3f_1988_);
lean_dec(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec(v___y_1982_);
v___x_1996_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_1996_;
}
else
{
lean_object* v___x_1997_; lean_object* v_alts_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1997_ = l_Lean_Syntax_getArg(v___x_1992_, v___x_1980_);
lean_dec(v___x_1992_);
v_alts_1998_ = l_Lean_Syntax_getArgs(v___x_1997_);
lean_dec(v___x_1997_);
v___x_1999_ = l_Lean_TSyntax_getId(v___y_1983_);
lean_dec(v___y_1983_);
v___x_2000_ = l_Lean_Elab_Command_resolveSyntaxKind(v___x_1999_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2002_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_2000_, 1);
v___x_2002_ = l_Lean_Elab_Command_elabElabRulesAux(v___y_1985_, v___y_1984_, v___y_1982_, v_a_2001_, v___y_1986_, v_expty_x3f_1988_, v_alts_1998_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1986_);
lean_dec(v___y_1984_);
return v___x_2002_;
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_dec_ref(v_alts_1998_);
lean_dec(v_expty_x3f_1988_);
lean_dec(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec(v___y_1982_);
v_a_2003_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_2000_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_2000_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
}
v___jp_2011_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2022_ = lean_unsigned_to_nat(6u);
v___x_2023_ = l_Lean_Syntax_getArg(v_stx_1970_, v___x_2022_);
v___x_2024_ = l_Lean_Syntax_isNone(v___x_2023_);
if (v___x_2024_ == 0)
{
uint8_t v___x_2025_; 
lean_inc(v___x_2023_);
v___x_2025_ = l_Lean_Syntax_matchesNull(v___x_2023_, v___y_2014_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; 
lean_dec(v___x_2023_);
lean_dec(v_cat_x3f_2019_);
lean_dec(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec(v___y_2013_);
lean_dec(v_stx_1970_);
v___x_2026_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2026_;
}
else
{
lean_object* v_expty_x3f_2027_; lean_object* v___x_2028_; 
v_expty_x3f_2027_ = l_Lean_Syntax_getArg(v___x_2023_, v___y_2012_);
lean_dec(v___x_2023_);
v___x_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2028_, 0, v_expty_x3f_2027_);
v___y_1982_ = v___y_2013_;
v___y_1983_ = v___y_2015_;
v___y_1984_ = v___y_2017_;
v___y_1985_ = v___y_2016_;
v___y_1986_ = v_cat_x3f_2019_;
v___y_1987_ = v___y_2018_;
v_expty_x3f_1988_ = v___x_2028_;
v___y_1989_ = v___y_2020_;
v___y_1990_ = v___y_2021_;
goto v___jp_1981_;
}
}
else
{
lean_object* v___x_2029_; 
lean_dec(v___x_2023_);
v___x_2029_ = lean_box(0);
v___y_1982_ = v___y_2013_;
v___y_1983_ = v___y_2015_;
v___y_1984_ = v___y_2017_;
v___y_1985_ = v___y_2016_;
v___y_1986_ = v_cat_x3f_2019_;
v___y_1987_ = v___y_2018_;
v_expty_x3f_1988_ = v___x_2029_;
v___y_1989_ = v___y_2020_;
v___y_1990_ = v___y_2021_;
goto v___jp_1981_;
}
}
v___jp_2030_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
v___x_2038_ = lean_unsigned_to_nat(7u);
v___x_2039_ = l_Lean_Syntax_getArg(v_stx_1970_, v___x_2038_);
lean_dec(v_stx_1970_);
v___x_2040_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_2041_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__2));
lean_inc(v___x_2039_);
v___x_2042_ = l_Lean_Syntax_isOfKind(v___x_2039_, v___x_2041_);
if (v___x_2042_ == 0)
{
lean_object* v___x_2043_; 
lean_dec(v___x_2039_);
lean_dec(v_expty_x3f_2037_);
lean_dec(v___y_2036_);
lean_dec(v___y_2034_);
lean_dec(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___f_1969_);
v___x_2043_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2043_;
}
else
{
lean_object* v___f_2044_; lean_object* v___x_2045_; lean_object* v_alts_2046_; lean_object* v___x_2047_; 
v___f_2044_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___lam__1___boxed), 18, 13);
lean_closure_set(v___f_2044_, 0, v___x_2041_);
lean_closure_set(v___f_2044_, 1, v___x_1977_);
lean_closure_set(v___f_2044_, 2, v___y_2036_);
lean_closure_set(v___f_2044_, 3, v_expty_x3f_2037_);
lean_closure_set(v___f_2044_, 4, v___f_1969_);
lean_closure_set(v___f_2044_, 5, v___y_2034_);
lean_closure_set(v___f_2044_, 6, v___x_1976_);
lean_closure_set(v___f_2044_, 7, v___x_1980_);
lean_closure_set(v___f_2044_, 8, v___y_2031_);
lean_closure_set(v___f_2044_, 9, v___x_1974_);
lean_closure_set(v___f_2044_, 10, v___x_1975_);
lean_closure_set(v___f_2044_, 11, v___x_2040_);
lean_closure_set(v___f_2044_, 12, v___y_2032_);
v___x_2045_ = l_Lean_Syntax_getArg(v___x_2039_, v___x_1980_);
lean_dec(v___x_2039_);
v_alts_2046_ = l_Lean_Syntax_getArgs(v___x_2045_);
lean_dec(v___x_2045_);
v___x_2047_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(v_alts_2046_, v___x_1976_, v___f_2044_, v___y_2033_, v___y_2035_);
lean_dec_ref(v_alts_2046_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2047_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2047_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
v_a_2056_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2047_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2047_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
v___jp_2064_:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2073_ = lean_unsigned_to_nat(6u);
v___x_2074_ = l_Lean_Syntax_getArg(v_stx_1970_, v___x_2073_);
v___x_2075_ = l_Lean_Syntax_isNone(v___x_2074_);
if (v___x_2075_ == 0)
{
uint8_t v___x_2076_; 
lean_inc(v___x_2074_);
v___x_2076_ = l_Lean_Syntax_matchesNull(v___x_2074_, v___y_2069_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; 
lean_dec(v___x_2074_);
lean_dec(v_cat_x3f_2070_);
lean_dec(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec(v_stx_1970_);
lean_dec_ref(v___f_1969_);
v___x_2077_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2077_;
}
else
{
lean_object* v_expty_x3f_2078_; lean_object* v___x_2079_; 
v_expty_x3f_2078_ = l_Lean_Syntax_getArg(v___x_2074_, v___y_2068_);
lean_dec(v___x_2074_);
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v_expty_x3f_2078_);
v___y_2031_ = v___y_2065_;
v___y_2032_ = v___y_2066_;
v___y_2033_ = v___y_2071_;
v___y_2034_ = v_cat_x3f_2070_;
v___y_2035_ = v___y_2072_;
v___y_2036_ = v___y_2067_;
v_expty_x3f_2037_ = v___x_2079_;
goto v___jp_2030_;
}
}
else
{
lean_object* v___x_2080_; 
lean_dec(v___x_2074_);
v___x_2080_ = lean_box(0);
v___y_2031_ = v___y_2065_;
v___y_2032_ = v___y_2066_;
v___y_2033_ = v___y_2071_;
v___y_2034_ = v_cat_x3f_2070_;
v___y_2035_ = v___y_2072_;
v___y_2036_ = v___y_2067_;
v_expty_x3f_2037_ = v___x_2080_;
goto v___jp_2030_;
}
}
v___jp_2081_:
{
lean_object* v___x_2087_; lean_object* v_attrKind_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2087_ = lean_unsigned_to_nat(2u);
v_attrKind_2088_ = l_Lean_Syntax_getArg(v_stx_1970_, v___x_2087_);
v___x_2089_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_2090_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v_attrKind_2088_);
v___x_2091_ = l_Lean_Syntax_isOfKind(v_attrKind_2088_, v___x_2090_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; 
lean_dec(v_attrKind_2088_);
lean_dec(v_attrs_x3f_2086_);
lean_dec(v___y_2083_);
lean_dec(v_stx_1970_);
lean_dec_ref(v___f_1969_);
v___x_2092_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2092_;
}
else
{
lean_object* v___x_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_2093_ = lean_unsigned_to_nat(4u);
v___x_2094_ = l_Lean_Syntax_getArg(v_stx_1970_, v___x_2093_);
lean_inc(v___x_2094_);
v___x_2095_ = l_Lean_Syntax_matchesNull(v___x_2094_, v___x_1980_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; uint8_t v___x_2097_; 
lean_dec_ref(v___f_1969_);
v___x_2096_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2094_);
v___x_2097_ = l_Lean_Syntax_matchesNull(v___x_2094_, v___x_2096_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; 
lean_dec(v___x_2094_);
lean_dec(v_attrKind_2088_);
lean_dec(v_attrs_x3f_2086_);
lean_dec(v___y_2083_);
lean_dec(v_stx_1970_);
v___x_2098_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2098_;
}
else
{
lean_object* v___x_2099_; lean_object* v_kind_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2099_ = lean_unsigned_to_nat(3u);
v_kind_2100_ = l_Lean_Syntax_getArg(v___x_2094_, v___x_2099_);
lean_dec(v___x_2094_);
v___x_2101_ = l_Lean_Syntax_getArg(v_stx_1970_, v___x_2096_);
v___x_2102_ = l_Lean_Syntax_isNone(v___x_2101_);
if (v___x_2102_ == 0)
{
uint8_t v___x_2103_; 
lean_inc(v___x_2101_);
v___x_2103_ = l_Lean_Syntax_matchesNull(v___x_2101_, v___x_2087_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; 
lean_dec(v___x_2101_);
lean_dec(v_kind_2100_);
lean_dec(v_attrKind_2088_);
lean_dec(v_attrs_x3f_2086_);
lean_dec(v___y_2083_);
lean_dec(v_stx_1970_);
v___x_2104_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2104_;
}
else
{
lean_object* v_cat_x3f_2105_; lean_object* v___x_2106_; 
v_cat_x3f_2105_ = l_Lean_Syntax_getArg(v___x_2101_, v___y_2085_);
lean_dec(v___x_2101_);
v___x_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2106_, 0, v_cat_x3f_2105_);
v___y_2012_ = v___y_2085_;
v___y_2013_ = v_attrKind_2088_;
v___y_2014_ = v___x_2087_;
v___y_2015_ = v_kind_2100_;
v___y_2016_ = v___y_2083_;
v___y_2017_ = v_attrs_x3f_2086_;
v___y_2018_ = v___x_2089_;
v_cat_x3f_2019_ = v___x_2106_;
v___y_2020_ = v___y_2084_;
v___y_2021_ = v___y_2082_;
goto v___jp_2011_;
}
}
else
{
lean_object* v___x_2107_; 
lean_dec(v___x_2101_);
v___x_2107_ = lean_box(0);
v___y_2012_ = v___y_2085_;
v___y_2013_ = v_attrKind_2088_;
v___y_2014_ = v___x_2087_;
v___y_2015_ = v_kind_2100_;
v___y_2016_ = v___y_2083_;
v___y_2017_ = v_attrs_x3f_2086_;
v___y_2018_ = v___x_2089_;
v_cat_x3f_2019_ = v___x_2107_;
v___y_2020_ = v___y_2084_;
v___y_2021_ = v___y_2082_;
goto v___jp_2011_;
}
}
}
else
{
lean_object* v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; 
lean_dec(v___x_2094_);
v___x_2108_ = lean_unsigned_to_nat(5u);
v___x_2109_ = l_Lean_Syntax_getArg(v_stx_1970_, v___x_2108_);
v___x_2110_ = l_Lean_Syntax_isNone(v___x_2109_);
if (v___x_2110_ == 0)
{
uint8_t v___x_2111_; 
lean_inc(v___x_2109_);
v___x_2111_ = l_Lean_Syntax_matchesNull(v___x_2109_, v___x_2087_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; 
lean_dec(v___x_2109_);
lean_dec(v_attrKind_2088_);
lean_dec(v_attrs_x3f_2086_);
lean_dec(v___y_2083_);
lean_dec(v_stx_1970_);
lean_dec_ref(v___f_1969_);
v___x_2112_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2112_;
}
else
{
lean_object* v_cat_x3f_2113_; lean_object* v___x_2114_; 
v_cat_x3f_2113_ = l_Lean_Syntax_getArg(v___x_2109_, v___y_2085_);
lean_dec(v___x_2109_);
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v_cat_x3f_2113_);
v___y_2065_ = v_attrs_x3f_2086_;
v___y_2066_ = v___y_2083_;
v___y_2067_ = v_attrKind_2088_;
v___y_2068_ = v___y_2085_;
v___y_2069_ = v___x_2087_;
v_cat_x3f_2070_ = v___x_2114_;
v___y_2071_ = v___y_2084_;
v___y_2072_ = v___y_2082_;
goto v___jp_2064_;
}
}
else
{
lean_object* v___x_2115_; 
lean_dec(v___x_2109_);
v___x_2115_ = lean_box(0);
v___y_2065_ = v_attrs_x3f_2086_;
v___y_2066_ = v___y_2083_;
v___y_2067_ = v_attrKind_2088_;
v___y_2068_ = v___y_2085_;
v___y_2069_ = v___x_2087_;
v_cat_x3f_2070_ = v___x_2115_;
v___y_2071_ = v___y_2084_;
v___y_2072_ = v___y_2082_;
goto v___jp_2064_;
}
}
}
}
v___jp_2116_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2120_ = lean_unsigned_to_nat(1u);
v___x_2121_ = l_Lean_Syntax_getArg(v_stx_1970_, v___x_2120_);
v___x_2122_ = l_Lean_Syntax_isNone(v___x_2121_);
if (v___x_2122_ == 0)
{
uint8_t v___x_2123_; 
lean_inc(v___x_2121_);
v___x_2123_ = l_Lean_Syntax_matchesNull(v___x_2121_, v___x_2120_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; 
lean_dec(v___x_2121_);
lean_dec(v_doc_x3f_2117_);
lean_dec(v_stx_1970_);
lean_dec_ref(v___f_1969_);
v___x_2124_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2124_;
}
else
{
lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2125_ = l_Lean_Syntax_getArg(v___x_2121_, v___x_1980_);
lean_dec(v___x_2121_);
v___x_2126_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5));
lean_inc(v___x_2125_);
v___x_2127_ = l_Lean_Syntax_isOfKind(v___x_2125_, v___x_2126_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; 
lean_dec(v___x_2125_);
lean_dec(v_doc_x3f_2117_);
lean_dec(v_stx_1970_);
lean_dec_ref(v___f_1969_);
v___x_2128_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; lean_object* v_attrs_x3f_2130_; lean_object* v___x_2131_; 
v___x_2129_ = l_Lean_Syntax_getArg(v___x_2125_, v___x_2120_);
lean_dec(v___x_2125_);
v_attrs_x3f_2130_ = l_Lean_Syntax_getArgs(v___x_2129_);
lean_dec(v___x_2129_);
v___x_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2131_, 0, v_attrs_x3f_2130_);
v___y_2082_ = v___y_2119_;
v___y_2083_ = v_doc_x3f_2117_;
v___y_2084_ = v___y_2118_;
v___y_2085_ = v___x_2120_;
v_attrs_x3f_2086_ = v___x_2131_;
goto v___jp_2081_;
}
}
}
else
{
lean_object* v___x_2132_; 
lean_dec(v___x_2121_);
v___x_2132_ = lean_box(0);
v___y_2082_ = v___y_2119_;
v___y_2083_ = v_doc_x3f_2117_;
v___y_2084_ = v___y_2118_;
v___y_2085_ = v___x_2120_;
v_attrs_x3f_2086_ = v___x_2132_;
goto v___jp_2081_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_elabElabRules___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1969_ = stack[0].m_obj;
lean_object* v_stx_1970_ = stack[1].m_obj;
lean_object* v___y_1971_ = stack[2].m_obj;
lean_object* v___y_1972_ = stack[3].m_obj;
lean_object* v_res_2145_;
v_res_2145_ = l_Lean_Elab_Command_elabElabRules___lam__2(v___f_1969_, v_stx_1970_, v___y_1971_, v___y_1972_);
stack->m_obj
 = v_res_2145_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___boxed(lean_object* v___f_2146_, lean_object* v_stx_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Lean_Elab_Command_elabElabRules___lam__2(v___f_2146_, v_stx_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
return v_res_2151_;
}
}
lean_object* l_Lean_Elab_Command_elabElabRules(lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_){
_start:
{
lean_object* v___f_2159_; lean_object* v___x_2160_; 
v___f_2159_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___closed__1));
v___x_2160_ = l_Lean_Elab_Command_adaptExpander(v___f_2159_, v_a_2155_, v_a_2156_, v_a_2157_);
return v___x_2160_;
}
}
LEAN_EXPORT void l_Lean_Elab_Command_elabElabRules_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2155_ = stack[0].m_obj;
lean_object* v_a_2156_ = stack[1].m_obj;
lean_object* v_a_2157_ = stack[2].m_obj;
lean_object* v_res_2161_;
v_res_2161_ = l_Lean_Elab_Command_elabElabRules(v_a_2155_, v_a_2156_, v_a_2157_);
stack->m_obj
 = v_res_2161_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___boxed(lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_Elab_Command_elabElabRules(v_a_2162_, v_a_2163_, v_a_2164_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
return v_res_2166_;
}
}
lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1(){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2174_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2175_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
v___x_2176_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2177_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___boxed), 4, 0);
v___x_2178_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2174_, v___x_2175_, v___x_2176_, v___x_2177_);
return v___x_2178_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2179_;
v_res_2179_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
stack->m_obj
 = v_res_2179_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___boxed(lean_object* v_a_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
return v_res_2181_;
}
}
lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3(){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2208_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2209_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6));
v___x_2210_ = l_Lean_addBuiltinDeclarationRanges(v___x_2208_, v___x_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2211_;
v_res_2211_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
stack->m_obj
 = v_res_2211_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___boxed(lean_object* v_a_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
return v_res_2213_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(size_t v_sz_2214_, size_t v_i_2215_, lean_object* v_bs_2216_){
_start:
{
uint8_t v___x_2217_; 
v___x_2217_ = lean_usize_dec_lt(v_i_2215_, v_sz_2214_);
if (v___x_2217_ == 0)
{
return v_bs_2216_;
}
else
{
lean_object* v_v_2218_; lean_object* v___x_2219_; lean_object* v_bs_x27_2220_; size_t v___x_2221_; size_t v___x_2222_; lean_object* v___x_2223_; 
v_v_2218_ = lean_array_uget(v_bs_2216_, v_i_2215_);
v___x_2219_ = lean_unsigned_to_nat(0u);
v_bs_x27_2220_ = lean_array_uset(v_bs_2216_, v_i_2215_, v___x_2219_);
v___x_2221_ = ((size_t)1ULL);
v___x_2222_ = lean_usize_add(v_i_2215_, v___x_2221_);
v___x_2223_ = lean_array_uset(v_bs_x27_2220_, v_i_2215_, v_v_2218_);
v_i_2215_ = v___x_2222_;
v_bs_2216_ = v___x_2223_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2214_ = stack[0].m_num;
size_t v_i_2215_ = stack[1].m_num;
lean_object* v_bs_2216_ = stack[2].m_obj;
lean_object* v_res_2225_;
v_res_2225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_2214_, v_i_2215_, v_bs_2216_);
stack->m_obj
 = v_res_2225_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2___boxed(lean_object* v_sz_2226_, lean_object* v_i_2227_, lean_object* v_bs_2228_){
_start:
{
size_t v_sz_boxed_2229_; size_t v_i_boxed_2230_; lean_object* v_res_2231_; 
v_sz_boxed_2229_ = lean_unbox_usize(v_sz_2226_);
lean_dec(v_sz_2226_);
v_i_boxed_2230_ = lean_unbox_usize(v_i_2227_);
lean_dec(v_i_2227_);
v_res_2231_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_boxed_2229_, v_i_boxed_2230_, v_bs_2228_);
return v_res_2231_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(size_t v_sz_2232_, size_t v_i_2233_, lean_object* v_bs_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
uint8_t v___x_2238_; 
v___x_2238_ = lean_usize_dec_lt(v_i_2233_, v_sz_2232_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; 
v___x_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2239_, 0, v_bs_2234_);
return v___x_2239_;
}
else
{
lean_object* v_v_2240_; lean_object* v___x_2241_; lean_object* v_bs_x27_2242_; lean_object* v___x_2243_; 
v_v_2240_ = lean_array_uget(v_bs_2234_, v_i_2233_);
v___x_2241_ = lean_unsigned_to_nat(0u);
v_bs_x27_2242_ = lean_array_uset(v_bs_2234_, v_i_2233_, v___x_2241_);
v___x_2243_ = l_Lean_Elab_Command_expandMacroArg(v_v_2240_, v___y_2235_, v___y_2236_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; size_t v___x_2245_; size_t v___x_2246_; lean_object* v___x_2247_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2244_);
lean_dec_ref_known(v___x_2243_, 1);
v___x_2245_ = ((size_t)1ULL);
v___x_2246_ = lean_usize_add(v_i_2233_, v___x_2245_);
v___x_2247_ = lean_array_uset(v_bs_x27_2242_, v_i_2233_, v_a_2244_);
v_i_2233_ = v___x_2246_;
v_bs_2234_ = v___x_2247_;
goto _start;
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_dec_ref(v_bs_x27_2242_);
v_a_2249_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2243_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2243_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2232_ = stack[0].m_num;
size_t v_i_2233_ = stack[1].m_num;
lean_object* v_bs_2234_ = stack[2].m_obj;
lean_object* v___y_2235_ = stack[3].m_obj;
lean_object* v___y_2236_ = stack[4].m_obj;
lean_object* v_res_2257_;
v_res_2257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_2232_, v_i_2233_, v_bs_2234_, v___y_2235_, v___y_2236_);
stack->m_obj
 = v_res_2257_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1___boxed(lean_object* v_sz_2258_, lean_object* v_i_2259_, lean_object* v_bs_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
size_t v_sz_boxed_2264_; size_t v_i_boxed_2265_; lean_object* v_res_2266_; 
v_sz_boxed_2264_ = lean_unbox_usize(v_sz_2258_);
lean_dec(v_sz_2258_);
v_i_boxed_2265_ = lean_unbox_usize(v_i_2259_);
lean_dec(v_i_2259_);
v_res_2266_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_boxed_2264_, v_i_boxed_2265_, v_bs_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
return v_res_2266_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(lean_object* v_keys_2267_, lean_object* v_i_2268_, lean_object* v_k_2269_){
_start:
{
lean_object* v___x_2270_; uint8_t v___x_2271_; 
v___x_2270_ = lean_array_get_size(v_keys_2267_);
v___x_2271_ = lean_nat_dec_lt(v_i_2268_, v___x_2270_);
if (v___x_2271_ == 0)
{
lean_dec(v_i_2268_);
return v___x_2271_;
}
else
{
lean_object* v_k_x27_2272_; uint8_t v___x_2273_; 
v_k_x27_2272_ = lean_array_fget_borrowed(v_keys_2267_, v_i_2268_);
v___x_2273_ = l_Lean_instBEqExtraModUse_beq(v_k_2269_, v_k_x27_2272_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = lean_unsigned_to_nat(1u);
v___x_2275_ = lean_nat_add(v_i_2268_, v___x_2274_);
lean_dec(v_i_2268_);
v_i_2268_ = v___x_2275_;
goto _start;
}
else
{
lean_dec(v_i_2268_);
return v___x_2271_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2267_ = stack[0].m_obj;
lean_object* v_i_2268_ = stack[1].m_obj;
lean_object* v_k_2269_ = stack[2].m_obj;
uint8_t v_res_2277_;
v_res_2277_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_2267_, v_i_2268_, v_k_2269_);
stack->m_num = v_res_2277_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_keys_2278_, lean_object* v_i_2279_, lean_object* v_k_2280_){
_start:
{
uint8_t v_res_2281_; lean_object* v_r_2282_; 
v_res_2281_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_2278_, v_i_2279_, v_k_2280_);
lean_dec_ref(v_k_2280_);
lean_dec_ref(v_keys_2278_);
v_r_2282_ = lean_box(v_res_2281_);
return v_r_2282_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(lean_object* v_x_2283_, size_t v_x_2284_, lean_object* v_x_2285_){
_start:
{
if (lean_obj_tag(v_x_2283_) == 0)
{
lean_object* v_es_2286_; lean_object* v___x_2287_; size_t v___x_2288_; size_t v___x_2289_; lean_object* v_j_2290_; lean_object* v___x_2291_; 
v_es_2286_ = lean_ctor_get(v_x_2283_, 0);
v___x_2287_ = lean_box(2);
v___x_2288_ = ((size_t)31ULL);
v___x_2289_ = lean_usize_land(v_x_2284_, v___x_2288_);
v_j_2290_ = lean_usize_to_nat(v___x_2289_);
v___x_2291_ = lean_array_get_borrowed(v___x_2287_, v_es_2286_, v_j_2290_);
lean_dec(v_j_2290_);
switch(lean_obj_tag(v___x_2291_))
{
case 0:
{
lean_object* v_key_2292_; uint8_t v___x_2293_; 
v_key_2292_ = lean_ctor_get(v___x_2291_, 0);
v___x_2293_ = l_Lean_instBEqExtraModUse_beq(v_x_2285_, v_key_2292_);
return v___x_2293_;
}
case 1:
{
lean_object* v_node_2294_; size_t v___x_2295_; size_t v___x_2296_; 
v_node_2294_ = lean_ctor_get(v___x_2291_, 0);
v___x_2295_ = ((size_t)5ULL);
v___x_2296_ = lean_usize_shift_right(v_x_2284_, v___x_2295_);
v_x_2283_ = v_node_2294_;
v_x_2284_ = v___x_2296_;
goto _start;
}
default: 
{
uint8_t v___x_2298_; 
v___x_2298_ = 0;
return v___x_2298_;
}
}
}
else
{
lean_object* v_ks_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; 
v_ks_2299_ = lean_ctor_get(v_x_2283_, 0);
v___x_2300_ = lean_unsigned_to_nat(0u);
v___x_2301_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_ks_2299_, v___x_2300_, v_x_2285_);
return v___x_2301_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2283_ = stack[0].m_obj;
size_t v_x_2284_ = stack[1].m_num;
lean_object* v_x_2285_ = stack[2].m_obj;
uint8_t v_res_2302_;
v_res_2302_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2283_, v_x_2284_, v_x_2285_);
stack->m_num = v_res_2302_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_x_2303_, lean_object* v_x_2304_, lean_object* v_x_2305_){
_start:
{
size_t v_x_16618__boxed_2306_; uint8_t v_res_2307_; lean_object* v_r_2308_; 
v_x_16618__boxed_2306_ = lean_unbox_usize(v_x_2304_);
lean_dec(v_x_2304_);
v_res_2307_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2303_, v_x_16618__boxed_2306_, v_x_2305_);
lean_dec_ref(v_x_2305_);
lean_dec_ref(v_x_2303_);
v_r_2308_ = lean_box(v_res_2307_);
return v_r_2308_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(lean_object* v_x_2309_, lean_object* v_x_2310_){
_start:
{
uint64_t v___x_2311_; size_t v___x_2312_; uint8_t v___x_2313_; 
v___x_2311_ = l_Lean_instHashableExtraModUse_hash(v_x_2310_);
v___x_2312_ = lean_uint64_to_usize(v___x_2311_);
v___x_2313_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2309_, v___x_2312_, v_x_2310_);
return v___x_2313_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2309_ = stack[0].m_obj;
lean_object* v_x_2310_ = stack[1].m_obj;
uint8_t v_res_2314_;
v_res_2314_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_2309_, v_x_2310_);
stack->m_num = v_res_2314_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_x_2315_, lean_object* v_x_2316_){
_start:
{
uint8_t v_res_2317_; lean_object* v_r_2318_; 
v_res_2317_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_2315_, v_x_2316_);
lean_dec_ref(v_x_2316_);
lean_dec_ref(v_x_2315_);
v_r_2318_ = lean_box(v_res_2317_);
return v_r_2318_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2319_; double v___x_2320_; 
v___x_2319_ = lean_unsigned_to_nat(0u);
v___x_2320_ = lean_float_of_nat(v___x_2319_);
return v___x_2320_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(lean_object* v_cls_2324_, lean_object* v_msg_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_Elab_Command_getRef___redArg(v___y_2326_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2331_; lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2380_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2329_, 1);
v___x_2331_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msg_2325_, v___y_2327_);
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2334_ = v___x_2331_;
v_isShared_2335_ = v_isSharedCheck_2380_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2331_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2380_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2336_; lean_object* v_traceState_2337_; lean_object* v_env_2338_; lean_object* v_messages_2339_; lean_object* v_scopes_2340_; lean_object* v_usedQuotCtxts_2341_; lean_object* v_nextMacroScope_2342_; lean_object* v_maxRecDepth_2343_; lean_object* v_ngen_2344_; lean_object* v_auxDeclNGen_2345_; lean_object* v_infoState_2346_; lean_object* v_snapshotTasks_2347_; lean_object* v_prevLinterStates_2348_; lean_object* v_codeQualityEntryTasks_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2379_; 
v___x_2336_ = lean_st_ref_take(v___y_2327_);
v_traceState_2337_ = lean_ctor_get(v___x_2336_, 9);
v_env_2338_ = lean_ctor_get(v___x_2336_, 0);
v_messages_2339_ = lean_ctor_get(v___x_2336_, 1);
v_scopes_2340_ = lean_ctor_get(v___x_2336_, 2);
v_usedQuotCtxts_2341_ = lean_ctor_get(v___x_2336_, 3);
v_nextMacroScope_2342_ = lean_ctor_get(v___x_2336_, 4);
v_maxRecDepth_2343_ = lean_ctor_get(v___x_2336_, 5);
v_ngen_2344_ = lean_ctor_get(v___x_2336_, 6);
v_auxDeclNGen_2345_ = lean_ctor_get(v___x_2336_, 7);
v_infoState_2346_ = lean_ctor_get(v___x_2336_, 8);
v_snapshotTasks_2347_ = lean_ctor_get(v___x_2336_, 10);
v_prevLinterStates_2348_ = lean_ctor_get(v___x_2336_, 11);
v_codeQualityEntryTasks_2349_ = lean_ctor_get(v___x_2336_, 12);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2351_ = v___x_2336_;
v_isShared_2352_ = v_isSharedCheck_2379_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2349_);
lean_inc(v_prevLinterStates_2348_);
lean_inc(v_snapshotTasks_2347_);
lean_inc(v_traceState_2337_);
lean_inc(v_infoState_2346_);
lean_inc(v_auxDeclNGen_2345_);
lean_inc(v_ngen_2344_);
lean_inc(v_maxRecDepth_2343_);
lean_inc(v_nextMacroScope_2342_);
lean_inc(v_usedQuotCtxts_2341_);
lean_inc(v_scopes_2340_);
lean_inc(v_messages_2339_);
lean_inc(v_env_2338_);
lean_dec(v___x_2336_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2379_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
uint64_t v_tid_2353_; lean_object* v_traces_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2378_; 
v_tid_2353_ = lean_ctor_get_uint64(v_traceState_2337_, sizeof(void*)*1);
v_traces_2354_ = lean_ctor_get(v_traceState_2337_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_traceState_2337_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2356_ = v_traceState_2337_;
v_isShared_2357_ = v_isSharedCheck_2378_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_traces_2354_);
lean_dec(v_traceState_2337_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2378_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; double v___x_2360_; uint8_t v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2358_ = lean_box(0);
v___x_2359_ = lean_box(0);
v___x_2360_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0);
v___x_2361_ = 0;
v___x_2362_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1));
v___x_2363_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2363_, 0, v_cls_2324_);
lean_ctor_set(v___x_2363_, 1, v___x_2359_);
lean_ctor_set(v___x_2363_, 2, v___x_2362_);
lean_ctor_set_float(v___x_2363_, sizeof(void*)*3, v___x_2360_);
lean_ctor_set_float(v___x_2363_, sizeof(void*)*3 + 8, v___x_2360_);
lean_ctor_set_uint8(v___x_2363_, sizeof(void*)*3 + 16, v___x_2361_);
v___x_2364_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2));
v___x_2365_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2363_);
lean_ctor_set(v___x_2365_, 1, v_a_2332_);
lean_ctor_set(v___x_2365_, 2, v___x_2364_);
v___x_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2366_, 0, v_a_2330_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = l_Lean_PersistentArray_push___redArg(v_traces_2354_, v___x_2366_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v___x_2367_);
v___x_2369_ = v___x_2356_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2367_);
lean_ctor_set_uint64(v_reuseFailAlloc_2377_, sizeof(void*)*1, v_tid_2353_);
v___x_2369_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2371_; 
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 9, v___x_2369_);
v___x_2371_ = v___x_2351_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_env_2338_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v_messages_2339_);
lean_ctor_set(v_reuseFailAlloc_2376_, 2, v_scopes_2340_);
lean_ctor_set(v_reuseFailAlloc_2376_, 3, v_usedQuotCtxts_2341_);
lean_ctor_set(v_reuseFailAlloc_2376_, 4, v_nextMacroScope_2342_);
lean_ctor_set(v_reuseFailAlloc_2376_, 5, v_maxRecDepth_2343_);
lean_ctor_set(v_reuseFailAlloc_2376_, 6, v_ngen_2344_);
lean_ctor_set(v_reuseFailAlloc_2376_, 7, v_auxDeclNGen_2345_);
lean_ctor_set(v_reuseFailAlloc_2376_, 8, v_infoState_2346_);
lean_ctor_set(v_reuseFailAlloc_2376_, 9, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2376_, 10, v_snapshotTasks_2347_);
lean_ctor_set(v_reuseFailAlloc_2376_, 11, v_prevLinterStates_2348_);
lean_ctor_set(v_reuseFailAlloc_2376_, 12, v_codeQualityEntryTasks_2349_);
v___x_2371_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2372_; lean_object* v___x_2374_; 
v___x_2372_ = lean_st_ref_put(v___y_2327_, v___x_2371_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v___x_2358_);
v___x_2374_ = v___x_2334_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2358_);
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
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec_ref(v_msg_2325_);
lean_dec(v_cls_2324_);
v_a_2381_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2329_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2329_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2324_ = stack[0].m_obj;
lean_object* v_msg_2325_ = stack[1].m_obj;
lean_object* v___y_2326_ = stack[2].m_obj;
lean_object* v___y_2327_ = stack[3].m_obj;
lean_object* v_res_2389_;
v_res_2389_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_2324_, v_msg_2325_, v___y_2326_, v___y_2327_);
stack->m_obj
 = v_res_2389_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___boxed(lean_object* v_cls_2390_, lean_object* v_msg_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_2390_, v_msg_2391_, v___y_2392_, v___y_2393_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___lam__0(lean_object* v___x_2396_, lean_object* v_entry_2397_, lean_object* v_s_2398_){
_start:
{
lean_object* v_addEntryFn_2399_; lean_object* v_importedEntries_2400_; lean_object* v_state_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2409_; 
v_addEntryFn_2399_ = lean_ctor_get(v___x_2396_, 3);
lean_inc(v_addEntryFn_2399_);
lean_dec_ref(v___x_2396_);
v_importedEntries_2400_ = lean_ctor_get(v_s_2398_, 0);
v_state_2401_ = lean_ctor_get(v_s_2398_, 1);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_s_2398_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2403_ = v_s_2398_;
v_isShared_2404_ = v_isSharedCheck_2409_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_state_2401_);
lean_inc(v_importedEntries_2400_);
lean_dec(v_s_2398_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2409_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v_state_2405_; lean_object* v___x_2407_; 
v_state_2405_ = lean_apply_2(v_addEntryFn_2399_, v_state_2401_, v_entry_2397_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 1, v_state_2405_);
v___x_2407_ = v___x_2403_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_importedEntries_2400_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v_state_2405_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2410_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3));
v___x_2416_ = l_Lean_stringToMessageData(v___x_2415_);
return v___x_2416_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5));
v___x_2419_ = l_Lean_stringToMessageData(v___x_2418_);
return v___x_2419_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1));
v___x_2421_ = l_Lean_stringToMessageData(v___x_2420_);
return v___x_2421_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v_cls_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v_cls_2425_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2));
v___x_2426_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9));
v___x_2427_ = l_Lean_Name_append(v___x_2426_, v_cls_2425_);
return v___x_2427_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2429_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11));
v___x_2430_ = l_Lean_stringToMessageData(v___x_2429_);
return v___x_2430_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13));
v___x_2433_ = l_Lean_stringToMessageData(v___x_2432_);
return v___x_2433_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(lean_object* v_mod_2438_, uint8_t v_isMeta_2439_, lean_object* v_hint_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v_env_2465_; uint8_t v_isExporting_2466_; lean_object* v_entry_2467_; lean_object* v___x_2468_; lean_object* v_env_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; uint8_t v___x_2474_; 
v___x_2463_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0);
v___x_2464_ = lean_st_ref_get(v___y_2442_);
v_env_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc_ref(v_env_2465_);
lean_dec(v___x_2464_);
v_isExporting_2466_ = lean_ctor_get_uint8(v_env_2465_, sizeof(void*)*13);
lean_dec_ref(v_env_2465_);
lean_inc(v_mod_2438_);
v_entry_2467_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2467_, 0, v_mod_2438_);
lean_ctor_set_uint8(v_entry_2467_, sizeof(void*)*1, v_isExporting_2466_);
lean_ctor_set_uint8(v_entry_2467_, sizeof(void*)*1 + 1, v_isMeta_2439_);
v___x_2468_ = lean_st_ref_get(v___y_2442_);
v_env_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc_ref(v_env_2469_);
lean_dec(v___x_2468_);
v___x_2470_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2471_ = lean_box(1);
v___x_2472_ = lean_box(0);
v___x_2473_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2463_, v___x_2470_, v_env_2469_, v___x_2471_, v___x_2472_);
v___x_2474_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v___x_2473_, v_entry_2467_);
lean_dec(v___x_2473_);
if (v___x_2474_ == 0)
{
lean_object* v___f_2475_; uint8_t v___x_2476_; lean_object* v___y_2478_; lean_object* v_cls_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v_scopes_2524_; lean_object* v___x_2525_; lean_object* v_opts_2526_; uint8_t v_hasTrace_2527_; 
v___f_2475_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_2475_, 0, v___x_2470_);
lean_closure_set(v___f_2475_, 1, v_entry_2467_);
v___x_2476_ = 1;
v_cls_2500_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2));
v___x_2501_ = l_Lean_inheritedTraceOptions;
v___x_2502_ = lean_st_ref_get(v___x_2501_);
v___x_2503_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2504_ = lean_st_ref_get(v___y_2442_);
v_scopes_2524_ = lean_ctor_get(v___x_2504_, 2);
lean_inc(v_scopes_2524_);
lean_dec(v___x_2504_);
v___x_2525_ = l_List_head_x21___redArg(v___x_2503_, v_scopes_2524_);
lean_dec(v_scopes_2524_);
v_opts_2526_ = lean_ctor_get(v___x_2525_, 1);
lean_inc_ref(v_opts_2526_);
lean_dec(v___x_2525_);
v_hasTrace_2527_ = lean_ctor_get_uint8(v_opts_2526_, sizeof(void*)*1);
if (v_hasTrace_2527_ == 0)
{
lean_dec_ref(v_opts_2526_);
lean_dec(v___x_2502_);
lean_dec(v_hint_2440_);
lean_dec(v_mod_2438_);
v___y_2478_ = v___y_2442_;
goto v___jp_2477_;
}
else
{
lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2528_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10);
v___x_2529_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2502_, v_opts_2526_, v___x_2528_);
lean_dec_ref(v_opts_2526_);
lean_dec(v___x_2502_);
if (v___x_2529_ == 0)
{
lean_dec(v_hint_2440_);
lean_dec(v_mod_2438_);
v___y_2478_ = v___y_2442_;
goto v___jp_2477_;
}
else
{
lean_object* v___x_2530_; lean_object* v___y_2532_; 
v___x_2530_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12);
if (v_isExporting_2466_ == 0)
{
lean_object* v___x_2539_; 
v___x_2539_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17));
v___y_2532_ = v___x_2539_;
goto v___jp_2531_;
}
else
{
lean_object* v___x_2540_; 
v___x_2540_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18));
v___y_2532_ = v___x_2540_;
goto v___jp_2531_;
}
v___jp_2531_:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
lean_inc_ref(v___y_2532_);
v___x_2533_ = l_Lean_stringToMessageData(v___y_2532_);
v___x_2534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2530_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14);
v___x_2536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2534_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
if (v_isMeta_2439_ == 0)
{
lean_object* v___x_2537_; 
v___x_2537_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15));
v___y_2511_ = v___x_2536_;
v___y_2512_ = v___x_2537_;
goto v___jp_2510_;
}
else
{
lean_object* v___x_2538_; 
v___x_2538_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16));
v___y_2511_ = v___x_2536_;
v___y_2512_ = v___x_2538_;
goto v___jp_2510_;
}
}
}
}
v___jp_2477_:
{
lean_object* v___x_2479_; lean_object* v_toEnvExtension_2480_; lean_object* v_env_2481_; lean_object* v_messages_2482_; lean_object* v_scopes_2483_; lean_object* v_usedQuotCtxts_2484_; lean_object* v_nextMacroScope_2485_; lean_object* v_maxRecDepth_2486_; lean_object* v_ngen_2487_; lean_object* v_auxDeclNGen_2488_; lean_object* v_infoState_2489_; lean_object* v_traceState_2490_; lean_object* v_snapshotTasks_2491_; lean_object* v_prevLinterStates_2492_; lean_object* v_codeQualityEntryTasks_2493_; lean_object* v_asyncMode_2494_; uint8_t v_logWrites_2495_; lean_object* v___x_2496_; 
v___x_2479_ = lean_st_ref_take(v___y_2478_);
v_toEnvExtension_2480_ = lean_ctor_get(v___x_2470_, 0);
v_env_2481_ = lean_ctor_get(v___x_2479_, 0);
lean_inc_ref(v_env_2481_);
v_messages_2482_ = lean_ctor_get(v___x_2479_, 1);
lean_inc_ref(v_messages_2482_);
v_scopes_2483_ = lean_ctor_get(v___x_2479_, 2);
lean_inc(v_scopes_2483_);
v_usedQuotCtxts_2484_ = lean_ctor_get(v___x_2479_, 3);
lean_inc(v_usedQuotCtxts_2484_);
v_nextMacroScope_2485_ = lean_ctor_get(v___x_2479_, 4);
lean_inc(v_nextMacroScope_2485_);
v_maxRecDepth_2486_ = lean_ctor_get(v___x_2479_, 5);
lean_inc(v_maxRecDepth_2486_);
v_ngen_2487_ = lean_ctor_get(v___x_2479_, 6);
lean_inc_ref(v_ngen_2487_);
v_auxDeclNGen_2488_ = lean_ctor_get(v___x_2479_, 7);
lean_inc_ref(v_auxDeclNGen_2488_);
v_infoState_2489_ = lean_ctor_get(v___x_2479_, 8);
lean_inc_ref(v_infoState_2489_);
v_traceState_2490_ = lean_ctor_get(v___x_2479_, 9);
lean_inc_ref(v_traceState_2490_);
v_snapshotTasks_2491_ = lean_ctor_get(v___x_2479_, 10);
lean_inc_ref(v_snapshotTasks_2491_);
v_prevLinterStates_2492_ = lean_ctor_get(v___x_2479_, 11);
lean_inc(v_prevLinterStates_2492_);
v_codeQualityEntryTasks_2493_ = lean_ctor_get(v___x_2479_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2493_);
lean_dec(v___x_2479_);
v_asyncMode_2494_ = lean_ctor_get(v_toEnvExtension_2480_, 2);
v_logWrites_2495_ = lean_ctor_get_uint8(v_toEnvExtension_2480_, sizeof(void*)*6);
v___x_2496_ = lean_box(0);
if (v_logWrites_2495_ == 0)
{
lean_object* v___x_2497_; 
lean_inc_ref(v_toEnvExtension_2480_);
v___x_2497_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2480_, v_env_2481_, v___f_2475_, v_asyncMode_2494_, v___x_2472_, v___x_2476_);
v___y_2445_ = v_snapshotTasks_2491_;
v___y_2446_ = v_infoState_2489_;
v___y_2447_ = v_maxRecDepth_2486_;
v___y_2448_ = v_usedQuotCtxts_2484_;
v___y_2449_ = v_codeQualityEntryTasks_2493_;
v___y_2450_ = v_traceState_2490_;
v___y_2451_ = v_ngen_2487_;
v___y_2452_ = v_messages_2482_;
v___y_2453_ = v_auxDeclNGen_2488_;
v___y_2454_ = v_scopes_2483_;
v___y_2455_ = v___y_2478_;
v___y_2456_ = v_nextMacroScope_2485_;
v___y_2457_ = v___x_2496_;
v___y_2458_ = v_prevLinterStates_2492_;
v___y_2459_ = v___x_2497_;
goto v___jp_2444_;
}
else
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
lean_inc_ref_n(v_toEnvExtension_2480_, 2);
v___x_2498_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2480_, v_env_2481_);
lean_dec_ref(v_env_2481_);
v___x_2499_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2480_, v___x_2498_, v___f_2475_, v_asyncMode_2494_, v___x_2472_, v___x_2476_);
v___y_2445_ = v_snapshotTasks_2491_;
v___y_2446_ = v_infoState_2489_;
v___y_2447_ = v_maxRecDepth_2486_;
v___y_2448_ = v_usedQuotCtxts_2484_;
v___y_2449_ = v_codeQualityEntryTasks_2493_;
v___y_2450_ = v_traceState_2490_;
v___y_2451_ = v_ngen_2487_;
v___y_2452_ = v_messages_2482_;
v___y_2453_ = v_auxDeclNGen_2488_;
v___y_2454_ = v_scopes_2483_;
v___y_2455_ = v___y_2478_;
v___y_2456_ = v_nextMacroScope_2485_;
v___y_2457_ = v___x_2496_;
v___y_2458_ = v_prevLinterStates_2492_;
v___y_2459_ = v___x_2499_;
goto v___jp_2444_;
}
}
v___jp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___y_2506_);
lean_ctor_set(v___x_2508_, 1, v___y_2507_);
v___x_2509_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_2500_, v___x_2508_, v___y_2441_, v___y_2442_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_dec_ref_known(v___x_2509_, 1);
v___y_2478_ = v___y_2442_;
goto v___jp_2477_;
}
else
{
lean_dec_ref(v___f_2475_);
return v___x_2509_;
}
}
v___jp_2510_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
lean_inc_ref(v___y_2512_);
v___x_2513_ = l_Lean_stringToMessageData(v___y_2512_);
v___x_2514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___y_2511_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
v___x_2515_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4);
v___x_2516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2514_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = l_Lean_MessageData_ofName(v_mod_2438_);
v___x_2518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = l_Lean_Name_isAnonymous(v_hint_2440_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2520_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6);
v___x_2521_ = l_Lean_MessageData_ofName(v_hint_2440_);
v___x_2522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___y_2506_ = v___x_2518_;
v___y_2507_ = v___x_2522_;
goto v___jp_2505_;
}
else
{
lean_object* v___x_2523_; 
lean_dec(v_hint_2440_);
v___x_2523_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7);
v___y_2506_ = v___x_2518_;
v___y_2507_ = v___x_2523_;
goto v___jp_2505_;
}
}
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_dec_ref_known(v_entry_2467_, 1);
lean_dec(v_hint_2440_);
lean_dec(v_mod_2438_);
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
return v___x_2542_;
}
v___jp_2444_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2460_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2460_, 0, v___y_2459_);
lean_ctor_set(v___x_2460_, 1, v___y_2452_);
lean_ctor_set(v___x_2460_, 2, v___y_2454_);
lean_ctor_set(v___x_2460_, 3, v___y_2448_);
lean_ctor_set(v___x_2460_, 4, v___y_2456_);
lean_ctor_set(v___x_2460_, 5, v___y_2447_);
lean_ctor_set(v___x_2460_, 6, v___y_2451_);
lean_ctor_set(v___x_2460_, 7, v___y_2453_);
lean_ctor_set(v___x_2460_, 8, v___y_2446_);
lean_ctor_set(v___x_2460_, 9, v___y_2450_);
lean_ctor_set(v___x_2460_, 10, v___y_2445_);
lean_ctor_set(v___x_2460_, 11, v___y_2458_);
lean_ctor_set(v___x_2460_, 12, v___y_2449_);
v___x_2461_ = lean_st_ref_put(v___y_2455_, v___x_2460_);
v___x_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2462_, 0, v___y_2457_);
return v___x_2462_;
}
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_2438_ = stack[0].m_obj;
uint8_t v_isMeta_2439_ = stack[1].m_num;
lean_object* v_hint_2440_ = stack[2].m_obj;
lean_object* v___y_2441_ = stack[3].m_obj;
lean_object* v___y_2442_ = stack[4].m_obj;
lean_object* v_res_2543_;
v_res_2543_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_mod_2438_, v_isMeta_2439_, v_hint_2440_, v___y_2441_, v___y_2442_);
stack->m_obj
 = v_res_2543_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___boxed(lean_object* v_mod_2544_, lean_object* v_isMeta_2545_, lean_object* v_hint_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
uint8_t v_isMeta_boxed_2550_; lean_object* v_res_2551_; 
v_isMeta_boxed_2550_ = lean_unbox(v_isMeta_2545_);
v_res_2551_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_mod_2544_, v_isMeta_boxed_2550_, v_hint_2546_, v___y_2547_, v___y_2548_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
return v_res_2551_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(lean_object* v___x_2552_, lean_object* v_declName_2553_, lean_object* v_as_2554_, size_t v_sz_2555_, size_t v_i_2556_, lean_object* v_b_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
uint8_t v___x_2561_; 
v___x_2561_ = lean_usize_dec_lt(v_i_2556_, v_sz_2555_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2562_; 
lean_dec(v_declName_2553_);
v___x_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2562_, 0, v_b_2557_);
return v___x_2562_;
}
else
{
lean_object* v___x_2563_; lean_object* v_modules_2564_; lean_object* v___x_2565_; lean_object* v_a_2566_; lean_object* v___x_2567_; lean_object* v_toImport_2568_; lean_object* v_module_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; lean_object* v___x_2572_; 
v___x_2563_ = l_Lean_Environment_header(v___x_2552_);
v_modules_2564_ = lean_ctor_get(v___x_2563_, 3);
lean_inc_ref(v_modules_2564_);
lean_dec_ref(v___x_2563_);
v___x_2565_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2566_ = lean_array_uget_borrowed(v_as_2554_, v_i_2556_);
v___x_2567_ = lean_array_get(v___x_2565_, v_modules_2564_, v_a_2566_);
lean_dec_ref(v_modules_2564_);
v_toImport_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc_ref(v_toImport_2568_);
lean_dec(v___x_2567_);
v_module_2569_ = lean_ctor_get(v_toImport_2568_, 0);
lean_inc(v_module_2569_);
lean_dec_ref(v_toImport_2568_);
v___x_2570_ = lean_box(0);
v___x_2571_ = 0;
lean_inc(v_declName_2553_);
v___x_2572_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_2569_, v___x_2571_, v_declName_2553_, v___y_2558_, v___y_2559_);
if (lean_obj_tag(v___x_2572_) == 0)
{
size_t v___x_2573_; size_t v___x_2574_; 
lean_dec_ref_known(v___x_2572_, 1);
v___x_2573_ = ((size_t)1ULL);
v___x_2574_ = lean_usize_add(v_i_2556_, v___x_2573_);
v_i_2556_ = v___x_2574_;
v_b_2557_ = v___x_2570_;
goto _start;
}
else
{
lean_dec(v_declName_2553_);
return v___x_2572_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2552_ = stack[0].m_obj;
lean_object* v_declName_2553_ = stack[1].m_obj;
lean_object* v_as_2554_ = stack[2].m_obj;
size_t v_sz_2555_ = stack[3].m_num;
size_t v_i_2556_ = stack[4].m_num;
lean_object* v_b_2557_ = stack[5].m_obj;
lean_object* v___y_2558_ = stack[6].m_obj;
lean_object* v___y_2559_ = stack[7].m_obj;
lean_object* v_res_2576_;
v_res_2576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v___x_2552_, v_declName_2553_, v_as_2554_, v_sz_2555_, v_i_2556_, v_b_2557_, v___y_2558_, v___y_2559_);
stack->m_obj
 = v_res_2576_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4___boxed(lean_object* v___x_2577_, lean_object* v_declName_2578_, lean_object* v_as_2579_, lean_object* v_sz_2580_, lean_object* v_i_2581_, lean_object* v_b_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
size_t v_sz_boxed_2586_; size_t v_i_boxed_2587_; lean_object* v_res_2588_; 
v_sz_boxed_2586_ = lean_unbox_usize(v_sz_2580_);
lean_dec(v_sz_2580_);
v_i_boxed_2587_ = lean_unbox_usize(v_i_2581_);
lean_dec(v_i_2581_);
v_res_2588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v___x_2577_, v_declName_2578_, v_as_2579_, v_sz_boxed_2586_, v_i_boxed_2587_, v_b_2582_, v___y_2583_, v___y_2584_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec_ref(v_as_2579_);
lean_dec_ref(v___x_2577_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(lean_object* v_a_2589_, lean_object* v_x_2590_){
_start:
{
if (lean_obj_tag(v_x_2590_) == 0)
{
lean_object* v___x_2591_; 
v___x_2591_ = lean_box(0);
return v___x_2591_;
}
else
{
lean_object* v_key_2592_; lean_object* v_value_2593_; lean_object* v_tail_2594_; uint8_t v___x_2595_; 
v_key_2592_ = lean_ctor_get(v_x_2590_, 0);
v_value_2593_ = lean_ctor_get(v_x_2590_, 1);
v_tail_2594_ = lean_ctor_get(v_x_2590_, 2);
v___x_2595_ = lean_name_eq(v_key_2592_, v_a_2589_);
if (v___x_2595_ == 0)
{
v_x_2590_ = v_tail_2594_;
goto _start;
}
else
{
lean_object* v___x_2597_; 
lean_inc(v_value_2593_);
v___x_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2597_, 0, v_value_2593_);
return v___x_2597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v_a_2598_, lean_object* v_x_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_2598_, v_x_2599_);
lean_dec(v_x_2599_);
lean_dec(v_a_2598_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(lean_object* v_m_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v_buckets_2603_; lean_object* v___x_2604_; uint64_t v___y_2606_; 
v_buckets_2603_ = lean_ctor_get(v_m_2601_, 1);
v___x_2604_ = lean_array_get_size(v_buckets_2603_);
if (lean_obj_tag(v_a_2602_) == 0)
{
uint64_t v___x_2620_; 
v___x_2620_ = 1723ULL;
v___y_2606_ = v___x_2620_;
goto v___jp_2605_;
}
else
{
uint64_t v_hash_2621_; 
v_hash_2621_ = lean_ctor_get_uint64(v_a_2602_, sizeof(void*)*2);
v___y_2606_ = v_hash_2621_;
goto v___jp_2605_;
}
v___jp_2605_:
{
uint64_t v___x_2607_; uint64_t v___x_2608_; uint64_t v_fold_2609_; uint64_t v___x_2610_; uint64_t v___x_2611_; uint64_t v___x_2612_; size_t v___x_2613_; size_t v___x_2614_; size_t v___x_2615_; size_t v___x_2616_; size_t v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2607_ = 32ULL;
v___x_2608_ = lean_uint64_shift_right(v___y_2606_, v___x_2607_);
v_fold_2609_ = lean_uint64_xor(v___y_2606_, v___x_2608_);
v___x_2610_ = 16ULL;
v___x_2611_ = lean_uint64_shift_right(v_fold_2609_, v___x_2610_);
v___x_2612_ = lean_uint64_xor(v_fold_2609_, v___x_2611_);
v___x_2613_ = lean_uint64_to_usize(v___x_2612_);
v___x_2614_ = lean_usize_of_nat(v___x_2604_);
v___x_2615_ = ((size_t)1ULL);
v___x_2616_ = lean_usize_sub(v___x_2614_, v___x_2615_);
v___x_2617_ = lean_usize_land(v___x_2613_, v___x_2616_);
v___x_2618_ = lean_array_uget_borrowed(v_buckets_2603_, v___x_2617_);
v___x_2619_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_2602_, v___x_2618_);
return v___x_2619_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_m_2622_, lean_object* v_a_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_2622_, v_a_2623_);
lean_dec(v_a_2623_);
lean_dec_ref(v_m_2622_);
return v_res_2624_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2625_;
}
}
lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(lean_object* v_declName_2628_, uint8_t v_isMeta_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v_env_2638_; lean_object* v___y_2640_; lean_object* v___x_2653_; 
v___x_2633_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0);
v___x_2634_ = lean_st_ref_get(v___y_2631_);
v_env_2638_ = lean_ctor_get(v___x_2634_, 0);
lean_inc_ref(v_env_2638_);
lean_dec(v___x_2634_);
v___x_2653_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2638_, v_declName_2628_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_dec_ref(v_env_2638_);
lean_dec(v_declName_2628_);
goto v___jp_2635_;
}
else
{
lean_object* v_val_2654_; lean_object* v___x_2655_; lean_object* v_modules_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v_val_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_val_2654_);
lean_dec_ref_known(v___x_2653_, 1);
v___x_2655_ = l_Lean_Environment_header(v_env_2638_);
v_modules_2656_ = lean_ctor_get(v___x_2655_, 3);
lean_inc_ref(v_modules_2656_);
lean_dec_ref(v___x_2655_);
v___x_2657_ = lean_array_get_size(v_modules_2656_);
v___x_2658_ = lean_nat_dec_lt(v_val_2654_, v___x_2657_);
if (v___x_2658_ == 0)
{
lean_dec_ref(v_modules_2656_);
lean_dec(v_val_2654_);
lean_dec_ref(v_env_2638_);
lean_dec(v_declName_2628_);
goto v___jp_2635_;
}
else
{
lean_object* v___x_2659_; lean_object* v___x_2660_; uint8_t v___y_2662_; 
v___x_2659_ = lean_array_fget(v_modules_2656_, v_val_2654_);
lean_dec(v_val_2654_);
lean_dec_ref(v_modules_2656_);
v___x_2660_ = lean_st_ref_get(v___y_2631_);
if (v_isMeta_2629_ == 0)
{
lean_dec(v___x_2660_);
v___y_2662_ = v_isMeta_2629_;
goto v___jp_2661_;
}
else
{
lean_object* v_env_2673_; uint8_t v___x_2674_; 
v_env_2673_ = lean_ctor_get(v___x_2660_, 0);
lean_inc_ref(v_env_2673_);
lean_dec(v___x_2660_);
lean_inc(v_declName_2628_);
v___x_2674_ = l_Lean_isMarkedMeta(v_env_2673_, v_declName_2628_);
if (v___x_2674_ == 0)
{
v___y_2662_ = v_isMeta_2629_;
goto v___jp_2661_;
}
else
{
uint8_t v___x_2675_; 
v___x_2675_ = 0;
v___y_2662_ = v___x_2675_;
goto v___jp_2661_;
}
}
v___jp_2661_:
{
lean_object* v_toImport_2663_; lean_object* v_module_2664_; lean_object* v___x_2665_; 
v_toImport_2663_ = lean_ctor_get(v___x_2659_, 0);
lean_inc_ref(v_toImport_2663_);
lean_dec(v___x_2659_);
v_module_2664_ = lean_ctor_get(v_toImport_2663_, 0);
lean_inc(v_module_2664_);
lean_dec_ref(v_toImport_2663_);
lean_inc(v_declName_2628_);
v___x_2665_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_2664_, v___y_2662_, v_declName_2628_, v___y_2630_, v___y_2631_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
lean_dec_ref_known(v___x_2665_, 1);
v___x_2666_ = l_Lean_indirectModUseExt;
v___x_2667_ = lean_box(1);
v___x_2668_ = lean_box(0);
lean_inc_ref(v_env_2638_);
v___x_2669_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2633_, v___x_2666_, v_env_2638_, v___x_2667_, v___x_2668_);
v___x_2670_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v___x_2669_, v_declName_2628_);
lean_dec(v___x_2669_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v___x_2671_; 
v___x_2671_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1));
v___y_2640_ = v___x_2671_;
goto v___jp_2639_;
}
else
{
lean_object* v_val_2672_; 
v_val_2672_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_val_2672_);
lean_dec_ref_known(v___x_2670_, 1);
v___y_2640_ = v_val_2672_;
goto v___jp_2639_;
}
}
else
{
lean_dec_ref(v_env_2638_);
lean_dec(v_declName_2628_);
return v___x_2665_;
}
}
}
}
v___jp_2635_:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = lean_box(0);
v___x_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
return v___x_2637_;
}
v___jp_2639_:
{
lean_object* v___x_2641_; size_t v_sz_2642_; size_t v___x_2643_; lean_object* v___x_2644_; 
v___x_2641_ = lean_box(0);
v_sz_2642_ = lean_array_size(v___y_2640_);
v___x_2643_ = ((size_t)0ULL);
v___x_2644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v_env_2638_, v_declName_2628_, v___y_2640_, v_sz_2642_, v___x_2643_, v___x_2641_, v___y_2630_, v___y_2631_);
lean_dec_ref(v___y_2640_);
lean_dec_ref(v_env_2638_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2651_ == 0)
{
lean_object* v_unused_2652_; 
v_unused_2652_ = lean_ctor_get(v___x_2644_, 0);
lean_dec(v_unused_2652_);
v___x_2646_ = v___x_2644_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_dec(v___x_2644_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v___x_2641_);
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2641_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
else
{
return v___x_2644_;
}
}
}
}
LEAN_EXPORT void l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2628_ = stack[0].m_obj;
uint8_t v_isMeta_2629_ = stack[1].m_num;
lean_object* v___y_2630_ = stack[2].m_obj;
lean_object* v___y_2631_ = stack[3].m_obj;
lean_object* v_res_2676_;
v_res_2676_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_declName_2628_, v_isMeta_2629_, v___y_2630_, v___y_2631_);
stack->m_obj
 = v_res_2676_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___boxed(lean_object* v_declName_2677_, lean_object* v_isMeta_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
uint8_t v_isMeta_boxed_2682_; lean_object* v_res_2683_; 
v_isMeta_boxed_2682_ = lean_unbox(v_isMeta_2678_);
v_res_2683_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_declName_2677_, v_isMeta_boxed_2682_, v___y_2679_, v___y_2680_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
return v_res_2683_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(lean_object* v_as_x27_2684_, lean_object* v_b_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
if (lean_obj_tag(v_as_x27_2684_) == 0)
{
lean_object* v___x_2689_; 
v___x_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2689_, 0, v_b_2685_);
return v___x_2689_;
}
else
{
lean_object* v_head_2690_; lean_object* v_tail_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; lean_object* v___x_2694_; 
v_head_2690_ = lean_ctor_get(v_as_x27_2684_, 0);
v_tail_2691_ = lean_ctor_get(v_as_x27_2684_, 1);
v___x_2692_ = lean_box(0);
v___x_2693_ = 1;
lean_inc(v_head_2690_);
v___x_2694_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_head_2690_, v___x_2693_, v___y_2686_, v___y_2687_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_dec_ref_known(v___x_2694_, 1);
v_as_x27_2684_ = v_tail_2691_;
v_b_2685_ = v___x_2692_;
goto _start;
}
else
{
return v___x_2694_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_2684_ = stack[0].m_obj;
lean_object* v_b_2685_ = stack[1].m_obj;
lean_object* v___y_2686_ = stack[2].m_obj;
lean_object* v___y_2687_ = stack[3].m_obj;
lean_object* v_res_2696_;
v_res_2696_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_2684_, v_b_2685_, v___y_2686_, v___y_2687_);
stack->m_obj
 = v_res_2696_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_2697_, lean_object* v_b_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_2697_, v_b_2698_, v___y_2699_, v___y_2700_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v_as_x27_2697_);
return v_res_2702_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = l_Lean_maxRecDepthErrorMessage;
v___x_2709_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
return v___x_2709_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3);
v___x_2711_ = l_Lean_MessageData_ofFormat(v___x_2710_);
return v___x_2711_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2712_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4);
v___x_2713_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2));
v___x_2714_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
lean_ctor_set(v___x_2714_, 1, v___x_2712_);
return v___x_2714_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(lean_object* v_ref_2715_){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2717_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5);
v___x_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2718_, 0, v_ref_2715_);
lean_ctor_set(v___x_2718_, 1, v___x_2717_);
v___x_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2715_ = stack[0].m_obj;
lean_object* v_res_2720_;
v_res_2720_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_2715_);
stack->m_obj
 = v_res_2720_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___boxed(lean_object* v_ref_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_2721_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(lean_object* v_currNamespace_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2727_, 0, v_currNamespace_2724_);
lean_ctor_set(v___x_2727_, 1, v___y_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(v_currNamespace_2728_, v___y_2729_, v___y_2730_);
lean_dec_ref(v___y_2729_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(lean_object* v_env_2732_, lean_object* v_declName_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
uint8_t v___x_2736_; lean_object* v_env_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; uint8_t v___x_2740_; 
v___x_2736_ = 0;
v_env_2737_ = l_Lean_Environment_setExporting(v_env_2732_, v___x_2736_);
lean_inc(v_declName_2733_);
v___x_2738_ = l_Lean_mkPrivateName(v_env_2737_, v_declName_2733_);
v___x_2739_ = 1;
lean_inc_ref(v_env_2737_);
v___x_2740_ = l_Lean_Environment_contains(v_env_2737_, v___x_2738_, v___x_2739_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; uint8_t v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2741_ = l_Lean_privateToUserName(v_declName_2733_);
v___x_2742_ = l_Lean_Environment_contains(v_env_2737_, v___x_2741_, v___x_2739_);
v___x_2743_ = lean_box(v___x_2742_);
v___x_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
lean_ctor_set(v___x_2744_, 1, v___y_2735_);
return v___x_2744_;
}
else
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
lean_dec_ref(v_env_2737_);
lean_dec(v_declName_2733_);
v___x_2745_ = lean_box(v___x_2740_);
v___x_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2745_);
lean_ctor_set(v___x_2746_, 1, v___y_2735_);
return v___x_2746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed(lean_object* v_env_2747_, lean_object* v_declName_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(v_env_2747_, v_declName_2748_, v___y_2749_, v___y_2750_);
lean_dec_ref(v___y_2749_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(lean_object* v_x_2752_, lean_object* v___y_2753_){
_start:
{
if (lean_obj_tag(v_x_2752_) == 0)
{
lean_object* v_a_2754_; lean_object* v___x_2755_; 
v_a_2754_ = lean_ctor_get(v_x_2752_, 0);
lean_inc(v_a_2754_);
v___x_2755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2755_, 0, v_a_2754_);
lean_ctor_set(v___x_2755_, 1, v___y_2753_);
return v___x_2755_;
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2757_; 
v_a_2756_ = lean_ctor_get(v_x_2752_, 0);
lean_inc(v_a_2756_);
v___x_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2757_, 0, v_a_2756_);
lean_ctor_set(v___x_2757_, 1, v___y_2753_);
return v___x_2757_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg___boxed(lean_object* v_x_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_2758_, v___y_2759_);
lean_dec_ref(v_x_2758_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(lean_object* v_env_2761_, lean_object* v_stx_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2761_, v_stx_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2766_);
if (lean_obj_tag(v_a_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2775_; 
v_a_2767_ = lean_ctor_get(v___x_2765_, 1);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2775_ == 0)
{
lean_object* v_unused_2776_; 
v_unused_2776_ = lean_ctor_get(v___x_2765_, 0);
lean_dec(v_unused_2776_);
v___x_2769_ = v___x_2765_;
v_isShared_2770_ = v_isSharedCheck_2775_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2765_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2775_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2771_; lean_object* v___x_2773_; 
v___x_2771_ = lean_box(0);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 0, v___x_2771_);
v___x_2773_ = v___x_2769_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_a_2767_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
else
{
lean_object* v_val_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2805_; 
v_val_2777_ = lean_ctor_get(v_a_2766_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v_a_2766_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2779_ = v_a_2766_;
v_isShared_2780_ = v_isSharedCheck_2805_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_val_2777_);
lean_dec(v_a_2766_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2805_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v_snd_2781_; 
v_snd_2781_ = lean_ctor_get(v_val_2777_, 1);
lean_inc(v_snd_2781_);
lean_dec(v_val_2777_);
if (lean_obj_tag(v_snd_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2791_; 
lean_del_object(v___x_2779_);
v_a_2782_ = lean_ctor_get(v___x_2765_, 1);
lean_inc(v_a_2782_);
lean_dec_ref_known(v___x_2765_, 2);
v_a_2783_ = lean_ctor_get(v_snd_2781_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v_snd_2781_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2785_ = v_snd_2781_;
v_isShared_2786_ = v_isSharedCheck_2791_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v_snd_2781_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2791_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_2788_, v_a_2782_);
lean_dec_ref(v___x_2788_);
return v___x_2789_;
}
}
}
else
{
lean_object* v_a_2792_; lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2804_; 
v_a_2792_ = lean_ctor_get(v___x_2765_, 1);
lean_inc(v_a_2792_);
lean_dec_ref_known(v___x_2765_, 2);
v_a_2793_ = lean_ctor_get(v_snd_2781_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_snd_2781_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2795_ = v_snd_2781_;
v_isShared_2796_ = v_isSharedCheck_2804_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v_snd_2781_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2804_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v_a_2793_);
v___x_2798_ = v___x_2779_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v___x_2800_; 
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 0, v___x_2798_);
v___x_2800_ = v___x_2795_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2798_);
v___x_2800_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_2800_, v_a_2792_);
lean_dec_ref(v___x_2800_);
return v___x_2801_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2806_; lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
v_a_2806_ = lean_ctor_get(v___x_2765_, 0);
v_a_2807_ = lean_ctor_get(v___x_2765_, 1);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2765_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_inc(v_a_2806_);
lean_dec(v___x_2765_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2806_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed(lean_object* v_env_2815_, lean_object* v_stx_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(v_env_2815_, v_stx_2816_, v___y_2817_, v___y_2818_);
lean_dec_ref(v___y_2817_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(lean_object* v_env_2820_, lean_object* v_currNamespace_2821_, lean_object* v_openDecls_2822_, lean_object* v_n_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = l_Lean_ResolveName_resolveNamespace(v_env_2820_, v_currNamespace_2821_, v_openDecls_2822_, v_n_2823_);
v___x_2827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
lean_ctor_set(v___x_2827_, 1, v___y_2825_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed(lean_object* v_env_2828_, lean_object* v_currNamespace_2829_, lean_object* v_openDecls_2830_, lean_object* v_n_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(v_env_2828_, v_currNamespace_2829_, v_openDecls_2830_, v_n_2831_, v___y_2832_, v___y_2833_);
lean_dec_ref(v___y_2832_);
return v_res_2834_;
}
}
lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(lean_object* v_as_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
if (lean_obj_tag(v_as_2835_) == 0)
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = lean_box(0);
v___x_2840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
return v___x_2840_;
}
else
{
lean_object* v_head_2841_; lean_object* v_tail_2842_; lean_object* v_fst_2843_; lean_object* v_snd_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v_scopes_2849_; lean_object* v___x_2850_; lean_object* v_opts_2851_; uint8_t v_hasTrace_2852_; 
v_head_2841_ = lean_ctor_get(v_as_2835_, 0);
lean_inc(v_head_2841_);
v_tail_2842_ = lean_ctor_get(v_as_2835_, 1);
lean_inc(v_tail_2842_);
lean_dec_ref_known(v_as_2835_, 2);
v_fst_2843_ = lean_ctor_get(v_head_2841_, 0);
lean_inc(v_fst_2843_);
v_snd_2844_ = lean_ctor_get(v_head_2841_, 1);
lean_inc(v_snd_2844_);
lean_dec(v_head_2841_);
v___x_2845_ = l_Lean_inheritedTraceOptions;
v___x_2846_ = lean_st_ref_get(v___x_2845_);
v___x_2847_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2848_ = lean_st_ref_get(v___y_2837_);
v_scopes_2849_ = lean_ctor_get(v___x_2848_, 2);
lean_inc(v_scopes_2849_);
lean_dec(v___x_2848_);
v___x_2850_ = l_List_head_x21___redArg(v___x_2847_, v_scopes_2849_);
lean_dec(v_scopes_2849_);
v_opts_2851_ = lean_ctor_get(v___x_2850_, 1);
lean_inc_ref(v_opts_2851_);
lean_dec(v___x_2850_);
v_hasTrace_2852_ = lean_ctor_get_uint8(v_opts_2851_, sizeof(void*)*1);
if (v_hasTrace_2852_ == 0)
{
lean_dec_ref(v_opts_2851_);
lean_dec(v___x_2846_);
lean_dec(v_snd_2844_);
lean_dec(v_fst_2843_);
v_as_2835_ = v_tail_2842_;
goto _start;
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; uint8_t v___x_2856_; 
v___x_2854_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9));
lean_inc(v_fst_2843_);
v___x_2855_ = l_Lean_Name_append(v___x_2854_, v_fst_2843_);
v___x_2856_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2846_, v_opts_2851_, v___x_2855_);
lean_dec(v___x_2855_);
lean_dec_ref(v_opts_2851_);
lean_dec(v___x_2846_);
if (v___x_2856_ == 0)
{
lean_dec(v_snd_2844_);
lean_dec(v_fst_2843_);
v_as_2835_ = v_tail_2842_;
goto _start;
}
else
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2858_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2858_, 0, v_snd_2844_);
v___x_2859_ = l_Lean_MessageData_ofFormat(v___x_2858_);
v___x_2860_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_fst_2843_, v___x_2859_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_dec_ref_known(v___x_2860_, 1);
v_as_2835_ = v_tail_2842_;
goto _start;
}
else
{
lean_dec(v_tail_2842_);
return v___x_2860_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2835_ = stack[0].m_obj;
lean_object* v___y_2836_ = stack[1].m_obj;
lean_object* v___y_2837_ = stack[2].m_obj;
lean_object* v_res_2862_;
v_res_2862_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v_as_2835_, v___y_2836_, v___y_2837_);
stack->m_obj
 = v_res_2862_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___boxed(lean_object* v_as_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v_as_2863_, v___y_2864_, v___y_2865_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(lean_object* v_env_2868_, lean_object* v_opts_2869_, lean_object* v_currNamespace_2870_, lean_object* v_openDecls_2871_, lean_object* v_n_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2875_ = l_Lean_ResolveName_resolveGlobalName(v_env_2868_, v_opts_2869_, v_currNamespace_2870_, v_openDecls_2871_, v_n_2872_);
v___x_2876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
lean_ctor_set(v___x_2876_, 1, v___y_2874_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed(lean_object* v_env_2877_, lean_object* v_opts_2878_, lean_object* v_currNamespace_2879_, lean_object* v_openDecls_2880_, lean_object* v_n_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(v_env_2877_, v_opts_2878_, v_currNamespace_2879_, v_openDecls_2880_, v_n_2881_, v___y_2882_, v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec_ref(v_opts_2878_);
return v_res_2884_;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(lean_object* v_x_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v___x_2890_; lean_object* v_env_2891_; lean_object* v___f_2892_; lean_object* v___f_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v_scopes_2896_; lean_object* v___x_2897_; lean_object* v_opts_2898_; lean_object* v___x_2899_; 
v___x_2890_ = lean_st_ref_get(v___y_2888_);
v_env_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc_ref_n(v_env_2891_, 3);
lean_dec(v___x_2890_);
v___f_2892_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2892_, 0, v_env_2891_);
v___f_2893_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2893_, 0, v_env_2891_);
v___x_2894_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2895_ = lean_st_ref_get(v___y_2888_);
v_scopes_2896_ = lean_ctor_get(v___x_2895_, 2);
lean_inc(v_scopes_2896_);
lean_dec(v___x_2895_);
v___x_2897_ = l_List_head_x21___redArg(v___x_2894_, v_scopes_2896_);
lean_dec(v_scopes_2896_);
v_opts_2898_ = lean_ctor_get(v___x_2897_, 1);
lean_inc_ref(v_opts_2898_);
lean_dec(v___x_2897_);
v___x_2899_ = l_Lean_Elab_Command_getScope___redArg(v___y_2888_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v_currNamespace_2901_; lean_object* v___f_2902_; lean_object* v___x_2903_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_a_2900_);
lean_dec_ref_known(v___x_2899_, 1);
v_currNamespace_2901_ = lean_ctor_get(v_a_2900_, 2);
lean_inc_n(v_currNamespace_2901_, 2);
lean_dec(v_a_2900_);
v___f_2902_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2902_, 0, v_currNamespace_2901_);
v___x_2903_ = l_Lean_Elab_Command_getScope___redArg(v___y_2888_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v_openDecls_2905_; lean_object* v___f_2906_; lean_object* v___f_2907_; lean_object* v_methods_2908_; lean_object* v___x_2909_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v_openDecls_2905_ = lean_ctor_get(v_a_2904_, 3);
lean_inc_n(v_openDecls_2905_, 2);
lean_dec(v_a_2904_);
lean_inc(v_currNamespace_2901_);
lean_inc_ref(v_env_2891_);
v___f_2906_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_2906_, 0, v_env_2891_);
lean_closure_set(v___f_2906_, 1, v_currNamespace_2901_);
lean_closure_set(v___f_2906_, 2, v_openDecls_2905_);
v___f_2907_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2907_, 0, v_env_2891_);
lean_closure_set(v___f_2907_, 1, v_opts_2898_);
lean_closure_set(v___f_2907_, 2, v_currNamespace_2901_);
lean_closure_set(v___f_2907_, 3, v_openDecls_2905_);
v_methods_2908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2908_, 0, v___f_2893_);
lean_ctor_set(v_methods_2908_, 1, v___f_2902_);
lean_ctor_set(v_methods_2908_, 2, v___f_2892_);
lean_ctor_set(v_methods_2908_, 3, v___f_2906_);
lean_ctor_set(v_methods_2908_, 4, v___f_2907_);
v___x_2909_ = l_Lean_Elab_Command_getRef___redArg(v___y_2887_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; lean_object* v___x_2911_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_a_2910_);
lean_dec_ref_known(v___x_2909_, 1);
v___x_2911_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2887_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v_currRecDepth_2913_; lean_object* v_quotContext_x3f_2914_; lean_object* v_a_2916_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref_known(v___x_2911_, 1);
v_currRecDepth_2913_ = lean_ctor_get(v___y_2887_, 2);
v_quotContext_x3f_2914_ = lean_ctor_get(v___y_2887_, 5);
if (lean_obj_tag(v_quotContext_x3f_2914_) == 0)
{
lean_object* v___x_2990_; lean_object* v_a_2991_; 
v___x_2990_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_2888_);
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref(v___x_2990_);
v_a_2916_ = v_a_2991_;
goto v___jp_2915_;
}
else
{
lean_object* v_val_2992_; 
v_val_2992_ = lean_ctor_get(v_quotContext_x3f_2914_, 0);
lean_inc(v_val_2992_);
v_a_2916_ = v_val_2992_;
goto v___jp_2915_;
}
v___jp_2915_:
{
lean_object* v___x_2917_; lean_object* v_maxRecDepth_2918_; lean_object* v___x_2919_; lean_object* v_nextMacroScope_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2917_ = lean_st_ref_get(v___y_2888_);
v_maxRecDepth_2918_ = lean_ctor_get(v___x_2917_, 5);
lean_inc(v_maxRecDepth_2918_);
lean_dec(v___x_2917_);
v___x_2919_ = lean_st_ref_get(v___y_2888_);
v_nextMacroScope_2920_ = lean_ctor_get(v___x_2919_, 4);
lean_inc(v_nextMacroScope_2920_);
lean_dec(v___x_2919_);
lean_inc(v_currRecDepth_2913_);
v___x_2921_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2921_, 0, v_methods_2908_);
lean_ctor_set(v___x_2921_, 1, v_a_2916_);
lean_ctor_set(v___x_2921_, 2, v_a_2912_);
lean_ctor_set(v___x_2921_, 3, v_currRecDepth_2913_);
lean_ctor_set(v___x_2921_, 4, v_maxRecDepth_2918_);
lean_ctor_set(v___x_2921_, 5, v_a_2910_);
v___x_2922_ = lean_box(0);
v___x_2923_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2923_, 0, v_nextMacroScope_2920_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
lean_ctor_set(v___x_2923_, 2, v___x_2922_);
v___x_2924_ = lean_apply_2(v_x_2886_, v___x_2921_, v___x_2923_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v_a_2926_; lean_object* v_macroScope_2927_; lean_object* v_traceMsgs_2928_; lean_object* v_expandedMacroDecls_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 1);
lean_inc(v_a_2925_);
v_a_2926_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v___x_2924_, 2);
v_macroScope_2927_ = lean_ctor_get(v_a_2925_, 0);
lean_inc(v_macroScope_2927_);
v_traceMsgs_2928_ = lean_ctor_get(v_a_2925_, 1);
lean_inc(v_traceMsgs_2928_);
v_expandedMacroDecls_2929_ = lean_ctor_get(v_a_2925_, 2);
lean_inc(v_expandedMacroDecls_2929_);
lean_dec(v_a_2925_);
v___x_2930_ = lean_box(0);
v___x_2931_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_expandedMacroDecls_2929_, v___x_2930_, v___y_2887_, v___y_2888_);
lean_dec(v_expandedMacroDecls_2929_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v___x_2932_; lean_object* v_env_2933_; lean_object* v_messages_2934_; lean_object* v_scopes_2935_; lean_object* v_usedQuotCtxts_2936_; lean_object* v_maxRecDepth_2937_; lean_object* v_ngen_2938_; lean_object* v_auxDeclNGen_2939_; lean_object* v_infoState_2940_; lean_object* v_traceState_2941_; lean_object* v_snapshotTasks_2942_; lean_object* v_prevLinterStates_2943_; lean_object* v_codeQualityEntryTasks_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2970_; 
lean_dec_ref_known(v___x_2931_, 1);
v___x_2932_ = lean_st_ref_take(v___y_2888_);
v_env_2933_ = lean_ctor_get(v___x_2932_, 0);
v_messages_2934_ = lean_ctor_get(v___x_2932_, 1);
v_scopes_2935_ = lean_ctor_get(v___x_2932_, 2);
v_usedQuotCtxts_2936_ = lean_ctor_get(v___x_2932_, 3);
v_maxRecDepth_2937_ = lean_ctor_get(v___x_2932_, 5);
v_ngen_2938_ = lean_ctor_get(v___x_2932_, 6);
v_auxDeclNGen_2939_ = lean_ctor_get(v___x_2932_, 7);
v_infoState_2940_ = lean_ctor_get(v___x_2932_, 8);
v_traceState_2941_ = lean_ctor_get(v___x_2932_, 9);
v_snapshotTasks_2942_ = lean_ctor_get(v___x_2932_, 10);
v_prevLinterStates_2943_ = lean_ctor_get(v___x_2932_, 11);
v_codeQualityEntryTasks_2944_ = lean_ctor_get(v___x_2932_, 12);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2970_ == 0)
{
lean_object* v_unused_2971_; 
v_unused_2971_ = lean_ctor_get(v___x_2932_, 4);
lean_dec(v_unused_2971_);
v___x_2946_ = v___x_2932_;
v_isShared_2947_ = v_isSharedCheck_2970_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2944_);
lean_inc(v_prevLinterStates_2943_);
lean_inc(v_snapshotTasks_2942_);
lean_inc(v_traceState_2941_);
lean_inc(v_infoState_2940_);
lean_inc(v_auxDeclNGen_2939_);
lean_inc(v_ngen_2938_);
lean_inc(v_maxRecDepth_2937_);
lean_inc(v_usedQuotCtxts_2936_);
lean_inc(v_scopes_2935_);
lean_inc(v_messages_2934_);
lean_inc(v_env_2933_);
lean_dec(v___x_2932_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2970_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 4, v_macroScope_2927_);
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_env_2933_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v_messages_2934_);
lean_ctor_set(v_reuseFailAlloc_2969_, 2, v_scopes_2935_);
lean_ctor_set(v_reuseFailAlloc_2969_, 3, v_usedQuotCtxts_2936_);
lean_ctor_set(v_reuseFailAlloc_2969_, 4, v_macroScope_2927_);
lean_ctor_set(v_reuseFailAlloc_2969_, 5, v_maxRecDepth_2937_);
lean_ctor_set(v_reuseFailAlloc_2969_, 6, v_ngen_2938_);
lean_ctor_set(v_reuseFailAlloc_2969_, 7, v_auxDeclNGen_2939_);
lean_ctor_set(v_reuseFailAlloc_2969_, 8, v_infoState_2940_);
lean_ctor_set(v_reuseFailAlloc_2969_, 9, v_traceState_2941_);
lean_ctor_set(v_reuseFailAlloc_2969_, 10, v_snapshotTasks_2942_);
lean_ctor_set(v_reuseFailAlloc_2969_, 11, v_prevLinterStates_2943_);
lean_ctor_set(v_reuseFailAlloc_2969_, 12, v_codeQualityEntryTasks_2944_);
v___x_2949_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2950_ = lean_st_ref_put(v___y_2888_, v___x_2949_);
v___x_2951_ = l_List_reverse___redArg(v_traceMsgs_2928_);
v___x_2952_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v___x_2951_, v___y_2887_, v___y_2888_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2959_ == 0)
{
lean_object* v_unused_2960_; 
v_unused_2960_ = lean_ctor_get(v___x_2952_, 0);
lean_dec(v_unused_2960_);
v___x_2954_ = v___x_2952_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_dec(v___x_2952_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 0, v_a_2926_);
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2926_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec(v_a_2926_);
v_a_2961_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2952_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2952_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_dec(v_traceMsgs_2928_);
lean_dec(v_macroScope_2927_);
lean_dec(v_a_2926_);
v_a_2972_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2931_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2931_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
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
else
{
lean_object* v_a_2980_; 
v_a_2980_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2980_);
lean_dec_ref_known(v___x_2924_, 2);
if (lean_obj_tag(v_a_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v_a_2982_; lean_object* v___x_2983_; uint8_t v___x_2984_; 
v_a_2981_ = lean_ctor_get(v_a_2980_, 0);
lean_inc(v_a_2981_);
v_a_2982_ = lean_ctor_get(v_a_2980_, 1);
lean_inc_ref(v_a_2982_);
lean_dec_ref_known(v_a_2980_, 2);
v___x_2983_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0));
v___x_2984_ = lean_string_dec_eq(v_a_2982_, v___x_2983_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2985_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2985_, 0, v_a_2982_);
v___x_2986_ = l_Lean_MessageData_ofFormat(v___x_2985_);
v___x_2987_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_a_2981_, v___x_2986_, v___y_2887_, v___y_2888_);
lean_dec(v_a_2981_);
return v___x_2987_;
}
else
{
lean_object* v___x_2988_; 
lean_dec_ref(v_a_2982_);
v___x_2988_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_a_2981_);
return v___x_2988_;
}
}
else
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2989_;
}
}
}
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec(v_a_2910_);
lean_dec_ref_known(v_methods_2908_, 5);
lean_dec_ref(v_x_2886_);
v_a_2993_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2911_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2911_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
lean_dec_ref_known(v_methods_2908_, 5);
lean_dec_ref(v_x_2886_);
v_a_3001_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___x_2909_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_2909_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec_ref(v___f_2902_);
lean_dec(v_currNamespace_2901_);
lean_dec_ref(v_opts_2898_);
lean_dec_ref(v___f_2893_);
lean_dec_ref(v___f_2892_);
lean_dec_ref(v_env_2891_);
lean_dec_ref(v_x_2886_);
v_a_3009_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_2903_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_2903_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
lean_dec_ref(v_opts_2898_);
lean_dec_ref(v___f_2893_);
lean_dec_ref(v___f_2892_);
lean_dec_ref(v_env_2891_);
lean_dec_ref(v_x_2886_);
v_a_3017_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_2899_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_2899_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2886_ = stack[0].m_obj;
lean_object* v___y_2887_ = stack[1].m_obj;
lean_object* v___y_2888_ = stack[2].m_obj;
lean_object* v_res_3025_;
v_res_3025_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_2886_, v___y_2887_, v___y_2888_);
stack->m_obj
 = v_res_3025_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___boxed(lean_object* v_x_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_3026_, v___y_3027_, v___y_3028_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
return v_res_3030_;
}
}
lean_object* l_Lean_Elab_Command_elabElab(lean_object* v_x_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___x_3116_; uint8_t v___x_3117_; 
v___x_3074_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_3075_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_3116_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
lean_inc(v_x_3070_);
v___x_3117_ = l_Lean_Syntax_isOfKind(v_x_3070_, v___x_3116_);
if (v___x_3117_ == 0)
{
lean_object* v___x_3118_; 
lean_dec(v_x_3070_);
v___x_3118_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3118_;
}
else
{
lean_object* v___x_3119_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; size_t v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; uint8_t v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; size_t v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; uint8_t v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; size_t v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; uint8_t v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; size_t v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; uint8_t v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; size_t v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; uint8_t v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v_expectedType_x3f_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v_prio_x3f_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v_name_x3f_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v_prec_x3f_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v_attrs_x3f_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v_doc_x3f_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___x_3596_; uint8_t v___x_3597_; 
v___x_3119_ = lean_unsigned_to_nat(0u);
v___x_3596_ = l_Lean_Syntax_getArg(v_x_3070_, v___x_3119_);
v___x_3597_ = l_Lean_Syntax_isNone(v___x_3596_);
if (v___x_3597_ == 0)
{
lean_object* v___x_3598_; uint8_t v___x_3599_; 
v___x_3598_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3596_);
v___x_3599_ = l_Lean_Syntax_matchesNull(v___x_3596_, v___x_3598_);
if (v___x_3599_ == 0)
{
lean_object* v___x_3600_; 
lean_dec(v___x_3596_);
lean_dec(v_x_3070_);
v___x_3600_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3600_;
}
else
{
lean_object* v_doc_x3f_3601_; 
v_doc_x3f_3601_ = l_Lean_Syntax_getArg(v___x_3596_, v___x_3119_);
lean_dec(v___x_3596_);
if (v___x_3597_ == 0)
{
lean_object* v___x_3604_; uint8_t v___x_3605_; 
v___x_3604_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7));
lean_inc(v_doc_x3f_3601_);
v___x_3605_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3601_, v___x_3604_);
if (v___x_3605_ == 0)
{
lean_object* v___x_3606_; 
lean_dec(v_doc_x3f_3601_);
lean_dec(v_x_3070_);
v___x_3606_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3606_;
}
else
{
goto v___jp_3602_;
}
}
else
{
goto v___jp_3602_;
}
v___jp_3602_:
{
lean_object* v___x_3603_; 
v___x_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3603_, 0, v_doc_x3f_3601_);
v_doc_x3f_3580_ = v___x_3603_;
v___y_3581_ = v_a_3071_;
v___y_3582_ = v_a_3072_;
goto v___jp_3579_;
}
}
}
else
{
lean_object* v___x_3607_; 
lean_dec(v___x_3596_);
v___x_3607_ = lean_box(0);
v_doc_x3f_3580_ = v___x_3607_;
v___y_3581_ = v_a_3071_;
v___y_3582_ = v_a_3072_;
goto v___jp_3579_;
}
v___jp_3120_:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
lean_inc_ref_n(v___y_3126_, 2);
v___x_3137_ = l_Array_append___redArg(v___y_3126_, v___y_3136_);
lean_dec_ref(v___y_3136_);
lean_inc_n(v___y_3123_, 3);
lean_inc_n(v___y_3125_, 6);
v___x_3138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3138_, 0, v___y_3125_);
lean_ctor_set(v___x_3138_, 1, v___y_3123_);
lean_ctor_set(v___x_3138_, 2, v___x_3137_);
v___x_3139_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3139_, 0, v___y_3125_);
lean_ctor_set(v___x_3139_, 1, v___y_3123_);
lean_ctor_set(v___x_3139_, 2, v___y_3126_);
lean_inc_ref(v___x_3139_);
lean_inc(v___y_3128_);
v___x_3140_ = l_Lean_Syntax_node1(v___y_3125_, v___y_3128_, v___x_3139_);
lean_inc_ref(v___y_3130_);
v___x_3141_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___y_3125_);
lean_ctor_set(v___x_3141_, 1, v___y_3130_);
lean_inc_ref(v___y_3135_);
v___x_3142_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___y_3125_);
lean_ctor_set(v___x_3142_, 1, v___y_3135_);
v___x_3143_ = l_Lean_Syntax_node2(v___y_3125_, v___y_3123_, v___x_3142_, v___y_3129_);
if (lean_obj_tag(v___y_3121_) == 1)
{
lean_object* v_val_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v_val_3144_ = lean_ctor_get(v___y_3121_, 0);
lean_inc(v_val_3144_);
lean_dec_ref_known(v___y_3121_, 1);
v___x_3145_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___y_3125_);
v___x_3146_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___y_3125_);
lean_ctor_set(v___x_3146_, 1, v___x_3145_);
v___x_3147_ = l_Array_mkArray2___redArg(v___x_3146_, v_val_3144_);
v___y_3077_ = v___y_3122_;
v___y_3078_ = v___x_3138_;
v___y_3079_ = v___y_3123_;
v___y_3080_ = v___y_3124_;
v___y_3081_ = v___y_3125_;
v___y_3082_ = v___x_3143_;
v___y_3083_ = v___y_3127_;
v___y_3084_ = v___y_3126_;
v___y_3085_ = v___x_3140_;
v___y_3086_ = v___x_3141_;
v___y_3087_ = v___y_3131_;
v___y_3088_ = v___x_3139_;
v___y_3089_ = v___y_3132_;
v___y_3090_ = v___y_3133_;
v___y_3091_ = v___y_3134_;
v___y_3092_ = v___x_3147_;
goto v___jp_3076_;
}
else
{
lean_object* v___x_3148_; 
lean_dec(v___y_3121_);
v___x_3148_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3077_ = v___y_3122_;
v___y_3078_ = v___x_3138_;
v___y_3079_ = v___y_3123_;
v___y_3080_ = v___y_3124_;
v___y_3081_ = v___y_3125_;
v___y_3082_ = v___x_3143_;
v___y_3083_ = v___y_3127_;
v___y_3084_ = v___y_3126_;
v___y_3085_ = v___x_3140_;
v___y_3086_ = v___x_3141_;
v___y_3087_ = v___y_3131_;
v___y_3088_ = v___x_3139_;
v___y_3089_ = v___y_3132_;
v___y_3090_ = v___y_3133_;
v___y_3091_ = v___y_3134_;
v___y_3092_ = v___x_3148_;
goto v___jp_3076_;
}
}
v___jp_3149_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3164_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
v___x_3165_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
if (lean_obj_tag(v___y_3158_) == 1)
{
lean_object* v_val_3166_; lean_object* v___x_3167_; 
v_val_3166_ = lean_ctor_get(v___y_3158_, 0);
lean_inc(v_val_3166_);
lean_dec_ref_known(v___y_3158_, 1);
v___x_3167_ = l_Array_mkArray1___redArg(v_val_3166_);
v___y_3121_ = v___y_3150_;
v___y_3122_ = v___y_3151_;
v___y_3123_ = v___y_3152_;
v___y_3124_ = v___x_3165_;
v___y_3125_ = v___y_3153_;
v___y_3126_ = v___y_3154_;
v___y_3127_ = v___y_3155_;
v___y_3128_ = v___y_3156_;
v___y_3129_ = v___y_3157_;
v___y_3130_ = v___x_3164_;
v___y_3131_ = v___y_3159_;
v___y_3132_ = v___y_3160_;
v___y_3133_ = v___y_3161_;
v___y_3134_ = v___y_3162_;
v___y_3135_ = v___y_3163_;
v___y_3136_ = v___x_3167_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3168_; 
lean_dec(v___y_3158_);
v___x_3168_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3121_ = v___y_3150_;
v___y_3122_ = v___y_3151_;
v___y_3123_ = v___y_3152_;
v___y_3124_ = v___x_3165_;
v___y_3125_ = v___y_3153_;
v___y_3126_ = v___y_3154_;
v___y_3127_ = v___y_3155_;
v___y_3128_ = v___y_3156_;
v___y_3129_ = v___y_3157_;
v___y_3130_ = v___x_3164_;
v___y_3131_ = v___y_3159_;
v___y_3132_ = v___y_3160_;
v___y_3133_ = v___y_3161_;
v___y_3134_ = v___y_3162_;
v___y_3135_ = v___y_3163_;
v___y_3136_ = v___x_3168_;
goto v___jp_3120_;
}
}
v___jp_3169_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; size_t v_sz_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
lean_inc_ref_n(v___y_3178_, 2);
v___x_3193_ = l_Array_append___redArg(v___y_3178_, v___y_3192_);
lean_dec_ref(v___y_3192_);
lean_inc_n(v___y_3173_, 3);
lean_inc_n(v___y_3174_, 9);
v___x_3194_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3194_, 0, v___y_3174_);
lean_ctor_set(v___x_3194_, 1, v___y_3173_);
lean_ctor_set(v___x_3194_, 2, v___x_3193_);
v___x_3195_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
v___x_3196_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
v___x_3197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___y_3174_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
v___x_3198_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__6));
v___x_3199_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3199_, 0, v___y_3174_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
v___x_3200_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_3201_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___y_3174_);
lean_ctor_set(v___x_3201_, 1, v___x_3200_);
v___x_3202_ = l_Nat_reprFast(v___y_3176_);
v___x_3203_ = lean_box(2);
v___x_3204_ = l_Lean_Syntax_mkNumLit(v___x_3202_, v___x_3203_);
v___x_3205_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_3206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___y_3174_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = l_Lean_Syntax_node5(v___y_3174_, v___x_3195_, v___x_3197_, v___x_3199_, v___x_3201_, v___x_3204_, v___x_3206_);
v___x_3208_ = l_Lean_Syntax_node1(v___y_3174_, v___y_3173_, v___x_3207_);
v_sz_3209_ = lean_array_size(v___y_3181_);
v___x_3210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_3209_, v___y_3175_, v___y_3181_);
v___x_3211_ = l_Array_append___redArg(v___y_3178_, v___x_3210_);
lean_dec_ref(v___x_3210_);
v___x_3212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3212_, 0, v___y_3174_);
lean_ctor_set(v___x_3212_, 1, v___y_3173_);
lean_ctor_set(v___x_3212_, 2, v___x_3211_);
v___x_3213_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_3214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___y_3174_);
lean_ctor_set(v___x_3214_, 1, v___x_3213_);
v___x_3215_ = lean_unsigned_to_nat(10u);
v___x_3216_ = lean_mk_empty_array_with_capacity(v___x_3215_);
v___x_3217_ = lean_array_push(v___x_3216_, v___y_3183_);
v___x_3218_ = lean_array_push(v___x_3217_, v___y_3184_);
v___x_3219_ = lean_array_push(v___x_3218_, v___y_3172_);
v___x_3220_ = lean_array_push(v___x_3219_, v___y_3187_);
v___x_3221_ = lean_array_push(v___x_3220_, v___y_3182_);
v___x_3222_ = lean_array_push(v___x_3221_, v___x_3194_);
v___x_3223_ = lean_array_push(v___x_3222_, v___x_3208_);
v___x_3224_ = lean_array_push(v___x_3223_, v___x_3212_);
v___x_3225_ = lean_array_push(v___x_3224_, v___x_3214_);
lean_inc(v___y_3180_);
v___x_3226_ = lean_array_push(v___x_3225_, v___y_3180_);
lean_inc(v___y_3188_);
v___x_3227_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3227_, 0, v___y_3174_);
lean_ctor_set(v___x_3227_, 1, v___y_3188_);
lean_ctor_set(v___x_3227_, 2, v___x_3226_);
v___x_3228_ = l_Lean_Elab_Command_elabSyntax(v___x_3227_, v___y_3171_, v___y_3177_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3229_);
lean_dec_ref_known(v___x_3228_, 1);
v___x_3230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3203_);
lean_ctor_set(v___x_3230_, 1, v_a_3229_);
lean_ctor_set(v___x_3230_, 2, v___y_3190_);
v___x_3231_ = l_Lean_Elab_Command_getRef___redArg(v___y_3171_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3232_);
lean_dec_ref_known(v___x_3231_, 1);
v___x_3233_ = l_Lean_SourceInfo_fromRef(v_a_3232_, v___y_3191_);
lean_dec(v_a_3232_);
v___x_3234_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3171_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_quotContext_x3f_3235_; 
lean_dec_ref_known(v___x_3234_, 1);
v_quotContext_x3f_3235_ = lean_ctor_get(v___y_3171_, 5);
if (lean_obj_tag(v_quotContext_x3f_3235_) == 0)
{
lean_object* v___x_3236_; 
v___x_3236_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3177_);
lean_dec_ref(v___x_3236_);
v___y_3150_ = v___y_3170_;
v___y_3151_ = v___y_3171_;
v___y_3152_ = v___y_3173_;
v___y_3153_ = v___x_3233_;
v___y_3154_ = v___y_3178_;
v___y_3155_ = v___y_3177_;
v___y_3156_ = v___y_3179_;
v___y_3157_ = v___y_3180_;
v___y_3158_ = v___y_3185_;
v___y_3159_ = v___x_3230_;
v___y_3160_ = v___y_3186_;
v___y_3161_ = v___y_3189_;
v___y_3162_ = v___x_3205_;
v___y_3163_ = v___x_3213_;
goto v___jp_3149_;
}
else
{
v___y_3150_ = v___y_3170_;
v___y_3151_ = v___y_3171_;
v___y_3152_ = v___y_3173_;
v___y_3153_ = v___x_3233_;
v___y_3154_ = v___y_3178_;
v___y_3155_ = v___y_3177_;
v___y_3156_ = v___y_3179_;
v___y_3157_ = v___y_3180_;
v___y_3158_ = v___y_3185_;
v___y_3159_ = v___x_3230_;
v___y_3160_ = v___y_3186_;
v___y_3161_ = v___y_3189_;
v___y_3162_ = v___x_3205_;
v___y_3163_ = v___x_3213_;
goto v___jp_3149_;
}
}
else
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
lean_dec(v___x_3233_);
lean_dec_ref_known(v___x_3230_, 3);
lean_dec(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec(v___y_3180_);
lean_dec(v___y_3170_);
v_a_3237_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3234_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3234_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec_ref_known(v___x_3230_, 3);
lean_dec(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec(v___y_3180_);
lean_dec(v___y_3170_);
v_a_3245_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3231_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3231_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
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
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec(v___y_3180_);
lean_dec(v___y_3170_);
v_a_3253_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3228_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3228_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
v___jp_3261_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
lean_inc_ref(v___y_3269_);
v___x_3285_ = l_Array_append___redArg(v___y_3269_, v___y_3284_);
lean_dec_ref(v___y_3284_);
lean_inc(v___y_3265_);
lean_inc(v___y_3266_);
v___x_3286_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3286_, 0, v___y_3266_);
lean_ctor_set(v___x_3286_, 1, v___y_3265_);
lean_ctor_set(v___x_3286_, 2, v___x_3285_);
if (lean_obj_tag(v___y_3276_) == 1)
{
lean_object* v_val_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v_val_3287_ = lean_ctor_get(v___y_3276_, 0);
lean_inc(v_val_3287_);
lean_dec_ref_known(v___y_3276_, 1);
v___x_3288_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
v___x_3289_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc_n(v___y_3266_, 5);
v___x_3290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___y_3266_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
v___x_3291_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__9));
v___x_3292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___y_3266_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_3294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___y_3266_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
v___x_3295_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_3296_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___y_3266_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
v___x_3297_ = l_Lean_Syntax_node5(v___y_3266_, v___x_3288_, v___x_3290_, v___x_3292_, v___x_3294_, v_val_3287_, v___x_3296_);
v___x_3298_ = l_Array_mkArray1___redArg(v___x_3297_);
v___y_3170_ = v___y_3262_;
v___y_3171_ = v___y_3263_;
v___y_3172_ = v___y_3264_;
v___y_3173_ = v___y_3265_;
v___y_3174_ = v___y_3266_;
v___y_3175_ = v___y_3267_;
v___y_3176_ = v___y_3268_;
v___y_3177_ = v___y_3270_;
v___y_3178_ = v___y_3269_;
v___y_3179_ = v___y_3271_;
v___y_3180_ = v___y_3272_;
v___y_3181_ = v___y_3273_;
v___y_3182_ = v___x_3286_;
v___y_3183_ = v___y_3275_;
v___y_3184_ = v___y_3274_;
v___y_3185_ = v___y_3277_;
v___y_3186_ = v___y_3279_;
v___y_3187_ = v___y_3278_;
v___y_3188_ = v___y_3280_;
v___y_3189_ = v___y_3282_;
v___y_3190_ = v___y_3281_;
v___y_3191_ = v___y_3283_;
v___y_3192_ = v___x_3298_;
goto v___jp_3169_;
}
else
{
lean_object* v___x_3299_; 
lean_dec(v___y_3276_);
v___x_3299_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3170_ = v___y_3262_;
v___y_3171_ = v___y_3263_;
v___y_3172_ = v___y_3264_;
v___y_3173_ = v___y_3265_;
v___y_3174_ = v___y_3266_;
v___y_3175_ = v___y_3267_;
v___y_3176_ = v___y_3268_;
v___y_3177_ = v___y_3270_;
v___y_3178_ = v___y_3269_;
v___y_3179_ = v___y_3271_;
v___y_3180_ = v___y_3272_;
v___y_3181_ = v___y_3273_;
v___y_3182_ = v___x_3286_;
v___y_3183_ = v___y_3275_;
v___y_3184_ = v___y_3274_;
v___y_3185_ = v___y_3277_;
v___y_3186_ = v___y_3279_;
v___y_3187_ = v___y_3278_;
v___y_3188_ = v___y_3280_;
v___y_3189_ = v___y_3282_;
v___y_3190_ = v___y_3281_;
v___y_3191_ = v___y_3283_;
v___y_3192_ = v___x_3299_;
goto v___jp_3169_;
}
}
v___jp_3300_:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
lean_inc_ref(v___y_3309_);
v___x_3325_ = l_Array_append___redArg(v___y_3309_, v___y_3324_);
lean_dec_ref(v___y_3324_);
lean_inc(v___y_3304_);
lean_inc(v___y_3305_);
v___x_3326_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3326_, 0, v___y_3305_);
lean_ctor_set(v___x_3326_, 1, v___y_3304_);
lean_ctor_set(v___x_3326_, 2, v___x_3325_);
v___x_3327_ = l_Lean_SourceInfo_fromRef(v___y_3314_, v___x_3117_);
lean_dec(v___y_3314_);
lean_inc_ref(v___y_3316_);
v___x_3328_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3327_);
lean_ctor_set(v___x_3328_, 1, v___y_3316_);
if (lean_obj_tag(v___y_3308_) == 1)
{
lean_object* v_val_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v_val_3329_ = lean_ctor_get(v___y_3308_, 0);
lean_inc(v_val_3329_);
lean_dec_ref_known(v___y_3308_, 1);
v___x_3330_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
v___x_3331_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc_n(v___y_3305_, 2);
v___x_3332_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___y_3305_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
v___x_3333_ = l_Lean_Syntax_node2(v___y_3305_, v___x_3330_, v___x_3332_, v_val_3329_);
v___x_3334_ = l_Array_mkArray1___redArg(v___x_3333_);
v___y_3262_ = v___y_3301_;
v___y_3263_ = v___y_3302_;
v___y_3264_ = v___y_3303_;
v___y_3265_ = v___y_3304_;
v___y_3266_ = v___y_3305_;
v___y_3267_ = v___y_3306_;
v___y_3268_ = v___y_3307_;
v___y_3269_ = v___y_3309_;
v___y_3270_ = v___y_3310_;
v___y_3271_ = v___y_3312_;
v___y_3272_ = v___y_3311_;
v___y_3273_ = v___y_3313_;
v___y_3274_ = v___x_3326_;
v___y_3275_ = v___y_3315_;
v___y_3276_ = v___y_3317_;
v___y_3277_ = v___y_3318_;
v___y_3278_ = v___x_3328_;
v___y_3279_ = v___y_3319_;
v___y_3280_ = v___y_3320_;
v___y_3281_ = v___y_3322_;
v___y_3282_ = v___y_3321_;
v___y_3283_ = v___y_3323_;
v___y_3284_ = v___x_3334_;
goto v___jp_3261_;
}
else
{
lean_object* v___x_3335_; 
lean_dec(v___y_3308_);
v___x_3335_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3262_ = v___y_3301_;
v___y_3263_ = v___y_3302_;
v___y_3264_ = v___y_3303_;
v___y_3265_ = v___y_3304_;
v___y_3266_ = v___y_3305_;
v___y_3267_ = v___y_3306_;
v___y_3268_ = v___y_3307_;
v___y_3269_ = v___y_3309_;
v___y_3270_ = v___y_3310_;
v___y_3271_ = v___y_3312_;
v___y_3272_ = v___y_3311_;
v___y_3273_ = v___y_3313_;
v___y_3274_ = v___x_3326_;
v___y_3275_ = v___y_3315_;
v___y_3276_ = v___y_3317_;
v___y_3277_ = v___y_3318_;
v___y_3278_ = v___x_3328_;
v___y_3279_ = v___y_3319_;
v___y_3280_ = v___y_3320_;
v___y_3281_ = v___y_3322_;
v___y_3282_ = v___y_3321_;
v___y_3283_ = v___y_3323_;
v___y_3284_ = v___x_3335_;
goto v___jp_3261_;
}
}
v___jp_3336_:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
lean_inc_ref(v___y_3344_);
v___x_3361_ = l_Array_append___redArg(v___y_3344_, v___y_3360_);
lean_dec_ref(v___y_3360_);
lean_inc(v___y_3340_);
lean_inc(v___y_3341_);
v___x_3362_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3362_, 0, v___y_3341_);
lean_ctor_set(v___x_3362_, 1, v___y_3340_);
lean_ctor_set(v___x_3362_, 2, v___x_3361_);
if (lean_obj_tag(v___y_3359_) == 1)
{
lean_object* v_val_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v_val_3363_ = lean_ctor_get(v___y_3359_, 0);
lean_inc(v_val_3363_);
lean_dec_ref_known(v___y_3359_, 1);
v___x_3364_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(v___y_3357_);
v___x_3365_ = l_Lean_Name_mkStr4(v___x_3074_, v___x_3075_, v___y_3357_, v___x_3364_);
v___x_3366_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc_n(v___y_3341_, 4);
v___x_3367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___y_3341_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
lean_inc_ref(v___y_3344_);
v___x_3368_ = l_Array_append___redArg(v___y_3344_, v_val_3363_);
lean_dec(v_val_3363_);
lean_inc(v___y_3340_);
v___x_3369_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3369_, 0, v___y_3341_);
lean_ctor_set(v___x_3369_, 1, v___y_3340_);
lean_ctor_set(v___x_3369_, 2, v___x_3368_);
v___x_3370_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_3371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___y_3341_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v___x_3372_ = l_Lean_Syntax_node3(v___y_3341_, v___x_3365_, v___x_3367_, v___x_3369_, v___x_3371_);
v___x_3373_ = l_Array_mkArray1___redArg(v___x_3372_);
v___y_3301_ = v___y_3337_;
v___y_3302_ = v___y_3338_;
v___y_3303_ = v___y_3339_;
v___y_3304_ = v___y_3340_;
v___y_3305_ = v___y_3341_;
v___y_3306_ = v___y_3342_;
v___y_3307_ = v___y_3343_;
v___y_3308_ = v___y_3345_;
v___y_3309_ = v___y_3344_;
v___y_3310_ = v___y_3346_;
v___y_3311_ = v___y_3347_;
v___y_3312_ = v___y_3348_;
v___y_3313_ = v___y_3350_;
v___y_3314_ = v___y_3349_;
v___y_3315_ = v___x_3362_;
v___y_3316_ = v___y_3351_;
v___y_3317_ = v___y_3352_;
v___y_3318_ = v___y_3353_;
v___y_3319_ = v___y_3354_;
v___y_3320_ = v___y_3355_;
v___y_3321_ = v___y_3357_;
v___y_3322_ = v___y_3356_;
v___y_3323_ = v___y_3358_;
v___y_3324_ = v___x_3373_;
goto v___jp_3300_;
}
else
{
lean_object* v___x_3374_; 
lean_dec(v___y_3359_);
v___x_3374_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3301_ = v___y_3337_;
v___y_3302_ = v___y_3338_;
v___y_3303_ = v___y_3339_;
v___y_3304_ = v___y_3340_;
v___y_3305_ = v___y_3341_;
v___y_3306_ = v___y_3342_;
v___y_3307_ = v___y_3343_;
v___y_3308_ = v___y_3345_;
v___y_3309_ = v___y_3344_;
v___y_3310_ = v___y_3346_;
v___y_3311_ = v___y_3347_;
v___y_3312_ = v___y_3348_;
v___y_3313_ = v___y_3350_;
v___y_3314_ = v___y_3349_;
v___y_3315_ = v___x_3362_;
v___y_3316_ = v___y_3351_;
v___y_3317_ = v___y_3352_;
v___y_3318_ = v___y_3353_;
v___y_3319_ = v___y_3354_;
v___y_3320_ = v___y_3355_;
v___y_3321_ = v___y_3357_;
v___y_3322_ = v___y_3356_;
v___y_3323_ = v___y_3358_;
v___y_3324_ = v___x_3374_;
goto v___jp_3300_;
}
}
v___jp_3375_:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3395_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__12));
v___x_3396_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__13));
v___x_3397_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_3398_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v___y_3389_) == 1)
{
lean_object* v_val_3399_; lean_object* v___x_3400_; 
v_val_3399_ = lean_ctor_get(v___y_3389_, 0);
lean_inc(v_val_3399_);
v___x_3400_ = l_Array_mkArray1___redArg(v_val_3399_);
v___y_3337_ = v___y_3376_;
v___y_3338_ = v___y_3377_;
v___y_3339_ = v___y_3378_;
v___y_3340_ = v___x_3397_;
v___y_3341_ = v___y_3379_;
v___y_3342_ = v___y_3380_;
v___y_3343_ = v___y_3381_;
v___y_3344_ = v___x_3398_;
v___y_3345_ = v___y_3382_;
v___y_3346_ = v___y_3383_;
v___y_3347_ = v___y_3384_;
v___y_3348_ = v___y_3385_;
v___y_3349_ = v___y_3386_;
v___y_3350_ = v___y_3387_;
v___y_3351_ = v___x_3395_;
v___y_3352_ = v___y_3388_;
v___y_3353_ = v___y_3389_;
v___y_3354_ = v___y_3390_;
v___y_3355_ = v___x_3396_;
v___y_3356_ = v___y_3392_;
v___y_3357_ = v___y_3391_;
v___y_3358_ = v___y_3393_;
v___y_3359_ = v___y_3394_;
v___y_3360_ = v___x_3400_;
goto v___jp_3336_;
}
else
{
lean_object* v___x_3401_; 
v___x_3401_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3337_ = v___y_3376_;
v___y_3338_ = v___y_3377_;
v___y_3339_ = v___y_3378_;
v___y_3340_ = v___x_3397_;
v___y_3341_ = v___y_3379_;
v___y_3342_ = v___y_3380_;
v___y_3343_ = v___y_3381_;
v___y_3344_ = v___x_3398_;
v___y_3345_ = v___y_3382_;
v___y_3346_ = v___y_3383_;
v___y_3347_ = v___y_3384_;
v___y_3348_ = v___y_3385_;
v___y_3349_ = v___y_3386_;
v___y_3350_ = v___y_3387_;
v___y_3351_ = v___x_3395_;
v___y_3352_ = v___y_3388_;
v___y_3353_ = v___y_3389_;
v___y_3354_ = v___y_3390_;
v___y_3355_ = v___x_3396_;
v___y_3356_ = v___y_3392_;
v___y_3357_ = v___y_3391_;
v___y_3358_ = v___y_3393_;
v___y_3359_ = v___y_3394_;
v___y_3360_ = v___x_3401_;
goto v___jp_3336_;
}
}
v___jp_3402_:
{
lean_object* v___x_3419_; lean_object* v_args_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3419_ = l_Lean_Syntax_getArg(v___y_3413_, v___y_3411_);
lean_dec(v___y_3413_);
v_args_3420_ = l_Lean_Syntax_getArgs(v___y_3414_);
lean_dec(v___y_3414_);
v___x_3421_ = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(v___x_3421_, 0, v___y_3410_);
v___x_3422_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v___x_3421_, v___y_3417_, v___y_3418_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; size_t v_sz_3424_; size_t v___x_3425_; lean_object* v___x_3426_; 
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc(v_a_3423_);
lean_dec_ref_known(v___x_3422_, 1);
v_sz_3424_ = lean_array_size(v_args_3420_);
v___x_3425_ = ((size_t)0ULL);
v___x_3426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_3424_, v___x_3425_, v_args_3420_, v___y_3417_, v___y_3418_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v___x_3428_; lean_object* v_fst_3429_; lean_object* v_snd_3430_; lean_object* v___x_3431_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3427_);
lean_dec_ref_known(v___x_3426_, 1);
v___x_3428_ = l_Array_unzip___redArg(v_a_3427_);
lean_dec(v_a_3427_);
v_fst_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_fst_3429_);
v_snd_3430_ = lean_ctor_get(v___x_3428_, 1);
lean_inc(v_snd_3430_);
lean_dec_ref(v___x_3428_);
v___x_3431_ = l_Lean_Elab_Command_getRef___redArg(v___y_3417_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; uint8_t v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref_known(v___x_3431_, 1);
v___x_3433_ = 0;
v___x_3434_ = l_Lean_SourceInfo_fromRef(v_a_3432_, v___x_3433_);
lean_dec(v_a_3432_);
v___x_3435_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3417_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_quotContext_x3f_3436_; 
lean_dec_ref_known(v___x_3435_, 1);
v_quotContext_x3f_3436_ = lean_ctor_get(v___y_3417_, 5);
if (lean_obj_tag(v_quotContext_x3f_3436_) == 0)
{
lean_object* v___x_3437_; 
v___x_3437_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3418_);
lean_dec_ref(v___x_3437_);
v___y_3376_ = v_expectedType_x3f_3416_;
v___y_3377_ = v___y_3417_;
v___y_3378_ = v___y_3403_;
v___y_3379_ = v___x_3434_;
v___y_3380_ = v___x_3425_;
v___y_3381_ = v_a_3423_;
v___y_3382_ = v___y_3404_;
v___y_3383_ = v___y_3418_;
v___y_3384_ = v___y_3405_;
v___y_3385_ = v___y_3406_;
v___y_3386_ = v___y_3407_;
v___y_3387_ = v_fst_3429_;
v___y_3388_ = v___y_3408_;
v___y_3389_ = v___y_3409_;
v___y_3390_ = v___x_3419_;
v___y_3391_ = v___y_3412_;
v___y_3392_ = v_snd_3430_;
v___y_3393_ = v___x_3433_;
v___y_3394_ = v___y_3415_;
goto v___jp_3375_;
}
else
{
v___y_3376_ = v_expectedType_x3f_3416_;
v___y_3377_ = v___y_3417_;
v___y_3378_ = v___y_3403_;
v___y_3379_ = v___x_3434_;
v___y_3380_ = v___x_3425_;
v___y_3381_ = v_a_3423_;
v___y_3382_ = v___y_3404_;
v___y_3383_ = v___y_3418_;
v___y_3384_ = v___y_3405_;
v___y_3385_ = v___y_3406_;
v___y_3386_ = v___y_3407_;
v___y_3387_ = v_fst_3429_;
v___y_3388_ = v___y_3408_;
v___y_3389_ = v___y_3409_;
v___y_3390_ = v___x_3419_;
v___y_3391_ = v___y_3412_;
v___y_3392_ = v_snd_3430_;
v___y_3393_ = v___x_3433_;
v___y_3394_ = v___y_3415_;
goto v___jp_3375_;
}
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec(v___x_3434_);
lean_dec(v_snd_3430_);
lean_dec(v_fst_3429_);
lean_dec(v_a_3423_);
lean_dec(v___x_3419_);
lean_dec(v_expectedType_x3f_3416_);
lean_dec(v___y_3415_);
lean_dec(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec(v___y_3403_);
v_a_3438_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3435_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3435_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
lean_dec(v_snd_3430_);
lean_dec(v_fst_3429_);
lean_dec(v_a_3423_);
lean_dec(v___x_3419_);
lean_dec(v_expectedType_x3f_3416_);
lean_dec(v___y_3415_);
lean_dec(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec(v___y_3403_);
v_a_3446_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3431_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3431_);
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
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
else
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
lean_dec(v_a_3423_);
lean_dec(v___x_3419_);
lean_dec(v_expectedType_x3f_3416_);
lean_dec(v___y_3415_);
lean_dec(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec(v___y_3403_);
v_a_3454_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3456_ = v___x_3426_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3426_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3454_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref(v_args_3420_);
lean_dec(v___x_3419_);
lean_dec(v_expectedType_x3f_3416_);
lean_dec(v___y_3415_);
lean_dec(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec(v___y_3403_);
v_a_3462_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3422_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3422_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
v___jp_3470_:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; uint8_t v___x_3488_; 
v___x_3485_ = lean_unsigned_to_nat(8u);
v___x_3486_ = l_Lean_Syntax_getArg(v_x_3070_, v___x_3485_);
v___x_3487_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__15));
lean_inc(v___x_3486_);
v___x_3488_ = l_Lean_Syntax_isOfKind(v___x_3486_, v___x_3487_);
if (v___x_3488_ == 0)
{
lean_object* v___x_3489_; 
lean_dec(v___x_3486_);
lean_dec(v_prio_x3f_3482_);
lean_dec(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec(v___y_3478_);
lean_dec(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec(v_x_3070_);
v___x_3489_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3489_;
}
else
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; 
v___x_3490_ = lean_unsigned_to_nat(7u);
v___x_3491_ = l_Lean_Syntax_getArg(v_x_3070_, v___x_3490_);
lean_dec(v_x_3070_);
v___x_3492_ = l_Lean_Syntax_getArg(v___x_3486_, v___y_3476_);
v___x_3493_ = l_Lean_Syntax_getArg(v___x_3486_, v___y_3471_);
v___x_3494_ = l_Lean_Syntax_isNone(v___x_3493_);
if (v___x_3494_ == 0)
{
uint8_t v___x_3495_; 
lean_inc(v___x_3493_);
v___x_3495_ = l_Lean_Syntax_matchesNull(v___x_3493_, v___y_3471_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3496_; 
lean_dec(v___x_3493_);
lean_dec(v___x_3492_);
lean_dec(v___x_3491_);
lean_dec(v___x_3486_);
lean_dec(v_prio_x3f_3482_);
lean_dec(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec(v___y_3478_);
lean_dec(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec(v___y_3472_);
v___x_3496_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3496_;
}
else
{
lean_object* v_expectedType_x3f_3497_; lean_object* v___x_3498_; 
v_expectedType_x3f_3497_ = l_Lean_Syntax_getArg(v___x_3493_, v___y_3476_);
lean_dec(v___x_3493_);
v___x_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3498_, 0, v_expectedType_x3f_3497_);
v___y_3403_ = v___y_3473_;
v___y_3404_ = v___y_3478_;
v___y_3405_ = v___x_3492_;
v___y_3406_ = v___y_3479_;
v___y_3407_ = v___y_3481_;
v___y_3408_ = v___y_3472_;
v___y_3409_ = v___y_3474_;
v___y_3410_ = v_prio_x3f_3482_;
v___y_3411_ = v___y_3475_;
v___y_3412_ = v___y_3477_;
v___y_3413_ = v___x_3486_;
v___y_3414_ = v___x_3491_;
v___y_3415_ = v___y_3480_;
v_expectedType_x3f_3416_ = v___x_3498_;
v___y_3417_ = v___y_3483_;
v___y_3418_ = v___y_3484_;
goto v___jp_3402_;
}
}
else
{
lean_object* v___x_3499_; 
lean_dec(v___x_3493_);
v___x_3499_ = lean_box(0);
v___y_3403_ = v___y_3473_;
v___y_3404_ = v___y_3478_;
v___y_3405_ = v___x_3492_;
v___y_3406_ = v___y_3479_;
v___y_3407_ = v___y_3481_;
v___y_3408_ = v___y_3472_;
v___y_3409_ = v___y_3474_;
v___y_3410_ = v_prio_x3f_3482_;
v___y_3411_ = v___y_3475_;
v___y_3412_ = v___y_3477_;
v___y_3413_ = v___x_3486_;
v___y_3414_ = v___x_3491_;
v___y_3415_ = v___y_3480_;
v_expectedType_x3f_3416_ = v___x_3499_;
v___y_3417_ = v___y_3483_;
v___y_3418_ = v___y_3484_;
goto v___jp_3402_;
}
}
}
v___jp_3500_:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; 
v___x_3515_ = lean_unsigned_to_nat(6u);
v___x_3516_ = l_Lean_Syntax_getArg(v_x_3070_, v___x_3515_);
v___x_3517_ = l_Lean_Syntax_isNone(v___x_3516_);
if (v___x_3517_ == 0)
{
uint8_t v___x_3518_; 
lean_inc(v___x_3516_);
v___x_3518_ = l_Lean_Syntax_matchesNull(v___x_3516_, v___y_3505_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; 
lean_dec(v___x_3516_);
lean_dec(v_name_x3f_3512_);
lean_dec(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec(v___y_3508_);
lean_dec(v___y_3503_);
lean_dec(v___y_3501_);
lean_dec(v_x_3070_);
v___x_3519_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3519_;
}
else
{
lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v___x_3520_ = l_Lean_Syntax_getArg(v___x_3516_, v___x_3119_);
lean_dec(v___x_3516_);
v___x_3521_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
lean_inc(v___x_3520_);
v___x_3522_ = l_Lean_Syntax_isOfKind(v___x_3520_, v___x_3521_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3523_; 
lean_dec(v___x_3520_);
lean_dec(v_name_x3f_3512_);
lean_dec(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec(v___y_3508_);
lean_dec(v___y_3503_);
lean_dec(v___y_3501_);
lean_dec(v_x_3070_);
v___x_3523_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3523_;
}
else
{
lean_object* v_prio_x3f_3524_; lean_object* v___x_3525_; 
v_prio_x3f_3524_ = l_Lean_Syntax_getArg(v___x_3520_, v___y_3504_);
lean_dec(v___x_3520_);
v___x_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3525_, 0, v_prio_x3f_3524_);
v___y_3471_ = v___y_3502_;
v___y_3472_ = v_name_x3f_3512_;
v___y_3473_ = v___y_3501_;
v___y_3474_ = v___y_3503_;
v___y_3475_ = v___y_3506_;
v___y_3476_ = v___y_3505_;
v___y_3477_ = v___y_3507_;
v___y_3478_ = v___y_3508_;
v___y_3479_ = v___y_3509_;
v___y_3480_ = v___y_3511_;
v___y_3481_ = v___y_3510_;
v_prio_x3f_3482_ = v___x_3525_;
v___y_3483_ = v___y_3513_;
v___y_3484_ = v___y_3514_;
goto v___jp_3470_;
}
}
}
else
{
lean_object* v___x_3526_; 
lean_dec(v___x_3516_);
v___x_3526_ = lean_box(0);
v___y_3471_ = v___y_3502_;
v___y_3472_ = v_name_x3f_3512_;
v___y_3473_ = v___y_3501_;
v___y_3474_ = v___y_3503_;
v___y_3475_ = v___y_3506_;
v___y_3476_ = v___y_3505_;
v___y_3477_ = v___y_3507_;
v___y_3478_ = v___y_3508_;
v___y_3479_ = v___y_3509_;
v___y_3480_ = v___y_3511_;
v___y_3481_ = v___y_3510_;
v_prio_x3f_3482_ = v___x_3526_;
v___y_3483_ = v___y_3513_;
v___y_3484_ = v___y_3514_;
goto v___jp_3470_;
}
}
v___jp_3527_:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; 
v___x_3541_ = lean_unsigned_to_nat(5u);
v___x_3542_ = l_Lean_Syntax_getArg(v_x_3070_, v___x_3541_);
v___x_3543_ = l_Lean_Syntax_isNone(v___x_3542_);
if (v___x_3543_ == 0)
{
uint8_t v___x_3544_; 
lean_inc(v___x_3542_);
v___x_3544_ = l_Lean_Syntax_matchesNull(v___x_3542_, v___y_3533_);
if (v___x_3544_ == 0)
{
lean_object* v___x_3545_; 
lean_dec(v___x_3542_);
lean_dec(v_prec_x3f_3538_);
lean_dec(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec(v_x_3070_);
v___x_3545_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3545_;
}
else
{
lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; 
v___x_3546_ = l_Lean_Syntax_getArg(v___x_3542_, v___x_3119_);
lean_dec(v___x_3542_);
v___x_3547_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
lean_inc(v___x_3546_);
v___x_3548_ = l_Lean_Syntax_isOfKind(v___x_3546_, v___x_3547_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; 
lean_dec(v___x_3546_);
lean_dec(v_prec_x3f_3538_);
lean_dec(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec(v_x_3070_);
v___x_3549_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3549_;
}
else
{
lean_object* v_name_x3f_3550_; lean_object* v___x_3551_; 
v_name_x3f_3550_ = l_Lean_Syntax_getArg(v___x_3546_, v___y_3531_);
lean_dec(v___x_3546_);
v___x_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3551_, 0, v_name_x3f_3550_);
v___y_3501_ = v___y_3529_;
v___y_3502_ = v___y_3528_;
v___y_3503_ = v___y_3530_;
v___y_3504_ = v___y_3531_;
v___y_3505_ = v___y_3533_;
v___y_3506_ = v___y_3532_;
v___y_3507_ = v___y_3534_;
v___y_3508_ = v_prec_x3f_3538_;
v___y_3509_ = v___y_3535_;
v___y_3510_ = v___y_3537_;
v___y_3511_ = v___y_3536_;
v_name_x3f_3512_ = v___x_3551_;
v___y_3513_ = v___y_3539_;
v___y_3514_ = v___y_3540_;
goto v___jp_3500_;
}
}
}
else
{
lean_object* v___x_3552_; 
lean_dec(v___x_3542_);
v___x_3552_ = lean_box(0);
v___y_3501_ = v___y_3529_;
v___y_3502_ = v___y_3528_;
v___y_3503_ = v___y_3530_;
v___y_3504_ = v___y_3531_;
v___y_3505_ = v___y_3533_;
v___y_3506_ = v___y_3532_;
v___y_3507_ = v___y_3534_;
v___y_3508_ = v_prec_x3f_3538_;
v___y_3509_ = v___y_3535_;
v___y_3510_ = v___y_3537_;
v___y_3511_ = v___y_3536_;
v_name_x3f_3512_ = v___x_3552_;
v___y_3513_ = v___y_3539_;
v___y_3514_ = v___y_3540_;
goto v___jp_3500_;
}
}
v___jp_3553_:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; uint8_t v___x_3563_; 
v___x_3559_ = lean_unsigned_to_nat(2u);
v___x_3560_ = l_Lean_Syntax_getArg(v_x_3070_, v___x_3559_);
v___x_3561_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_3562_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v___x_3560_);
v___x_3563_ = l_Lean_Syntax_isOfKind(v___x_3560_, v___x_3562_);
if (v___x_3563_ == 0)
{
lean_object* v___x_3564_; 
lean_dec(v___x_3560_);
lean_dec(v_attrs_x3f_3556_);
lean_dec(v___y_3554_);
lean_dec(v_x_3070_);
v___x_3564_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3564_;
}
else
{
lean_object* v___x_3565_; lean_object* v_tk_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; uint8_t v___x_3569_; 
v___x_3565_ = lean_unsigned_to_nat(3u);
v_tk_3566_ = l_Lean_Syntax_getArg(v_x_3070_, v___x_3565_);
v___x_3567_ = lean_unsigned_to_nat(4u);
v___x_3568_ = l_Lean_Syntax_getArg(v_x_3070_, v___x_3567_);
v___x_3569_ = l_Lean_Syntax_isNone(v___x_3568_);
if (v___x_3569_ == 0)
{
uint8_t v___x_3570_; 
lean_inc(v___x_3568_);
v___x_3570_ = l_Lean_Syntax_matchesNull(v___x_3568_, v___y_3555_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; 
lean_dec(v___x_3568_);
lean_dec(v_tk_3566_);
lean_dec(v___x_3560_);
lean_dec(v_attrs_x3f_3556_);
lean_dec(v___y_3554_);
lean_dec(v_x_3070_);
v___x_3571_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3571_;
}
else
{
lean_object* v___x_3572_; lean_object* v___x_3573_; uint8_t v___x_3574_; 
v___x_3572_ = l_Lean_Syntax_getArg(v___x_3568_, v___x_3119_);
lean_dec(v___x_3568_);
v___x_3573_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
lean_inc(v___x_3572_);
v___x_3574_ = l_Lean_Syntax_isOfKind(v___x_3572_, v___x_3573_);
if (v___x_3574_ == 0)
{
lean_object* v___x_3575_; 
lean_dec(v___x_3572_);
lean_dec(v_tk_3566_);
lean_dec(v___x_3560_);
lean_dec(v_attrs_x3f_3556_);
lean_dec(v___y_3554_);
lean_dec(v_x_3070_);
v___x_3575_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3575_;
}
else
{
lean_object* v_prec_x3f_3576_; lean_object* v___x_3577_; 
v_prec_x3f_3576_ = l_Lean_Syntax_getArg(v___x_3572_, v___y_3555_);
lean_dec(v___x_3572_);
v___x_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3577_, 0, v_prec_x3f_3576_);
v___y_3528_ = v___x_3559_;
v___y_3529_ = v___x_3560_;
v___y_3530_ = v___y_3554_;
v___y_3531_ = v___x_3565_;
v___y_3532_ = v___x_3567_;
v___y_3533_ = v___y_3555_;
v___y_3534_ = v___x_3561_;
v___y_3535_ = v___x_3562_;
v___y_3536_ = v_attrs_x3f_3556_;
v___y_3537_ = v_tk_3566_;
v_prec_x3f_3538_ = v___x_3577_;
v___y_3539_ = v___y_3557_;
v___y_3540_ = v___y_3558_;
goto v___jp_3527_;
}
}
}
else
{
lean_object* v___x_3578_; 
lean_dec(v___x_3568_);
v___x_3578_ = lean_box(0);
v___y_3528_ = v___x_3559_;
v___y_3529_ = v___x_3560_;
v___y_3530_ = v___y_3554_;
v___y_3531_ = v___x_3565_;
v___y_3532_ = v___x_3567_;
v___y_3533_ = v___y_3555_;
v___y_3534_ = v___x_3561_;
v___y_3535_ = v___x_3562_;
v___y_3536_ = v_attrs_x3f_3556_;
v___y_3537_ = v_tk_3566_;
v_prec_x3f_3538_ = v___x_3578_;
v___y_3539_ = v___y_3557_;
v___y_3540_ = v___y_3558_;
goto v___jp_3527_;
}
}
}
v___jp_3579_:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; uint8_t v___x_3585_; 
v___x_3583_ = lean_unsigned_to_nat(1u);
v___x_3584_ = l_Lean_Syntax_getArg(v_x_3070_, v___x_3583_);
v___x_3585_ = l_Lean_Syntax_isNone(v___x_3584_);
if (v___x_3585_ == 0)
{
uint8_t v___x_3586_; 
lean_inc(v___x_3584_);
v___x_3586_ = l_Lean_Syntax_matchesNull(v___x_3584_, v___x_3583_);
if (v___x_3586_ == 0)
{
lean_object* v___x_3587_; 
lean_dec(v___x_3584_);
lean_dec(v_doc_x3f_3580_);
lean_dec(v_x_3070_);
v___x_3587_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3587_;
}
else
{
lean_object* v___x_3588_; lean_object* v___x_3589_; uint8_t v___x_3590_; 
v___x_3588_ = l_Lean_Syntax_getArg(v___x_3584_, v___x_3119_);
lean_dec(v___x_3584_);
v___x_3589_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5));
lean_inc(v___x_3588_);
v___x_3590_ = l_Lean_Syntax_isOfKind(v___x_3588_, v___x_3589_);
if (v___x_3590_ == 0)
{
lean_object* v___x_3591_; 
lean_dec(v___x_3588_);
lean_dec(v_doc_x3f_3580_);
lean_dec(v_x_3070_);
v___x_3591_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3591_;
}
else
{
lean_object* v___x_3592_; lean_object* v_attrs_x3f_3593_; lean_object* v___x_3594_; 
v___x_3592_ = l_Lean_Syntax_getArg(v___x_3588_, v___x_3583_);
lean_dec(v___x_3588_);
v_attrs_x3f_3593_ = l_Lean_Syntax_getArgs(v___x_3592_);
lean_dec(v___x_3592_);
v___x_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3594_, 0, v_attrs_x3f_3593_);
v___y_3554_ = v_doc_x3f_3580_;
v___y_3555_ = v___x_3583_;
v_attrs_x3f_3556_ = v___x_3594_;
v___y_3557_ = v___y_3581_;
v___y_3558_ = v___y_3582_;
goto v___jp_3553_;
}
}
}
else
{
lean_object* v___x_3595_; 
lean_dec(v___x_3584_);
v___x_3595_ = lean_box(0);
v___y_3554_ = v_doc_x3f_3580_;
v___y_3555_ = v___x_3583_;
v_attrs_x3f_3556_ = v___x_3595_;
v___y_3557_ = v___y_3581_;
v___y_3558_ = v___y_3582_;
goto v___jp_3553_;
}
}
}
v___jp_3076_:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
lean_inc_ref(v___y_3084_);
v___x_3093_ = l_Array_append___redArg(v___y_3084_, v___y_3092_);
lean_dec_ref(v___y_3092_);
lean_inc_n(v___y_3079_, 4);
lean_inc_n(v___y_3081_, 11);
v___x_3094_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3094_, 0, v___y_3081_);
lean_ctor_set(v___x_3094_, 1, v___y_3079_);
lean_ctor_set(v___x_3094_, 2, v___x_3093_);
v___x_3095_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc_ref_n(v___y_3090_, 3);
v___x_3096_ = l_Lean_Name_mkStr4(v___x_3074_, v___x_3075_, v___y_3090_, v___x_3095_);
v___x_3097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_3098_ = l_Lean_Name_mkStr4(v___x_3074_, v___x_3075_, v___y_3090_, v___x_3097_);
v___x_3099_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_3100_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___y_3081_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
v___x_3101_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__0));
v___x_3102_ = l_Lean_Name_mkStr4(v___x_3074_, v___x_3075_, v___y_3090_, v___x_3101_);
v___x_3103_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__1));
v___x_3104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___y_3081_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
lean_inc_ref(v___y_3091_);
v___x_3105_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___y_3081_);
lean_ctor_set(v___x_3105_, 1, v___y_3091_);
v___x_3106_ = l_Lean_Syntax_node3(v___y_3081_, v___x_3102_, v___x_3104_, v___y_3087_, v___x_3105_);
v___x_3107_ = l_Lean_Syntax_node1(v___y_3081_, v___y_3079_, v___x_3106_);
v___x_3108_ = l_Lean_Syntax_node1(v___y_3081_, v___y_3079_, v___x_3107_);
v___x_3109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_3110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___y_3081_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
v___x_3111_ = l_Lean_Syntax_node4(v___y_3081_, v___x_3098_, v___x_3100_, v___x_3108_, v___x_3110_, v___y_3089_);
v___x_3112_ = l_Lean_Syntax_node1(v___y_3081_, v___y_3079_, v___x_3111_);
v___x_3113_ = l_Lean_Syntax_node1(v___y_3081_, v___x_3096_, v___x_3112_);
lean_inc(v___y_3088_);
lean_inc(v___y_3080_);
v___x_3114_ = l_Lean_Syntax_node8(v___y_3081_, v___y_3080_, v___y_3078_, v___y_3088_, v___y_3085_, v___y_3086_, v___y_3088_, v___y_3082_, v___x_3094_, v___x_3113_);
v___x_3115_ = l_Lean_Elab_Command_elabCommand(v___x_3114_, v___y_3077_, v___y_3083_);
return v___x_3115_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_elabElab_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3070_ = stack[0].m_obj;
lean_object* v_a_3071_ = stack[1].m_obj;
lean_object* v_a_3072_ = stack[2].m_obj;
lean_object* v_res_3608_;
v_res_3608_ = l_Lean_Elab_Command_elabElab(v_x_3070_, v_a_3071_, v_a_3072_);
stack->m_obj
 = v_res_3608_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___boxed(lean_object* v_x_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_Lean_Elab_Command_elabElab(v_x_3609_, v_a_3610_, v_a_3611_);
lean_dec(v_a_3611_);
lean_dec_ref(v_a_3610_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(lean_object* v_00_u03b1_3614_, lean_object* v_x_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v___x_3618_; 
v___x_3618_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_3615_, v___y_3617_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3619_, lean_object* v_x_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(v_00_u03b1_3619_, v_x_3620_, v___y_3621_, v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec_ref(v_x_3620_);
return v_res_3623_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(lean_object* v_00_u03b1_3624_, lean_object* v_ref_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v___x_3629_; 
v___x_3629_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_3625_);
return v___x_3629_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3625_ = stack[1].m_obj;
lean_object* v___y_3626_ = stack[2].m_obj;
lean_object* v___y_3627_ = stack[3].m_obj;
lean_object* v_res_3630_;
v_res_3630_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(lean_box(0), v_ref_3625_, v___y_3626_, v___y_3627_);
stack->m_obj
 = v_res_3630_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___boxed(lean_object* v_00_u03b1_3631_, lean_object* v_ref_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(v_00_u03b1_3631_, v_ref_3632_, v___y_3633_, v___y_3634_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
return v_res_3636_;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(lean_object* v_00_u03b1_3637_, lean_object* v_x_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_3638_, v___y_3639_, v___y_3640_);
return v___x_3642_;
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3638_ = stack[1].m_obj;
lean_object* v___y_3639_ = stack[2].m_obj;
lean_object* v___y_3640_ = stack[3].m_obj;
lean_object* v_res_3643_;
v_res_3643_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(lean_box(0), v_x_3638_, v___y_3639_, v___y_3640_);
stack->m_obj
 = v_res_3643_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___boxed(lean_object* v_00_u03b1_3644_, lean_object* v_x_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(v_00_u03b1_3644_, v_x_3645_, v___y_3646_, v___y_3647_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
return v_res_3649_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(lean_object* v_as_3650_, lean_object* v_as_x27_3651_, lean_object* v_b_3652_, lean_object* v_a_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_3651_, v_b_3652_, v___y_3654_, v___y_3655_);
return v___x_3657_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3650_ = stack[0].m_obj;
lean_object* v_as_x27_3651_ = stack[1].m_obj;
lean_object* v_b_3652_ = stack[2].m_obj;
lean_object* v___y_3654_ = stack[4].m_obj;
lean_object* v___y_3655_ = stack[5].m_obj;
lean_object* v_res_3658_;
v_res_3658_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(v_as_3650_, v_as_x27_3651_, v_b_3652_, lean_box(0), v___y_3654_, v___y_3655_);
stack->m_obj
 = v_res_3658_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___boxed(lean_object* v_as_3659_, lean_object* v_as_x27_3660_, lean_object* v_b_3661_, lean_object* v_a_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(v_as_3659_, v_as_x27_3660_, v_b_3661_, v_a_3662_, v___y_3663_, v___y_3664_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v_as_x27_3660_);
lean_dec(v_as_3659_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3667_, lean_object* v_m_3668_, lean_object* v_a_3669_){
_start:
{
lean_object* v___x_3670_; 
v___x_3670_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_3668_, v_a_3669_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3671_, lean_object* v_m_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(v_00_u03b2_3671_, v_m_3672_, v_a_3673_);
lean_dec(v_a_3673_);
lean_dec_ref(v_m_3672_);
return v_res_3674_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_3675_, lean_object* v_x_3676_, lean_object* v_x_3677_){
_start:
{
uint8_t v___x_3678_; 
v___x_3678_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_3676_, v_x_3677_);
return v___x_3678_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3676_ = stack[1].m_obj;
lean_object* v_x_3677_ = stack[2].m_obj;
uint8_t v_res_3679_;
v_res_3679_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(lean_box(0), v_x_3676_, v_x_3677_);
stack->m_num = v_res_3679_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3680_, lean_object* v_x_3681_, lean_object* v_x_3682_){
_start:
{
uint8_t v_res_3683_; lean_object* v_r_3684_; 
v_res_3683_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(v_00_u03b2_3680_, v_x_3681_, v_x_3682_);
lean_dec_ref(v_x_3682_);
lean_dec_ref(v_x_3681_);
v_r_3684_ = lean_box(v_res_3683_);
return v_r_3684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_3685_, lean_object* v_a_3686_, lean_object* v_x_3687_){
_start:
{
lean_object* v___x_3688_; 
v___x_3688_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_3686_, v_x_3687_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___boxed(lean_object* v_00_u03b2_3689_, lean_object* v_a_3690_, lean_object* v_x_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(v_00_u03b2_3689_, v_a_3690_, v_x_3691_);
lean_dec(v_x_3691_);
lean_dec(v_a_3690_);
return v_res_3692_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(lean_object* v_00_u03b2_3693_, lean_object* v_x_3694_, size_t v_x_3695_, lean_object* v_x_3696_){
_start:
{
uint8_t v___x_3697_; 
v___x_3697_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_3694_, v_x_3695_, v_x_3696_);
return v___x_3697_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3694_ = stack[1].m_obj;
size_t v_x_3695_ = stack[2].m_num;
lean_object* v_x_3696_ = stack[3].m_obj;
uint8_t v_res_3698_;
v_res_3698_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(lean_box(0), v_x_3694_, v_x_3695_, v_x_3696_);
stack->m_num = v_res_3698_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3699_, lean_object* v_x_3700_, lean_object* v_x_3701_, lean_object* v_x_3702_){
_start:
{
size_t v_x_20226__boxed_3703_; uint8_t v_res_3704_; lean_object* v_r_3705_; 
v_x_20226__boxed_3703_ = lean_unbox_usize(v_x_3701_);
lean_dec(v_x_3701_);
v_res_3704_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(v_00_u03b2_3699_, v_x_3700_, v_x_20226__boxed_3703_, v_x_3702_);
lean_dec_ref(v_x_3702_);
lean_dec_ref(v_x_3700_);
v_r_3705_ = lean_box(v_res_3704_);
return v_r_3705_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(lean_object* v_00_u03b2_3706_, lean_object* v_keys_3707_, lean_object* v_vals_3708_, lean_object* v_heq_3709_, lean_object* v_i_3710_, lean_object* v_k_3711_){
_start:
{
uint8_t v___x_3712_; 
v___x_3712_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_3707_, v_i_3710_, v_k_3711_);
return v___x_3712_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_3707_ = stack[1].m_obj;
lean_object* v_vals_3708_ = stack[2].m_obj;
lean_object* v_i_3710_ = stack[4].m_obj;
lean_object* v_k_3711_ = stack[5].m_obj;
uint8_t v_res_3713_;
v_res_3713_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(lean_box(0), v_keys_3707_, v_vals_3708_, lean_box(0), v_i_3710_, v_k_3711_);
stack->m_num = v_res_3713_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___boxed(lean_object* v_00_u03b2_3714_, lean_object* v_keys_3715_, lean_object* v_vals_3716_, lean_object* v_heq_3717_, lean_object* v_i_3718_, lean_object* v_k_3719_){
_start:
{
uint8_t v_res_3720_; lean_object* v_r_3721_; 
v_res_3720_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(v_00_u03b2_3714_, v_keys_3715_, v_vals_3716_, v_heq_3717_, v_i_3718_, v_k_3719_);
lean_dec_ref(v_k_3719_);
lean_dec_ref(v_vals_3716_);
lean_dec_ref(v_keys_3715_);
v_r_3721_ = lean_box(v_res_3720_);
return v_r_3721_;
}
}
lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1(){
_start:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3729_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3730_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
v___x_3731_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3732_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElab___boxed), 4, 0);
v___x_3733_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3729_, v___x_3730_, v___x_3731_, v___x_3732_);
return v___x_3733_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3734_;
v_res_3734_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
stack->m_obj
 = v_res_3734_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___boxed(lean_object* v_a_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
return v_res_3736_;
}
}
lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3(){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3763_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3764_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6));
v___x_3765_ = l_Lean_addBuiltinDeclarationRanges(v___x_3763_, v___x_3764_);
return v___x_3765_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3766_;
v_res_3766_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
stack->m_obj
 = v_res_3766_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___boxed(lean_object* v_a_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
return v_res_3768_;
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
