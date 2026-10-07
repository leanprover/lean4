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
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_box(0);
v___x_61_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg(){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0);
v___x_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___boxed(lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(lean_object* v_00_u03b1_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___boxed(lean_object* v_00_u03b1_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(v_00_u03b1_73_, v___y_74_, v___y_75_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0(lean_object* v_k_97_, lean_object* v_attrKind_98_, lean_object* v_attrs_x3f_99_, lean_object* v_kind_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
uint8_t v___x_104_; lean_object* v___x_105_; 
v___x_104_ = 0;
v___x_105_ = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(v_k_97_, v___x_104_, v___y_101_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_107_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_106_);
lean_dec_ref_known(v___x_105_, 1);
v___x_107_ = l_Lean_Elab_Command_getRef___redArg(v___y_101_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_144_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_144_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_144_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_144_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_133_; 
v___x_112_ = l_Lean_SourceInfo_fromRef(v_a_108_, v___x_104_);
lean_dec(v_a_108_);
v___x_133_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_101_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_quotContext_x3f_134_; 
lean_dec_ref_known(v___x_133_, 1);
v_quotContext_x3f_134_ = lean_ctor_get(v___y_101_, 5);
if (lean_obj_tag(v_quotContext_x3f_134_) == 0)
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_102_);
lean_dec_ref(v___x_135_);
goto v___jp_113_;
}
else
{
goto v___jp_113_;
}
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
lean_dec(v___x_112_);
lean_del_object(v___x_110_);
lean_dec(v_a_106_);
lean_dec(v_kind_100_);
lean_dec(v_attrKind_98_);
v_a_136_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_133_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_133_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
v___jp_113_:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_114_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4));
v___x_115_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7));
v___x_116_ = l_Lean_mkIdent(v_kind_100_);
v___x_117_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
lean_inc_n(v___x_112_, 2);
v___x_118_ = l_Lean_Syntax_node1(v___x_112_, v___x_117_, v_a_106_);
v___x_119_ = l_Lean_Syntax_node2(v___x_112_, v___x_115_, v___x_116_, v___x_118_);
v___x_120_ = l_Lean_Syntax_node2(v___x_112_, v___x_114_, v_attrKind_98_, v___x_119_);
if (lean_obj_tag(v_attrs_x3f_99_) == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = lean_mk_empty_array_with_capacity(v___x_121_);
v___x_123_ = lean_array_push(v___x_122_, v___x_120_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_123_);
v___x_125_ = v___x_110_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
else
{
lean_object* v_val_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v_val_127_ = lean_ctor_get(v_attrs_x3f_99_, 0);
v___x_128_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_127_);
v___x_129_ = lean_array_push(v___x_128_, v___x_120_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_129_);
v___x_131_ = v___x_110_;
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
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
lean_dec(v_a_106_);
lean_dec(v_kind_100_);
lean_dec(v_attrKind_98_);
v_a_145_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_107_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_107_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
else
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
lean_dec(v_kind_100_);
lean_dec(v_attrKind_98_);
v_a_153_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_160_ == 0)
{
v___x_155_ = v___x_105_;
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_105_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_153_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___boxed(lean_object* v_k_161_, lean_object* v_attrKind_162_, lean_object* v_attrs_x3f_163_, lean_object* v_kind_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_161_, v_attrKind_162_, v_attrs_x3f_163_, v_kind_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v_attrs_x3f_163_);
return v_res_168_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(lean_object* v_opts_169_, lean_object* v_opt_170_){
_start:
{
lean_object* v_name_171_; lean_object* v_defValue_172_; lean_object* v_map_173_; lean_object* v___x_174_; 
v_name_171_ = lean_ctor_get(v_opt_170_, 0);
v_defValue_172_ = lean_ctor_get(v_opt_170_, 1);
v_map_173_ = lean_ctor_get(v_opts_169_, 0);
v___x_174_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_173_, v_name_171_);
if (lean_obj_tag(v___x_174_) == 0)
{
uint8_t v___x_175_; 
v___x_175_ = lean_unbox(v_defValue_172_);
return v___x_175_;
}
else
{
lean_object* v_val_176_; 
v_val_176_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_val_176_);
lean_dec_ref_known(v___x_174_, 1);
if (lean_obj_tag(v_val_176_) == 1)
{
uint8_t v_v_177_; 
v_v_177_ = lean_ctor_get_uint8(v_val_176_, 0);
lean_dec_ref_known(v_val_176_, 0);
return v_v_177_;
}
else
{
uint8_t v___x_178_; 
lean_dec(v_val_176_);
v___x_178_ = lean_unbox(v_defValue_172_);
return v___x_178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8___boxed(lean_object* v_opts_179_, lean_object* v_opt_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(v_opts_179_, v_opt_180_);
lean_dec_ref(v_opt_180_);
lean_dec_ref(v_opts_179_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_box(1);
v___x_184_ = l_Lean_MessageData_ofFormat(v___x_183_);
return v___x_184_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2));
v___x_189_ = l_Lean_MessageData_ofFormat(v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
if (lean_obj_tag(v_x_191_) == 0)
{
return v_x_190_;
}
else
{
lean_object* v_head_192_; lean_object* v_tail_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_215_; 
v_head_192_ = lean_ctor_get(v_x_191_, 0);
v_tail_193_ = lean_ctor_get(v_x_191_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_x_191_);
if (v_isSharedCheck_215_ == 0)
{
v___x_195_ = v_x_191_;
v_isShared_196_ = v_isSharedCheck_215_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_tail_193_);
lean_inc(v_head_192_);
lean_dec(v_x_191_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_215_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v_before_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_213_; 
v_before_197_ = lean_ctor_get(v_head_192_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v_head_192_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; 
v_unused_214_ = lean_ctor_get(v_head_192_, 1);
lean_dec(v_unused_214_);
v___x_199_ = v_head_192_;
v_isShared_200_ = v_isSharedCheck_213_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_before_197_);
lean_dec(v_head_192_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_213_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_201_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_200_ == 0)
{
lean_ctor_set_tag(v___x_199_, 7);
lean_ctor_set(v___x_199_, 1, v___x_201_);
lean_ctor_set(v___x_199_, 0, v_x_190_);
v___x_203_ = v___x_199_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_x_190_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_201_);
v___x_203_ = v_reuseFailAlloc_212_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_204_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3);
if (v_isShared_196_ == 0)
{
lean_ctor_set_tag(v___x_195_, 7);
lean_ctor_set(v___x_195_, 1, v___x_204_);
lean_ctor_set(v___x_195_, 0, v___x_203_);
v___x_206_ = v___x_195_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v___x_204_);
v___x_206_ = v_reuseFailAlloc_211_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = l_Lean_MessageData_ofSyntax(v_before_197_);
v___x_208_ = l_Lean_indentD(v___x_207_);
v___x_209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_206_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v_x_190_ = v___x_209_;
v_x_191_ = v_tail_193_;
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
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1));
v___x_220_ = l_Lean_MessageData_ofFormat(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(lean_object* v_msgData_221_, lean_object* v_macroStack_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v_scopes_227_; lean_object* v___x_228_; lean_object* v_opts_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_225_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_226_ = lean_st_ref_get(v___y_223_);
v_scopes_227_ = lean_ctor_get(v___x_226_, 2);
lean_inc(v_scopes_227_);
lean_dec(v___x_226_);
v___x_228_ = l_List_head_x21___redArg(v___x_225_, v_scopes_227_);
lean_dec(v_scopes_227_);
v_opts_229_ = lean_ctor_get(v___x_228_, 1);
lean_inc_ref(v_opts_229_);
lean_dec(v___x_228_);
v___x_230_ = l_Lean_Elab_pp_macroStack;
v___x_231_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(v_opts_229_, v___x_230_);
lean_dec_ref(v_opts_229_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; 
lean_dec(v_macroStack_222_);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v_msgData_221_);
return v___x_232_;
}
else
{
if (lean_obj_tag(v_macroStack_222_) == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v_msgData_221_);
return v___x_233_;
}
else
{
lean_object* v_head_234_; lean_object* v_after_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_250_; 
v_head_234_ = lean_ctor_get(v_macroStack_222_, 0);
lean_inc(v_head_234_);
v_after_235_ = lean_ctor_get(v_head_234_, 1);
v_isSharedCheck_250_ = !lean_is_exclusive(v_head_234_);
if (v_isSharedCheck_250_ == 0)
{
lean_object* v_unused_251_; 
v_unused_251_ = lean_ctor_get(v_head_234_, 0);
lean_dec(v_unused_251_);
v___x_237_ = v_head_234_;
v_isShared_238_ = v_isSharedCheck_250_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_after_235_);
lean_dec(v_head_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_250_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_238_ == 0)
{
lean_ctor_set_tag(v___x_237_, 7);
lean_ctor_set(v___x_237_, 1, v___x_239_);
lean_ctor_set(v___x_237_, 0, v_msgData_221_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_msgData_221_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_239_);
v___x_241_ = v_reuseFailAlloc_249_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_msgData_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_242_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2);
v___x_243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = l_Lean_MessageData_ofSyntax(v_after_235_);
v___x_245_ = l_Lean_indentD(v___x_244_);
v_msgData_246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_246_, 0, v___x_243_);
lean_ctor_set(v_msgData_246_, 1, v___x_245_);
v___x_247_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(v_msgData_246_, v_macroStack_222_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___boxed(lean_object* v_msgData_252_, lean_object* v_macroStack_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_msgData_252_, v_macroStack_253_, v___y_254_);
lean_dec(v___y_254_);
return v_res_256_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_257_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_260_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_261_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
lean_ctor_set(v___x_263_, 2, v___x_262_);
lean_ctor_set(v___x_263_, 3, v___x_262_);
lean_ctor_set(v___x_263_, 4, v___x_261_);
lean_ctor_set(v___x_263_, 5, v___x_261_);
lean_ctor_set(v___x_263_, 6, v___x_261_);
lean_ctor_set(v___x_263_, 7, v___x_261_);
lean_ctor_set(v___x_263_, 8, v___x_261_);
lean_ctor_set(v___x_263_, 9, v___x_261_);
lean_ctor_set(v___x_263_, 10, v___x_261_);
lean_ctor_set(v___x_263_, 11, v___x_260_);
return v___x_263_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_unsigned_to_nat(32u);
v___x_265_ = lean_mk_empty_array_with_capacity(v___x_264_);
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_267_ = ((size_t)5ULL);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_unsigned_to_nat(32u);
v___x_270_ = lean_mk_empty_array_with_capacity(v___x_269_);
v___x_271_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3);
v___x_272_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_270_);
lean_ctor_set(v___x_272_, 2, v___x_268_);
lean_ctor_set(v___x_272_, 3, v___x_268_);
lean_ctor_set_usize(v___x_272_, 4, v___x_267_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_273_ = lean_box(1);
v___x_274_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4);
v___x_275_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1);
v___x_276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v___x_274_);
lean_ctor_set(v___x_276_, 2, v___x_273_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(lean_object* v_msgData_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_280_; lean_object* v_env_281_; uint8_t v___x_282_; lean_object* v_env_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_scopes_286_; lean_object* v___x_287_; lean_object* v_opts_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_280_ = lean_st_ref_get(v___y_278_);
v_env_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc_ref(v_env_281_);
lean_dec(v___x_280_);
v___x_282_ = 0;
v_env_283_ = l_Lean_Environment_setRecordingDeps(v_env_281_, v___x_282_);
v___x_284_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_285_ = lean_st_ref_get(v___y_278_);
v_scopes_286_ = lean_ctor_get(v___x_285_, 2);
lean_inc(v_scopes_286_);
lean_dec(v___x_285_);
v___x_287_ = l_List_head_x21___redArg(v___x_284_, v_scopes_286_);
lean_dec(v_scopes_286_);
v_opts_288_ = lean_ctor_get(v___x_287_, 1);
lean_inc_ref(v_opts_288_);
lean_dec(v___x_287_);
v___x_289_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2);
v___x_290_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5);
v___x_291_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_291_, 0, v_env_283_);
lean_ctor_set(v___x_291_, 1, v___x_289_);
lean_ctor_set(v___x_291_, 2, v___x_290_);
lean_ctor_set(v___x_291_, 3, v_opts_288_);
v___x_292_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v_msgData_277_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___boxed(lean_object* v_msgData_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msgData_294_, v___y_295_);
lean_dec(v___y_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(lean_object* v_msg_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Elab_Command_getRef___redArg(v___y_299_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v_macroStack_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v_a_307_; lean_object* v___x_308_; lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_317_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_303_);
lean_dec_ref_known(v___x_302_, 1);
v_macroStack_304_ = lean_ctor_get(v___y_299_, 4);
v___x_305_ = l_Lean_Elab_getBetterRef(v_a_303_, v_macroStack_304_);
lean_dec(v_a_303_);
v___x_306_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msg_298_, v___y_300_);
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_307_);
lean_dec_ref(v___x_306_);
lean_inc(v_macroStack_304_);
v___x_308_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_a_307_, v_macroStack_304_, v___y_300_);
v_a_309_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_317_ == 0)
{
v___x_311_ = v___x_308_;
v_isShared_312_ = v_isSharedCheck_317_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_317_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_305_);
lean_ctor_set(v___x_313_, 1, v_a_309_);
if (v_isShared_312_ == 0)
{
lean_ctor_set_tag(v___x_311_, 1);
lean_ctor_set(v___x_311_, 0, v___x_313_);
v___x_315_ = v___x_311_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec_ref(v_msg_298_);
v_a_318_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_302_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_302_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg___boxed(lean_object* v_msg_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(lean_object* v_ref_331_, lean_object* v_msg_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Elab_Command_getRef___redArg(v___y_333_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v_fileName_338_; lean_object* v_fileMap_339_; lean_object* v_currRecDepth_340_; lean_object* v_cmdPos_341_; lean_object* v_macroStack_342_; lean_object* v_quotContext_x3f_343_; lean_object* v_currMacroScope_344_; lean_object* v_snap_x3f_345_; lean_object* v_cancelTk_x3f_346_; uint8_t v_suppressElabErrors_347_; lean_object* v_ref_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
lean_dec_ref_known(v___x_336_, 1);
v_fileName_338_ = lean_ctor_get(v___y_333_, 0);
v_fileMap_339_ = lean_ctor_get(v___y_333_, 1);
v_currRecDepth_340_ = lean_ctor_get(v___y_333_, 2);
v_cmdPos_341_ = lean_ctor_get(v___y_333_, 3);
v_macroStack_342_ = lean_ctor_get(v___y_333_, 4);
v_quotContext_x3f_343_ = lean_ctor_get(v___y_333_, 5);
v_currMacroScope_344_ = lean_ctor_get(v___y_333_, 6);
v_snap_x3f_345_ = lean_ctor_get(v___y_333_, 8);
v_cancelTk_x3f_346_ = lean_ctor_get(v___y_333_, 9);
v_suppressElabErrors_347_ = lean_ctor_get_uint8(v___y_333_, sizeof(void*)*10);
v_ref_348_ = l_Lean_replaceRef(v_ref_331_, v_a_337_);
lean_dec(v_a_337_);
lean_inc(v_cancelTk_x3f_346_);
lean_inc(v_snap_x3f_345_);
lean_inc(v_currMacroScope_344_);
lean_inc(v_quotContext_x3f_343_);
lean_inc(v_macroStack_342_);
lean_inc(v_cmdPos_341_);
lean_inc(v_currRecDepth_340_);
lean_inc_ref(v_fileMap_339_);
lean_inc_ref(v_fileName_338_);
v___x_349_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_349_, 0, v_fileName_338_);
lean_ctor_set(v___x_349_, 1, v_fileMap_339_);
lean_ctor_set(v___x_349_, 2, v_currRecDepth_340_);
lean_ctor_set(v___x_349_, 3, v_cmdPos_341_);
lean_ctor_set(v___x_349_, 4, v_macroStack_342_);
lean_ctor_set(v___x_349_, 5, v_quotContext_x3f_343_);
lean_ctor_set(v___x_349_, 6, v_currMacroScope_344_);
lean_ctor_set(v___x_349_, 7, v_ref_348_);
lean_ctor_set(v___x_349_, 8, v_snap_x3f_345_);
lean_ctor_set(v___x_349_, 9, v_cancelTk_x3f_346_);
lean_ctor_set_uint8(v___x_349_, sizeof(void*)*10, v_suppressElabErrors_347_);
v___x_350_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_332_, v___x_349_, v___y_334_);
lean_dec_ref_known(v___x_349_, 10);
return v___x_350_;
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec_ref(v_msg_332_);
v_a_351_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_336_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_336_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(lean_object* v_ref_359_, lean_object* v_msg_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_359_, v_msg_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v_ref_359_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(lean_object* v_k_368_, lean_object* v_as_369_, size_t v_sz_370_, size_t v_i_371_, lean_object* v_b_372_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = lean_usize_dec_lt(v_i_371_, v_sz_370_);
if (v___x_373_ == 0)
{
lean_dec(v_k_368_);
lean_inc_ref(v_b_372_);
return v_b_372_;
}
else
{
lean_object* v___x_374_; lean_object* v_a_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_374_ = lean_box(0);
v_a_375_ = lean_array_uget_borrowed(v_as_369_, v_i_371_);
lean_inc(v_a_375_);
v___x_376_ = l_Lean_Syntax_getKind(v_a_375_);
lean_inc(v_k_368_);
v___x_377_ = l_Lean_Elab_Command_checkRuleKind(v___x_376_, v_k_368_);
lean_dec(v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; size_t v___x_379_; size_t v___x_380_; 
v___x_378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0));
v___x_379_ = ((size_t)1ULL);
v___x_380_ = lean_usize_add(v_i_371_, v___x_379_);
v_i_371_ = v___x_380_;
v_b_372_ = v___x_378_;
goto _start;
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec(v_k_368_);
lean_inc(v_a_375_);
v___x_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_382_, 0, v_a_375_);
v___x_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v___x_374_);
return v___x_384_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(lean_object* v_k_385_, lean_object* v_as_386_, lean_object* v_sz_387_, lean_object* v_i_388_, lean_object* v_b_389_){
_start:
{
size_t v_sz_boxed_390_; size_t v_i_boxed_391_; lean_object* v_res_392_; 
v_sz_boxed_390_ = lean_unbox_usize(v_sz_387_);
lean_dec(v_sz_387_);
v_i_boxed_391_ = lean_unbox_usize(v_i_388_);
lean_dec(v_i_388_);
v_res_392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_k_385_, v_as_386_, v_sz_boxed_390_, v_i_boxed_391_, v_b_389_);
lean_dec_ref(v_b_389_);
lean_dec_ref(v_as_386_);
return v_res_392_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0));
v___x_395_ = l_Lean_stringToMessageData(v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2));
v___x_398_ = l_Lean_stringToMessageData(v___x_397_);
return v___x_398_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7(void){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Array_mkArray0___redArg();
return v___x_406_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11));
v___x_413_ = l_Lean_stringToMessageData(v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(lean_object* v_k_414_, size_t v_sz_415_, size_t v_i_416_, lean_object* v_bs_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
uint8_t v___x_421_; 
v___x_421_ = lean_usize_dec_lt(v_i_416_, v_sz_415_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
lean_dec(v_k_414_);
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v_bs_417_);
return v___x_422_;
}
else
{
lean_object* v_v_423_; lean_object* v___x_424_; lean_object* v_bs_x27_425_; lean_object* v_a_427_; lean_object* v___y_433_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___x_452_; uint8_t v___x_453_; 
v_v_423_ = lean_array_uget(v_bs_417_, v_i_416_);
v___x_424_ = lean_unsigned_to_nat(0u);
v_bs_x27_425_ = lean_array_uset(v_bs_417_, v_i_416_, v___x_424_);
v___x_452_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5));
lean_inc(v_v_423_);
v___x_453_ = l_Lean_Syntax_isOfKind(v_v_423_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
lean_dec(v_v_423_);
v___x_454_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
v___y_433_ = v___x_454_;
goto v___jp_432_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_456_ = l_Lean_Syntax_getArg(v_v_423_, v___x_455_);
lean_inc(v___x_456_);
v___x_457_ = l_Lean_Syntax_matchesNull(v___x_456_, v___x_455_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; 
lean_dec(v___x_456_);
lean_dec(v_v_423_);
v___x_458_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
v___y_433_ = v___x_458_;
goto v___jp_432_;
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___x_476_; lean_object* v_pat_477_; lean_object* v___y_479_; lean_object* v___y_480_; uint8_t v___x_532_; 
v___x_459_ = lean_box(0);
v___x_460_ = l_Lean_Syntax_getArg(v___x_456_, v___x_424_);
lean_dec(v___x_456_);
v___x_461_ = lean_unsigned_to_nat(3u);
v___x_462_ = l_Lean_Syntax_getArg(v_v_423_, v___x_461_);
v___x_476_ = l_Lean_Syntax_getArgs(v___x_460_);
lean_dec(v___x_460_);
v_pat_477_ = lean_array_get_borrowed(v___x_459_, v___x_476_, v___x_424_);
v___x_532_ = l_Lean_Syntax_isQuot(v_pat_477_);
if (v___x_532_ == 0)
{
if (v___x_457_ == 0)
{
v___y_479_ = v___y_418_;
v___y_480_ = v___y_419_;
goto v___jp_478_;
}
else
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
if (lean_obj_tag(v___x_533_) == 0)
{
lean_dec_ref_known(v___x_533_, 1);
v___y_479_ = v___y_418_;
v___y_480_ = v___y_419_;
goto v___jp_478_;
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec_ref(v___x_476_);
lean_dec(v___x_462_);
lean_dec_ref(v_bs_x27_425_);
lean_dec(v_v_423_);
lean_dec(v_k_414_);
v_a_534_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
else
{
v___y_479_ = v___y_418_;
v___y_480_ = v___y_419_;
goto v___jp_478_;
}
v___jp_463_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc_n(v___y_465_, 4);
v___x_467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_467_, 0, v___y_465_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_469_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
v___x_470_ = l_Array_append___redArg(v___x_469_, v___y_464_);
lean_dec_ref(v___y_464_);
v___x_471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_471_, 0, v___y_465_);
lean_ctor_set(v___x_471_, 1, v___x_468_);
lean_ctor_set(v___x_471_, 2, v___x_470_);
v___x_472_ = l_Lean_Syntax_node1(v___y_465_, v___x_468_, v___x_471_);
v___x_473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_474_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_474_, 0, v___y_465_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = l_Lean_Syntax_node4(v___y_465_, v___x_452_, v___x_467_, v___x_472_, v___x_474_, v___x_462_);
v_a_427_ = v___x_475_;
goto v___jp_426_;
}
v___jp_478_:
{
lean_object* v_quoted_481_; lean_object* v_k_x27_482_; uint8_t v___x_483_; 
lean_inc(v_pat_477_);
v_quoted_481_ = l_Lean_Syntax_getQuotContent(v_pat_477_);
lean_inc(v_quoted_481_);
v_k_x27_482_ = l_Lean_Syntax_getKind(v_quoted_481_);
lean_inc(v_k_414_);
v___x_483_ = l_Lean_Elab_Command_checkRuleKind(v_k_x27_482_, v_k_414_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10));
v___x_485_ = lean_name_eq(v_k_x27_482_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec(v_quoted_481_);
lean_dec_ref(v___x_476_);
lean_dec(v___x_462_);
v___x_486_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12);
v___x_487_ = l_Lean_MessageData_ofName(v_k_x27_482_);
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_v_423_, v___x_490_, v___y_479_, v___y_480_);
lean_dec(v_v_423_);
v___y_433_ = v___x_491_;
goto v___jp_432_;
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; size_t v_sz_494_; size_t v___x_495_; lean_object* v___x_496_; lean_object* v_fst_497_; 
lean_dec(v_k_x27_482_);
v___x_492_ = l_Lean_Syntax_getArgs(v_quoted_481_);
lean_dec(v_quoted_481_);
v___x_493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0));
v_sz_494_ = lean_array_size(v___x_492_);
v___x_495_ = ((size_t)0ULL);
lean_inc(v_k_414_);
v___x_496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_k_414_, v___x_492_, v_sz_494_, v___x_495_, v___x_493_);
lean_dec_ref(v___x_492_);
v_fst_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_fst_497_);
lean_dec_ref(v___x_496_);
if (lean_obj_tag(v_fst_497_) == 0)
{
lean_dec_ref(v___x_476_);
lean_dec(v___x_462_);
v___y_444_ = v___y_479_;
v___y_445_ = v___y_480_;
goto v___jp_443_;
}
else
{
lean_object* v_val_498_; 
v_val_498_ = lean_ctor_get(v_fst_497_, 0);
lean_inc(v_val_498_);
lean_dec_ref_known(v_fst_497_, 1);
if (lean_obj_tag(v_val_498_) == 0)
{
lean_dec_ref(v___x_476_);
lean_dec(v___x_462_);
v___y_444_ = v___y_479_;
v___y_445_ = v___y_480_;
goto v___jp_443_;
}
else
{
lean_object* v_val_499_; lean_object* v_pat_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
lean_dec(v_v_423_);
v_val_499_ = lean_ctor_get(v_val_498_, 0);
lean_inc(v_val_499_);
lean_dec_ref_known(v_val_498_, 1);
lean_inc(v_pat_477_);
v_pat_500_ = l_Lean_Syntax_setArg(v_pat_477_, v___x_455_, v_val_499_);
v___x_501_ = lean_array_set(v___x_476_, v___x_424_, v_pat_500_);
v___x_502_ = l_Lean_Elab_Command_getRef___redArg(v___y_479_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v___x_502_, 1);
v___x_504_ = l_Lean_SourceInfo_fromRef(v_a_503_, v___x_483_);
lean_dec(v_a_503_);
v___x_505_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_479_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_quotContext_x3f_506_; 
lean_dec_ref_known(v___x_505_, 1);
v_quotContext_x3f_506_ = lean_ctor_get(v___y_479_, 5);
if (lean_obj_tag(v_quotContext_x3f_506_) == 0)
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_480_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_dec_ref_known(v___x_507_, 1);
v___y_464_ = v___x_501_;
v___y_465_ = v___x_504_;
goto v___jp_463_;
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec(v___x_504_);
lean_dec_ref(v___x_501_);
lean_dec(v___x_462_);
lean_dec_ref(v_bs_x27_425_);
lean_dec(v_k_414_);
v_a_508_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_507_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
else
{
v___y_464_ = v___x_501_;
v___y_465_ = v___x_504_;
goto v___jp_463_;
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec(v___x_504_);
lean_dec_ref(v___x_501_);
lean_dec(v___x_462_);
lean_dec_ref(v_bs_x27_425_);
lean_dec(v_k_414_);
v_a_516_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_505_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_505_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec_ref(v___x_501_);
lean_dec(v___x_462_);
lean_dec_ref(v_bs_x27_425_);
lean_dec(v_k_414_);
v_a_524_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_502_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_502_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_x27_482_);
lean_dec(v_quoted_481_);
lean_dec_ref(v___x_476_);
lean_dec(v___x_462_);
v_a_427_ = v_v_423_;
goto v___jp_426_;
}
}
}
}
v___jp_426_:
{
size_t v___x_428_; size_t v___x_429_; lean_object* v___x_430_; 
v___x_428_ = ((size_t)1ULL);
v___x_429_ = lean_usize_add(v_i_416_, v___x_428_);
v___x_430_ = lean_array_uset(v_bs_x27_425_, v_i_416_, v_a_427_);
v_i_416_ = v___x_429_;
v_bs_417_ = v___x_430_;
goto _start;
}
v___jp_432_:
{
if (lean_obj_tag(v___y_433_) == 0)
{
lean_object* v_a_434_; 
v_a_434_ = lean_ctor_get(v___y_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___y_433_, 1);
v_a_427_ = v_a_434_;
goto v___jp_426_;
}
else
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
lean_dec_ref(v_bs_x27_425_);
lean_dec(v_k_414_);
v_a_435_ = lean_ctor_get(v___y_433_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___y_433_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___y_433_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___y_433_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
v___jp_443_:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_446_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1);
lean_inc(v_k_414_);
v___x_447_ = l_Lean_MessageData_ofName(v_k_414_);
v___x_448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_v_423_, v___x_450_, v___y_444_, v___y_445_);
lean_dec(v_v_423_);
v___y_433_ = v___x_451_;
goto v___jp_432_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___boxed(lean_object* v_k_542_, lean_object* v_sz_543_, lean_object* v_i_544_, lean_object* v_bs_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
size_t v_sz_boxed_549_; size_t v_i_boxed_550_; lean_object* v_res_551_; 
v_sz_boxed_549_ = lean_unbox_usize(v_sz_543_);
lean_dec(v_sz_543_);
v_i_boxed_550_ = lean_unbox_usize(v_i_544_);
lean_dec(v_i_544_);
v_res_551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(v_k_542_, v_sz_boxed_549_, v_i_boxed_550_, v_bs_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
return v_res_551_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__4));
v___x_558_ = l_String_toRawSubstring_x27(v___x_557_);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__8));
v___x_564_ = l_String_toRawSubstring_x27(v___x_563_);
return v___x_564_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__15));
v___x_572_ = l_String_toRawSubstring_x27(v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_585_ = l_String_toRawSubstring_x27(v___x_584_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__35(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__34));
v___x_600_ = l_String_toRawSubstring_x27(v___x_599_);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__38(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__37));
v___x_604_ = l_String_toRawSubstring_x27(v___x_603_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__42(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__41));
v___x_610_ = l_String_toRawSubstring_x27(v___x_609_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__45(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__44));
v___x_614_ = l_String_toRawSubstring_x27(v___x_613_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__48(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__47));
v___x_618_ = l_String_toRawSubstring_x27(v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__51(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__50));
v___x_623_ = l_String_toRawSubstring_x27(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__58(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__57));
v___x_633_ = l_Lean_stringToMessageData(v___x_632_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__60(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__59));
v___x_636_ = l_Lean_stringToMessageData(v___x_635_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__72(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__71));
v___x_654_ = l_Lean_stringToMessageData(v___x_653_);
return v___x_654_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__75));
v___x_660_ = l_Lean_stringToMessageData(v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object* v_doc_x3f_661_, lean_object* v_attrs_x3f_662_, lean_object* v_attrKind_663_, lean_object* v_k_664_, lean_object* v_cat_x3f_665_, lean_object* v_expty_x3f_666_, lean_object* v_alts_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
size_t v_sz_671_; size_t v___x_672_; lean_object* v___x_673_; 
v_sz_671_ = lean_array_size(v_alts_667_);
v___x_672_ = ((size_t)0ULL);
lean_inc(v_k_664_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(v_k_664_, v_sz_671_, v___x_672_, v_alts_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_1690_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_1690_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_1690_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v_a_805_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v_a_957_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v_a_1070_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; uint8_t v___y_1085_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v_a_1241_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v_a_1355_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v_a_1488_; lean_object* v_catName_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; 
if (lean_obj_tag(v_cat_x3f_665_) == 1)
{
lean_object* v_val_1677_; lean_object* v___x_1678_; 
v_val_1677_ = lean_ctor_get(v_cat_x3f_665_, 0);
v___x_1678_ = l_Lean_TSyntax_getId(v_val_1677_);
v_catName_1499_ = v___x_1678_;
v___y_1500_ = v_a_668_;
v___y_1501_ = v_a_669_;
goto v___jp_1498_;
}
else
{
if (lean_obj_tag(v_expty_x3f_666_) == 1)
{
lean_object* v___x_1679_; 
v___x_1679_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v_catName_1499_ = v___x_1679_;
v___y_1500_ = v_a_668_;
v___y_1501_ = v_a_669_;
goto v___jp_1498_;
}
else
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_del_object(v___x_676_);
lean_dec(v_a_674_);
lean_dec(v_expty_x3f_666_);
lean_dec(v_k_664_);
lean_dec(v_attrKind_663_);
lean_dec(v_doc_x3f_661_);
v___x_1680_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__76, &l_Lean_Elab_Command_elabElabRulesAux___closed__76_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76);
v___x_1681_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v___x_1680_, v_a_668_, v_a_669_);
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1681_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1681_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
v___jp_678_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_797_; 
lean_inc_ref_n(v___y_679_, 4);
v___x_692_ = l_Array_append___redArg(v___y_679_, v___y_691_);
lean_dec_ref(v___y_691_);
lean_inc_n(v___y_687_, 10);
lean_inc_n(v___y_683_, 35);
v___x_693_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_693_, 0, v___y_683_);
lean_ctor_set(v___x_693_, 1, v___y_687_);
lean_ctor_set(v___x_693_, 2, v___x_692_);
v___x_694_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_695_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_696_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_686_, 11);
v___x_697_ = l_Lean_Name_mkStr4(v___y_686_, v___x_694_, v___x_695_, v___x_696_);
v___x_698_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_699_, 0, v___y_683_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_701_ = l_Lean_Syntax_SepArray_ofElems(v___x_700_, v___y_680_);
lean_dec_ref(v___y_680_);
v___x_702_ = l_Array_append___redArg(v___y_679_, v___x_701_);
lean_dec_ref(v___x_701_);
v___x_703_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_703_, 0, v___y_683_);
lean_ctor_set(v___x_703_, 1, v___y_687_);
lean_ctor_set(v___x_703_, 2, v___x_702_);
v___x_704_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_705_, 0, v___y_683_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = l_Lean_Syntax_node3(v___y_683_, v___x_697_, v___x_699_, v___x_703_, v___x_705_);
v___x_707_ = l_Lean_Syntax_node1(v___y_683_, v___y_687_, v___x_706_);
lean_inc_ref(v___y_688_);
v___x_708_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_708_, 0, v___y_683_);
lean_ctor_set(v___x_708_, 1, v___y_688_);
v___x_709_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_710_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_689_, 3);
lean_inc_n(v___y_684_, 3);
v___x_711_ = l_Lean_addMacroScope(v___y_684_, v___x_710_, v___y_689_);
v___x_712_ = lean_box(0);
v___x_713_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_713_, 0, v___y_683_);
lean_ctor_set(v___x_713_, 1, v___x_709_);
lean_ctor_set(v___x_713_, 2, v___x_711_);
lean_ctor_set(v___x_713_, 3, v___x_712_);
v___x_714_ = l_Lean_mkIdent(v_k_664_);
v___x_715_ = l_Lean_Syntax_node2(v___y_683_, v___y_687_, v___x_713_, v___x_714_);
v___x_716_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_717_, 0, v___y_683_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_719_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
v___x_720_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc_ref_n(v___y_690_, 2);
v___x_721_ = l_Lean_Name_mkStr4(v___y_686_, v___y_690_, v___x_719_, v___x_720_);
lean_inc(v___x_721_);
v___x_722_ = l_Lean_addMacroScope(v___y_684_, v___x_721_, v___y_689_);
v___x_723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_712_);
v___x_724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v___x_712_);
v___x_725_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_725_, 0, v___y_683_);
lean_ctor_set(v___x_725_, 1, v___x_718_);
lean_ctor_set(v___x_725_, 2, v___x_722_);
lean_ctor_set(v___x_725_, 3, v___x_724_);
v___x_726_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_727_, 0, v___y_683_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_729_ = l_Lean_Name_mkStr4(v___y_686_, v___x_694_, v___x_695_, v___x_728_);
v___x_730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_730_, 0, v___y_683_);
lean_ctor_set(v___x_730_, 1, v___x_728_);
v___x_731_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_732_ = l_Lean_Name_mkStr4(v___y_686_, v___x_694_, v___x_695_, v___x_731_);
v___x_733_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_734_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_735_ = l_Lean_addMacroScope(v___y_684_, v___x_734_, v___y_689_);
v___x_736_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_736_, 0, v___y_683_);
lean_ctor_set(v___x_736_, 1, v___x_733_);
lean_ctor_set(v___x_736_, 2, v___x_735_);
lean_ctor_set(v___x_736_, 3, v___x_712_);
lean_inc_ref(v___x_736_);
v___x_737_ = l_Lean_Syntax_node2(v___y_683_, v___y_687_, v___x_736_, v___y_685_);
v___x_738_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_738_, 0, v___y_683_);
lean_ctor_set(v___x_738_, 1, v___y_687_);
lean_ctor_set(v___x_738_, 2, v___y_679_);
v___x_739_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_740_, 0, v___y_683_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_742_ = l_Lean_Name_mkStr4(v___y_686_, v___x_694_, v___x_695_, v___x_741_);
v___x_743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_743_, 0, v___y_683_);
lean_ctor_set(v___x_743_, 1, v___x_741_);
v___x_744_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_745_ = l_Lean_Name_mkStr4(v___y_686_, v___x_694_, v___x_695_, v___x_744_);
lean_inc_ref_n(v___x_738_, 3);
v___x_746_ = l_Lean_Syntax_node2(v___y_683_, v___x_745_, v___x_738_, v___x_736_);
v___x_747_ = l_Lean_Syntax_node1(v___y_683_, v___y_687_, v___x_746_);
v___x_748_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_749_, 0, v___y_683_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_751_ = l_Lean_Name_mkStr4(v___y_686_, v___x_694_, v___x_695_, v___x_750_);
v___x_752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_753_ = l_Lean_Name_mkStr4(v___y_686_, v___x_694_, v___x_695_, v___x_752_);
v___x_754_ = l_Array_append___redArg(v___y_679_, v_a_674_);
lean_dec(v_a_674_);
v___x_755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_756_, 0, v___y_683_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_758_ = l_Lean_Name_mkStr4(v___y_686_, v___x_694_, v___x_695_, v___x_757_);
v___x_759_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_760_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_760_, 0, v___y_683_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l_Lean_Syntax_node1(v___y_683_, v___x_758_, v___x_760_);
v___x_762_ = l_Lean_Syntax_node1(v___y_683_, v___y_687_, v___x_761_);
v___x_763_ = l_Lean_Syntax_node1(v___y_683_, v___y_687_, v___x_762_);
v___x_764_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_765_ = l_Lean_Name_mkStr4(v___y_686_, v___x_694_, v___x_695_, v___x_764_);
v___x_766_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_767_, 0, v___y_683_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_769_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_770_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_771_ = l_Lean_addMacroScope(v___y_684_, v___x_770_, v___y_689_);
v___x_772_ = l_Lean_Name_mkStr3(v___y_686_, v___y_690_, v___x_768_);
v___x_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v___x_712_);
v___x_774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v___x_712_);
v___x_775_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_775_, 0, v___y_683_);
lean_ctor_set(v___x_775_, 1, v___x_769_);
lean_ctor_set(v___x_775_, 2, v___x_771_);
lean_ctor_set(v___x_775_, 3, v___x_774_);
v___x_776_ = l_Lean_Syntax_node2(v___y_683_, v___x_765_, v___x_767_, v___x_775_);
lean_inc_ref(v___x_740_);
v___x_777_ = l_Lean_Syntax_node4(v___y_683_, v___x_753_, v___x_756_, v___x_763_, v___x_740_, v___x_776_);
v___x_778_ = lean_array_push(v___x_754_, v___x_777_);
v___x_779_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_779_, 0, v___y_683_);
lean_ctor_set(v___x_779_, 1, v___y_687_);
lean_ctor_set(v___x_779_, 2, v___x_778_);
v___x_780_ = l_Lean_Syntax_node1(v___y_683_, v___x_751_, v___x_779_);
v___x_781_ = l_Lean_Syntax_node6(v___y_683_, v___x_742_, v___x_743_, v___x_738_, v___x_738_, v___x_747_, v___x_749_, v___x_780_);
v___x_782_ = l_Lean_Syntax_node4(v___y_683_, v___x_732_, v___x_737_, v___x_738_, v___x_740_, v___x_781_);
v___x_783_ = l_Lean_Syntax_node2(v___y_683_, v___x_729_, v___x_730_, v___x_782_);
v___x_784_ = lean_unsigned_to_nat(9u);
v___x_785_ = lean_mk_empty_array_with_capacity(v___x_784_);
v___x_786_ = lean_array_push(v___x_785_, v___x_693_);
v___x_787_ = lean_array_push(v___x_786_, v___x_707_);
v___x_788_ = lean_array_push(v___x_787_, v___y_682_);
v___x_789_ = lean_array_push(v___x_788_, v___x_708_);
v___x_790_ = lean_array_push(v___x_789_, v___x_715_);
v___x_791_ = lean_array_push(v___x_790_, v___x_717_);
v___x_792_ = lean_array_push(v___x_791_, v___x_725_);
v___x_793_ = lean_array_push(v___x_792_, v___x_727_);
v___x_794_ = lean_array_push(v___x_793_, v___x_783_);
lean_inc(v___y_681_);
v___x_795_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_795_, 0, v___y_683_);
lean_ctor_set(v___x_795_, 1, v___y_681_);
lean_ctor_set(v___x_795_, 2, v___x_794_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_795_);
v___x_797_ = v___x_676_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
v___jp_799_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_806_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_807_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_808_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_809_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_810_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_811_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_661_) == 1)
{
lean_object* v_val_812_; lean_object* v___x_813_; 
v_val_812_ = lean_ctor_get(v_doc_x3f_661_, 0);
lean_inc(v_val_812_);
lean_dec_ref_known(v_doc_x3f_661_, 1);
v___x_813_ = l_Array_mkArray1___redArg(v_val_812_);
v___y_679_ = v___x_811_;
v___y_680_ = v___y_801_;
v___y_681_ = v___x_809_;
v___y_682_ = v___y_803_;
v___y_683_ = v___y_800_;
v___y_684_ = v_a_805_;
v___y_685_ = v___y_802_;
v___y_686_ = v___x_806_;
v___y_687_ = v___x_810_;
v___y_688_ = v___x_808_;
v___y_689_ = v___y_804_;
v___y_690_ = v___x_807_;
v___y_691_ = v___x_813_;
goto v___jp_678_;
}
else
{
lean_object* v___x_814_; 
lean_dec(v_doc_x3f_661_);
v___x_814_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_679_ = v___x_811_;
v___y_680_ = v___y_801_;
v___y_681_ = v___x_809_;
v___y_682_ = v___y_803_;
v___y_683_ = v___y_800_;
v___y_684_ = v_a_805_;
v___y_685_ = v___y_802_;
v___y_686_ = v___x_806_;
v___y_687_ = v___x_810_;
v___y_688_ = v___x_808_;
v___y_689_ = v___y_804_;
v___y_690_ = v___x_807_;
v___y_691_ = v___x_814_;
goto v___jp_678_;
}
}
v___jp_815_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
lean_inc_ref_n(v___y_825_, 4);
v___x_829_ = l_Array_append___redArg(v___y_825_, v___y_828_);
lean_dec_ref(v___y_828_);
lean_inc_n(v___y_826_, 12);
lean_inc_n(v___y_817_, 42);
v___x_830_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_830_, 0, v___y_817_);
lean_ctor_set(v___x_830_, 1, v___y_826_);
lean_ctor_set(v___x_830_, 2, v___x_829_);
v___x_831_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_832_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_833_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_822_, 13);
v___x_834_ = l_Lean_Name_mkStr4(v___y_822_, v___x_831_, v___x_832_, v___x_833_);
v___x_835_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_836_, 0, v___y_817_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_838_ = l_Lean_Syntax_SepArray_ofElems(v___x_837_, v___y_820_);
lean_dec_ref(v___y_820_);
v___x_839_ = l_Array_append___redArg(v___y_825_, v___x_838_);
lean_dec_ref(v___x_838_);
v___x_840_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_840_, 0, v___y_817_);
lean_ctor_set(v___x_840_, 1, v___y_826_);
lean_ctor_set(v___x_840_, 2, v___x_839_);
v___x_841_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_842_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_842_, 0, v___y_817_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = l_Lean_Syntax_node3(v___y_817_, v___x_834_, v___x_836_, v___x_840_, v___x_842_);
v___x_844_ = l_Lean_Syntax_node1(v___y_817_, v___y_826_, v___x_843_);
lean_inc_ref(v___y_821_);
v___x_845_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_845_, 0, v___y_817_);
lean_ctor_set(v___x_845_, 1, v___y_821_);
v___x_846_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_847_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_827_, 5);
lean_inc_n(v___y_816_, 5);
v___x_848_ = l_Lean_addMacroScope(v___y_816_, v___x_847_, v___y_827_);
v___x_849_ = lean_box(0);
v___x_850_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_850_, 0, v___y_817_);
lean_ctor_set(v___x_850_, 1, v___x_846_);
lean_ctor_set(v___x_850_, 2, v___x_848_);
lean_ctor_set(v___x_850_, 3, v___x_849_);
v___x_851_ = l_Lean_mkIdent(v_k_664_);
v___x_852_ = l_Lean_Syntax_node2(v___y_817_, v___y_826_, v___x_850_, v___x_851_);
v___x_853_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_854_, 0, v___y_817_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__35, &l_Lean_Elab_Command_elabElabRulesAux___closed__35_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__35);
v___x_856_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__36));
lean_inc_ref_n(v___y_819_, 3);
v___x_857_ = l_Lean_Name_mkStr4(v___y_822_, v___y_819_, v___x_832_, v___x_856_);
lean_inc(v___x_857_);
v___x_858_ = l_Lean_addMacroScope(v___y_816_, v___x_857_, v___y_827_);
v___x_859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_857_);
lean_ctor_set(v___x_859_, 1, v___x_849_);
v___x_860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v___x_849_);
v___x_861_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_861_, 0, v___y_817_);
lean_ctor_set(v___x_861_, 1, v___x_855_);
lean_ctor_set(v___x_861_, 2, v___x_858_);
lean_ctor_set(v___x_861_, 3, v___x_860_);
v___x_862_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_863_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_863_, 0, v___y_817_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_865_ = l_Lean_Name_mkStr4(v___y_822_, v___x_831_, v___x_832_, v___x_864_);
v___x_866_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_866_, 0, v___y_817_);
lean_ctor_set(v___x_866_, 1, v___x_864_);
v___x_867_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_868_ = l_Lean_Name_mkStr4(v___y_822_, v___x_831_, v___x_832_, v___x_867_);
v___x_869_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_870_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_871_ = l_Lean_addMacroScope(v___y_816_, v___x_870_, v___y_827_);
v___x_872_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_872_, 0, v___y_817_);
lean_ctor_set(v___x_872_, 1, v___x_869_);
lean_ctor_set(v___x_872_, 2, v___x_871_);
lean_ctor_set(v___x_872_, 3, v___x_849_);
v___x_873_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__38, &l_Lean_Elab_Command_elabElabRulesAux___closed__38_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__38);
v___x_874_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__39));
v___x_875_ = l_Lean_addMacroScope(v___y_816_, v___x_874_, v___y_827_);
v___x_876_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_876_, 0, v___y_817_);
lean_ctor_set(v___x_876_, 1, v___x_873_);
lean_ctor_set(v___x_876_, 2, v___x_875_);
lean_ctor_set(v___x_876_, 3, v___x_849_);
lean_inc_ref(v___x_876_);
lean_inc_ref(v___x_872_);
v___x_877_ = l_Lean_Syntax_node2(v___y_817_, v___y_826_, v___x_872_, v___x_876_);
v___x_878_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_878_, 0, v___y_817_);
lean_ctor_set(v___x_878_, 1, v___y_826_);
lean_ctor_set(v___x_878_, 2, v___y_825_);
v___x_879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_880_, 0, v___y_817_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__40));
v___x_882_ = l_Lean_Name_mkStr4(v___y_822_, v___x_831_, v___x_832_, v___x_881_);
v___x_883_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__42, &l_Lean_Elab_Command_elabElabRulesAux___closed__42_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__42);
v___x_884_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__43));
v___x_885_ = l_Lean_Name_mkStr4(v___y_822_, v___y_819_, v___x_832_, v___x_884_);
lean_inc(v___x_885_);
v___x_886_ = l_Lean_addMacroScope(v___y_816_, v___x_885_, v___y_827_);
v___x_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_849_);
v___x_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v___x_849_);
v___x_889_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_889_, 0, v___y_817_);
lean_ctor_set(v___x_889_, 1, v___x_883_);
lean_ctor_set(v___x_889_, 2, v___x_886_);
lean_ctor_set(v___x_889_, 3, v___x_888_);
v___x_890_ = l_Lean_Syntax_node1(v___y_817_, v___y_826_, v___y_823_);
v___x_891_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_892_ = l_Lean_Name_mkStr4(v___y_822_, v___x_831_, v___x_832_, v___x_891_);
v___x_893_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_893_, 0, v___y_817_);
lean_ctor_set(v___x_893_, 1, v___x_891_);
v___x_894_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_895_ = l_Lean_Name_mkStr4(v___y_822_, v___x_831_, v___x_832_, v___x_894_);
lean_inc_ref_n(v___x_878_, 4);
v___x_896_ = l_Lean_Syntax_node2(v___y_817_, v___x_895_, v___x_878_, v___x_872_);
v___x_897_ = l_Lean_Syntax_node1(v___y_817_, v___y_826_, v___x_896_);
v___x_898_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_899_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_899_, 0, v___y_817_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_901_ = l_Lean_Name_mkStr4(v___y_822_, v___x_831_, v___x_832_, v___x_900_);
v___x_902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_903_ = l_Lean_Name_mkStr4(v___y_822_, v___x_831_, v___x_832_, v___x_902_);
v___x_904_ = l_Array_append___redArg(v___y_825_, v_a_674_);
lean_dec(v_a_674_);
v___x_905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_906_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_906_, 0, v___y_817_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_908_ = l_Lean_Name_mkStr4(v___y_822_, v___x_831_, v___x_832_, v___x_907_);
v___x_909_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_910_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_910_, 0, v___y_817_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = l_Lean_Syntax_node1(v___y_817_, v___x_908_, v___x_910_);
v___x_912_ = l_Lean_Syntax_node1(v___y_817_, v___y_826_, v___x_911_);
v___x_913_ = l_Lean_Syntax_node1(v___y_817_, v___y_826_, v___x_912_);
v___x_914_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_915_ = l_Lean_Name_mkStr4(v___y_822_, v___x_831_, v___x_832_, v___x_914_);
v___x_916_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_917_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_917_, 0, v___y_817_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_919_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_920_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_921_ = l_Lean_addMacroScope(v___y_816_, v___x_920_, v___y_827_);
v___x_922_ = l_Lean_Name_mkStr3(v___y_822_, v___y_819_, v___x_918_);
v___x_923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v___x_849_);
v___x_924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v___x_849_);
v___x_925_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_925_, 0, v___y_817_);
lean_ctor_set(v___x_925_, 1, v___x_919_);
lean_ctor_set(v___x_925_, 2, v___x_921_);
lean_ctor_set(v___x_925_, 3, v___x_924_);
v___x_926_ = l_Lean_Syntax_node2(v___y_817_, v___x_915_, v___x_917_, v___x_925_);
lean_inc_ref_n(v___x_880_, 2);
v___x_927_ = l_Lean_Syntax_node4(v___y_817_, v___x_903_, v___x_906_, v___x_913_, v___x_880_, v___x_926_);
v___x_928_ = lean_array_push(v___x_904_, v___x_927_);
v___x_929_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_929_, 0, v___y_817_);
lean_ctor_set(v___x_929_, 1, v___y_826_);
lean_ctor_set(v___x_929_, 2, v___x_928_);
v___x_930_ = l_Lean_Syntax_node1(v___y_817_, v___x_901_, v___x_929_);
v___x_931_ = l_Lean_Syntax_node6(v___y_817_, v___x_892_, v___x_893_, v___x_878_, v___x_878_, v___x_897_, v___x_899_, v___x_930_);
lean_inc(v___x_868_);
v___x_932_ = l_Lean_Syntax_node4(v___y_817_, v___x_868_, v___x_890_, v___x_878_, v___x_880_, v___x_931_);
lean_inc_ref(v___x_866_);
lean_inc(v___x_865_);
v___x_933_ = l_Lean_Syntax_node2(v___y_817_, v___x_865_, v___x_866_, v___x_932_);
v___x_934_ = l_Lean_Syntax_node2(v___y_817_, v___y_826_, v___x_876_, v___x_933_);
v___x_935_ = l_Lean_Syntax_node2(v___y_817_, v___x_882_, v___x_889_, v___x_934_);
v___x_936_ = l_Lean_Syntax_node4(v___y_817_, v___x_868_, v___x_877_, v___x_878_, v___x_880_, v___x_935_);
v___x_937_ = l_Lean_Syntax_node2(v___y_817_, v___x_865_, v___x_866_, v___x_936_);
v___x_938_ = lean_unsigned_to_nat(9u);
v___x_939_ = lean_mk_empty_array_with_capacity(v___x_938_);
v___x_940_ = lean_array_push(v___x_939_, v___x_830_);
v___x_941_ = lean_array_push(v___x_940_, v___x_844_);
v___x_942_ = lean_array_push(v___x_941_, v___y_818_);
v___x_943_ = lean_array_push(v___x_942_, v___x_845_);
v___x_944_ = lean_array_push(v___x_943_, v___x_852_);
v___x_945_ = lean_array_push(v___x_944_, v___x_854_);
v___x_946_ = lean_array_push(v___x_945_, v___x_861_);
v___x_947_ = lean_array_push(v___x_946_, v___x_863_);
v___x_948_ = lean_array_push(v___x_947_, v___x_937_);
lean_inc(v___y_824_);
v___x_949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_949_, 0, v___y_817_);
lean_ctor_set(v___x_949_, 1, v___y_824_);
lean_ctor_set(v___x_949_, 2, v___x_948_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
return v___x_950_;
}
v___jp_951_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_958_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_959_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_960_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_961_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_962_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_963_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_661_) == 1)
{
lean_object* v_val_964_; lean_object* v___x_965_; 
v_val_964_ = lean_ctor_get(v_doc_x3f_661_, 0);
lean_inc(v_val_964_);
lean_dec_ref_known(v_doc_x3f_661_, 1);
v___x_965_ = l_Array_mkArray1___redArg(v_val_964_);
v___y_816_ = v_a_957_;
v___y_817_ = v___y_954_;
v___y_818_ = v___y_953_;
v___y_819_ = v___x_959_;
v___y_820_ = v___y_956_;
v___y_821_ = v___x_960_;
v___y_822_ = v___x_958_;
v___y_823_ = v___y_952_;
v___y_824_ = v___x_961_;
v___y_825_ = v___x_963_;
v___y_826_ = v___x_962_;
v___y_827_ = v___y_955_;
v___y_828_ = v___x_965_;
goto v___jp_815_;
}
else
{
lean_object* v___x_966_; 
lean_dec(v_doc_x3f_661_);
v___x_966_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_816_ = v_a_957_;
v___y_817_ = v___y_954_;
v___y_818_ = v___y_953_;
v___y_819_ = v___x_959_;
v___y_820_ = v___y_956_;
v___y_821_ = v___x_960_;
v___y_822_ = v___x_958_;
v___y_823_ = v___y_952_;
v___y_824_ = v___x_961_;
v___y_825_ = v___x_963_;
v___y_826_ = v___x_962_;
v___y_827_ = v___y_955_;
v___y_828_ = v___x_966_;
goto v___jp_815_;
}
}
v___jp_967_:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
lean_inc_ref_n(v___y_972_, 3);
v___x_980_ = l_Array_append___redArg(v___y_972_, v___y_979_);
lean_dec_ref(v___y_979_);
lean_inc_n(v___y_976_, 7);
lean_inc_n(v___y_974_, 26);
v___x_981_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_981_, 0, v___y_974_);
lean_ctor_set(v___x_981_, 1, v___y_976_);
lean_ctor_set(v___x_981_, 2, v___x_980_);
v___x_982_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_983_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_984_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_971_, 8);
v___x_985_ = l_Lean_Name_mkStr4(v___y_971_, v___x_982_, v___x_983_, v___x_984_);
v___x_986_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_987_, 0, v___y_974_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_989_ = l_Lean_Syntax_SepArray_ofElems(v___x_988_, v___y_975_);
lean_dec_ref(v___y_975_);
v___x_990_ = l_Array_append___redArg(v___y_972_, v___x_989_);
lean_dec_ref(v___x_989_);
v___x_991_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_991_, 0, v___y_974_);
lean_ctor_set(v___x_991_, 1, v___y_976_);
lean_ctor_set(v___x_991_, 2, v___x_990_);
v___x_992_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_993_, 0, v___y_974_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = l_Lean_Syntax_node3(v___y_974_, v___x_985_, v___x_987_, v___x_991_, v___x_993_);
v___x_995_ = l_Lean_Syntax_node1(v___y_974_, v___y_976_, v___x_994_);
lean_inc_ref(v___y_978_);
v___x_996_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_996_, 0, v___y_974_);
lean_ctor_set(v___x_996_, 1, v___y_978_);
v___x_997_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_998_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_977_, 2);
lean_inc_n(v___y_973_, 2);
v___x_999_ = l_Lean_addMacroScope(v___y_973_, v___x_998_, v___y_977_);
v___x_1000_ = lean_box(0);
v___x_1001_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1001_, 0, v___y_974_);
lean_ctor_set(v___x_1001_, 1, v___x_997_);
lean_ctor_set(v___x_1001_, 2, v___x_999_);
lean_ctor_set(v___x_1001_, 3, v___x_1000_);
v___x_1002_ = l_Lean_mkIdent(v_k_664_);
v___x_1003_ = l_Lean_Syntax_node2(v___y_974_, v___y_976_, v___x_1001_, v___x_1002_);
v___x_1004_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___y_974_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__45, &l_Lean_Elab_Command_elabElabRulesAux___closed__45_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__45);
v___x_1007_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__46));
lean_inc_ref_n(v___y_969_, 2);
v___x_1008_ = l_Lean_Name_mkStr4(v___y_971_, v___y_969_, v___x_1007_, v___x_1007_);
lean_inc(v___x_1008_);
v___x_1009_ = l_Lean_addMacroScope(v___y_973_, v___x_1008_, v___y_977_);
v___x_1010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1000_);
v___x_1011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_1000_);
v___x_1012_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1012_, 0, v___y_974_);
lean_ctor_set(v___x_1012_, 1, v___x_1006_);
lean_ctor_set(v___x_1012_, 2, v___x_1009_);
lean_ctor_set(v___x_1012_, 3, v___x_1011_);
v___x_1013_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1014_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___y_974_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1016_ = l_Lean_Name_mkStr4(v___y_971_, v___x_982_, v___x_983_, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___y_974_);
lean_ctor_set(v___x_1017_, 1, v___x_1015_);
v___x_1018_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1019_ = l_Lean_Name_mkStr4(v___y_971_, v___x_982_, v___x_983_, v___x_1018_);
v___x_1020_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1021_ = l_Lean_Name_mkStr4(v___y_971_, v___x_982_, v___x_983_, v___x_1020_);
v___x_1022_ = l_Array_append___redArg(v___y_972_, v_a_674_);
lean_dec(v_a_674_);
v___x_1023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1024_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___y_974_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1026_ = l_Lean_Name_mkStr4(v___y_971_, v___x_982_, v___x_983_, v___x_1025_);
v___x_1027_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1028_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___y_974_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = l_Lean_Syntax_node1(v___y_974_, v___x_1026_, v___x_1028_);
v___x_1030_ = l_Lean_Syntax_node1(v___y_974_, v___y_976_, v___x_1029_);
v___x_1031_ = l_Lean_Syntax_node1(v___y_974_, v___y_976_, v___x_1030_);
v___x_1032_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1033_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___y_974_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1035_ = l_Lean_Name_mkStr4(v___y_971_, v___x_982_, v___x_983_, v___x_1034_);
v___x_1036_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1037_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___y_974_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1039_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_1040_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1041_ = l_Lean_addMacroScope(v___y_973_, v___x_1040_, v___y_977_);
v___x_1042_ = l_Lean_Name_mkStr3(v___y_971_, v___y_969_, v___x_1038_);
v___x_1043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v___x_1000_);
v___x_1044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set(v___x_1044_, 1, v___x_1000_);
v___x_1045_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1045_, 0, v___y_974_);
lean_ctor_set(v___x_1045_, 1, v___x_1039_);
lean_ctor_set(v___x_1045_, 2, v___x_1041_);
lean_ctor_set(v___x_1045_, 3, v___x_1044_);
v___x_1046_ = l_Lean_Syntax_node2(v___y_974_, v___x_1035_, v___x_1037_, v___x_1045_);
v___x_1047_ = l_Lean_Syntax_node4(v___y_974_, v___x_1021_, v___x_1024_, v___x_1031_, v___x_1033_, v___x_1046_);
v___x_1048_ = lean_array_push(v___x_1022_, v___x_1047_);
v___x_1049_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1049_, 0, v___y_974_);
lean_ctor_set(v___x_1049_, 1, v___y_976_);
lean_ctor_set(v___x_1049_, 2, v___x_1048_);
v___x_1050_ = l_Lean_Syntax_node1(v___y_974_, v___x_1019_, v___x_1049_);
v___x_1051_ = l_Lean_Syntax_node2(v___y_974_, v___x_1016_, v___x_1017_, v___x_1050_);
v___x_1052_ = lean_unsigned_to_nat(9u);
v___x_1053_ = lean_mk_empty_array_with_capacity(v___x_1052_);
v___x_1054_ = lean_array_push(v___x_1053_, v___x_981_);
v___x_1055_ = lean_array_push(v___x_1054_, v___x_995_);
v___x_1056_ = lean_array_push(v___x_1055_, v___y_970_);
v___x_1057_ = lean_array_push(v___x_1056_, v___x_996_);
v___x_1058_ = lean_array_push(v___x_1057_, v___x_1003_);
v___x_1059_ = lean_array_push(v___x_1058_, v___x_1005_);
v___x_1060_ = lean_array_push(v___x_1059_, v___x_1012_);
v___x_1061_ = lean_array_push(v___x_1060_, v___x_1014_);
v___x_1062_ = lean_array_push(v___x_1061_, v___x_1051_);
lean_inc(v___y_968_);
v___x_1063_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1063_, 0, v___y_974_);
lean_ctor_set(v___x_1063_, 1, v___y_968_);
lean_ctor_set(v___x_1063_, 2, v___x_1062_);
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
v___jp_1065_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1071_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1072_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1073_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1074_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1075_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1076_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_661_) == 1)
{
lean_object* v_val_1077_; lean_object* v___x_1078_; 
v_val_1077_ = lean_ctor_get(v_doc_x3f_661_, 0);
lean_inc(v_val_1077_);
lean_dec_ref_known(v_doc_x3f_661_, 1);
v___x_1078_ = l_Array_mkArray1___redArg(v_val_1077_);
v___y_968_ = v___x_1074_;
v___y_969_ = v___x_1072_;
v___y_970_ = v___y_1066_;
v___y_971_ = v___x_1071_;
v___y_972_ = v___x_1076_;
v___y_973_ = v_a_1070_;
v___y_974_ = v___y_1067_;
v___y_975_ = v___y_1068_;
v___y_976_ = v___x_1075_;
v___y_977_ = v___y_1069_;
v___y_978_ = v___x_1073_;
v___y_979_ = v___x_1078_;
goto v___jp_967_;
}
else
{
lean_object* v___x_1079_; 
lean_dec(v_doc_x3f_661_);
v___x_1079_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_968_ = v___x_1074_;
v___y_969_ = v___x_1072_;
v___y_970_ = v___y_1066_;
v___y_971_ = v___x_1071_;
v___y_972_ = v___x_1076_;
v___y_973_ = v_a_1070_;
v___y_974_ = v___y_1067_;
v___y_975_ = v___y_1068_;
v___y_976_ = v___x_1075_;
v___y_977_ = v___y_1069_;
v___y_978_ = v___x_1073_;
v___y_979_ = v___x_1079_;
goto v___jp_967_;
}
}
v___jp_1080_:
{
lean_object* v___x_1086_; 
lean_inc(v___y_1081_);
lean_inc(v_k_664_);
v___x_1086_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_664_, v_attrKind_663_, v_attrs_x3f_662_, v___y_1081_, v___y_1083_, v___y_1082_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1088_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1088_ = l_Lean_Elab_Command_getRef___redArg(v___y_1083_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 1);
v___x_1090_ = l_Lean_SourceInfo_fromRef(v_a_1089_, v___y_1085_);
lean_dec(v_a_1089_);
v___x_1091_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1083_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_quotContext_x3f_1092_; 
v_quotContext_x3f_1092_ = lean_ctor_get(v___y_1083_, 5);
if (lean_obj_tag(v_quotContext_x3f_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1094_; lean_object* v_a_1095_; 
v_a_1093_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1091_, 1);
v___x_1094_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1082_);
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref(v___x_1094_);
v___y_1066_ = v___y_1084_;
v___y_1067_ = v___x_1090_;
v___y_1068_ = v_a_1087_;
v___y_1069_ = v_a_1093_;
v_a_1070_ = v_a_1095_;
goto v___jp_1065_;
}
else
{
lean_object* v_a_1096_; lean_object* v_val_1097_; 
v_a_1096_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1091_, 1);
v_val_1097_ = lean_ctor_get(v_quotContext_x3f_1092_, 0);
lean_inc(v_val_1097_);
v___y_1066_ = v___y_1084_;
v___y_1067_ = v___x_1090_;
v___y_1068_ = v_a_1087_;
v___y_1069_ = v_a_1096_;
v_a_1070_ = v_val_1097_;
goto v___jp_1065_;
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec(v___x_1090_);
lean_dec(v_a_1087_);
lean_dec(v___y_1084_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1098_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1091_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1091_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
else
{
lean_dec(v_a_1087_);
lean_dec(v___y_1084_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
return v___x_1088_;
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec(v___y_1084_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1106_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1086_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1086_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
v___jp_1114_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_inc_ref_n(v___y_1120_, 4);
v___x_1127_ = l_Array_append___redArg(v___y_1120_, v___y_1126_);
lean_dec_ref(v___y_1126_);
lean_inc_n(v___y_1124_, 10);
lean_inc_n(v___y_1118_, 36);
v___x_1128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1128_, 0, v___y_1118_);
lean_ctor_set(v___x_1128_, 1, v___y_1124_);
lean_ctor_set(v___x_1128_, 2, v___x_1127_);
v___x_1129_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1130_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1131_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1122_, 11);
v___x_1132_ = l_Lean_Name_mkStr4(v___y_1122_, v___x_1129_, v___x_1130_, v___x_1131_);
v___x_1133_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___y_1118_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1136_ = l_Lean_Syntax_SepArray_ofElems(v___x_1135_, v___y_1117_);
lean_dec_ref(v___y_1117_);
v___x_1137_ = l_Array_append___redArg(v___y_1120_, v___x_1136_);
lean_dec_ref(v___x_1136_);
v___x_1138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1138_, 0, v___y_1118_);
lean_ctor_set(v___x_1138_, 1, v___y_1124_);
lean_ctor_set(v___x_1138_, 2, v___x_1137_);
v___x_1139_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___y_1118_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = l_Lean_Syntax_node3(v___y_1118_, v___x_1132_, v___x_1134_, v___x_1138_, v___x_1140_);
v___x_1142_ = l_Lean_Syntax_node1(v___y_1118_, v___y_1124_, v___x_1141_);
lean_inc_ref(v___y_1121_);
v___x_1143_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___y_1118_);
lean_ctor_set(v___x_1143_, 1, v___y_1121_);
v___x_1144_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1145_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1115_, 4);
lean_inc_n(v___y_1125_, 4);
v___x_1146_ = l_Lean_addMacroScope(v___y_1125_, v___x_1145_, v___y_1115_);
v___x_1147_ = lean_box(0);
v___x_1148_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1148_, 0, v___y_1118_);
lean_ctor_set(v___x_1148_, 1, v___x_1144_);
lean_ctor_set(v___x_1148_, 2, v___x_1146_);
lean_ctor_set(v___x_1148_, 3, v___x_1147_);
v___x_1149_ = l_Lean_mkIdent(v_k_664_);
v___x_1150_ = l_Lean_Syntax_node2(v___y_1118_, v___y_1124_, v___x_1148_, v___x_1149_);
v___x_1151_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1152_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___y_1118_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_1154_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
v___x_1155_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc_ref_n(v___y_1116_, 2);
v___x_1156_ = l_Lean_Name_mkStr4(v___y_1122_, v___y_1116_, v___x_1154_, v___x_1155_);
lean_inc(v___x_1156_);
v___x_1157_ = l_Lean_addMacroScope(v___y_1125_, v___x_1156_, v___y_1115_);
v___x_1158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1147_);
v___x_1159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
lean_ctor_set(v___x_1159_, 1, v___x_1147_);
v___x_1160_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1160_, 0, v___y_1118_);
lean_ctor_set(v___x_1160_, 1, v___x_1153_);
lean_ctor_set(v___x_1160_, 2, v___x_1157_);
lean_ctor_set(v___x_1160_, 3, v___x_1159_);
v___x_1161_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1162_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___y_1118_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1164_ = l_Lean_Name_mkStr4(v___y_1122_, v___x_1129_, v___x_1130_, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___y_1118_);
lean_ctor_set(v___x_1165_, 1, v___x_1163_);
v___x_1166_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_1167_ = l_Lean_Name_mkStr4(v___y_1122_, v___x_1129_, v___x_1130_, v___x_1166_);
v___x_1168_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_1169_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1170_ = l_Lean_addMacroScope(v___y_1125_, v___x_1169_, v___y_1115_);
v___x_1171_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1171_, 0, v___y_1118_);
lean_ctor_set(v___x_1171_, 1, v___x_1168_);
lean_ctor_set(v___x_1171_, 2, v___x_1170_);
lean_ctor_set(v___x_1171_, 3, v___x_1147_);
v___x_1172_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__48, &l_Lean_Elab_Command_elabElabRulesAux___closed__48_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__48);
v___x_1173_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__49));
v___x_1174_ = l_Lean_addMacroScope(v___y_1125_, v___x_1173_, v___y_1115_);
v___x_1175_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1175_, 0, v___y_1118_);
lean_ctor_set(v___x_1175_, 1, v___x_1172_);
lean_ctor_set(v___x_1175_, 2, v___x_1174_);
lean_ctor_set(v___x_1175_, 3, v___x_1147_);
lean_inc_ref(v___x_1171_);
v___x_1176_ = l_Lean_Syntax_node2(v___y_1118_, v___y_1124_, v___x_1171_, v___x_1175_);
v___x_1177_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1177_, 0, v___y_1118_);
lean_ctor_set(v___x_1177_, 1, v___y_1124_);
lean_ctor_set(v___x_1177_, 2, v___y_1120_);
v___x_1178_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___y_1118_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1181_ = l_Lean_Name_mkStr4(v___y_1122_, v___x_1129_, v___x_1130_, v___x_1180_);
v___x_1182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___y_1118_);
lean_ctor_set(v___x_1182_, 1, v___x_1180_);
v___x_1183_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_1184_ = l_Lean_Name_mkStr4(v___y_1122_, v___x_1129_, v___x_1130_, v___x_1183_);
lean_inc_ref_n(v___x_1177_, 3);
v___x_1185_ = l_Lean_Syntax_node2(v___y_1118_, v___x_1184_, v___x_1177_, v___x_1171_);
v___x_1186_ = l_Lean_Syntax_node1(v___y_1118_, v___y_1124_, v___x_1185_);
v___x_1187_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_1188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___y_1118_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1190_ = l_Lean_Name_mkStr4(v___y_1122_, v___x_1129_, v___x_1130_, v___x_1189_);
v___x_1191_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1192_ = l_Lean_Name_mkStr4(v___y_1122_, v___x_1129_, v___x_1130_, v___x_1191_);
v___x_1193_ = l_Array_append___redArg(v___y_1120_, v_a_674_);
lean_dec(v_a_674_);
v___x_1194_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1195_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___y_1118_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1197_ = l_Lean_Name_mkStr4(v___y_1122_, v___x_1129_, v___x_1130_, v___x_1196_);
v___x_1198_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1199_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___y_1118_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = l_Lean_Syntax_node1(v___y_1118_, v___x_1197_, v___x_1199_);
v___x_1201_ = l_Lean_Syntax_node1(v___y_1118_, v___y_1124_, v___x_1200_);
v___x_1202_ = l_Lean_Syntax_node1(v___y_1118_, v___y_1124_, v___x_1201_);
v___x_1203_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1204_ = l_Lean_Name_mkStr4(v___y_1122_, v___x_1129_, v___x_1130_, v___x_1203_);
v___x_1205_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___y_1118_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1208_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_1209_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1210_ = l_Lean_addMacroScope(v___y_1125_, v___x_1209_, v___y_1115_);
v___x_1211_ = l_Lean_Name_mkStr3(v___y_1122_, v___y_1116_, v___x_1207_);
v___x_1212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
lean_ctor_set(v___x_1212_, 1, v___x_1147_);
v___x_1213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v___x_1147_);
v___x_1214_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1214_, 0, v___y_1118_);
lean_ctor_set(v___x_1214_, 1, v___x_1208_);
lean_ctor_set(v___x_1214_, 2, v___x_1210_);
lean_ctor_set(v___x_1214_, 3, v___x_1213_);
v___x_1215_ = l_Lean_Syntax_node2(v___y_1118_, v___x_1204_, v___x_1206_, v___x_1214_);
lean_inc_ref(v___x_1179_);
v___x_1216_ = l_Lean_Syntax_node4(v___y_1118_, v___x_1192_, v___x_1195_, v___x_1202_, v___x_1179_, v___x_1215_);
v___x_1217_ = lean_array_push(v___x_1193_, v___x_1216_);
v___x_1218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1218_, 0, v___y_1118_);
lean_ctor_set(v___x_1218_, 1, v___y_1124_);
lean_ctor_set(v___x_1218_, 2, v___x_1217_);
v___x_1219_ = l_Lean_Syntax_node1(v___y_1118_, v___x_1190_, v___x_1218_);
v___x_1220_ = l_Lean_Syntax_node6(v___y_1118_, v___x_1181_, v___x_1182_, v___x_1177_, v___x_1177_, v___x_1186_, v___x_1188_, v___x_1219_);
v___x_1221_ = l_Lean_Syntax_node4(v___y_1118_, v___x_1167_, v___x_1176_, v___x_1177_, v___x_1179_, v___x_1220_);
v___x_1222_ = l_Lean_Syntax_node2(v___y_1118_, v___x_1164_, v___x_1165_, v___x_1221_);
v___x_1223_ = lean_unsigned_to_nat(9u);
v___x_1224_ = lean_mk_empty_array_with_capacity(v___x_1223_);
v___x_1225_ = lean_array_push(v___x_1224_, v___x_1128_);
v___x_1226_ = lean_array_push(v___x_1225_, v___x_1142_);
v___x_1227_ = lean_array_push(v___x_1226_, v___y_1119_);
v___x_1228_ = lean_array_push(v___x_1227_, v___x_1143_);
v___x_1229_ = lean_array_push(v___x_1228_, v___x_1150_);
v___x_1230_ = lean_array_push(v___x_1229_, v___x_1152_);
v___x_1231_ = lean_array_push(v___x_1230_, v___x_1160_);
v___x_1232_ = lean_array_push(v___x_1231_, v___x_1162_);
v___x_1233_ = lean_array_push(v___x_1232_, v___x_1222_);
lean_inc(v___y_1123_);
v___x_1234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1234_, 0, v___y_1118_);
lean_ctor_set(v___x_1234_, 1, v___y_1123_);
lean_ctor_set(v___x_1234_, 2, v___x_1233_);
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
return v___x_1235_;
}
v___jp_1236_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1242_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1243_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1244_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1245_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1246_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1247_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_661_) == 1)
{
lean_object* v_val_1248_; lean_object* v___x_1249_; 
v_val_1248_ = lean_ctor_get(v_doc_x3f_661_, 0);
lean_inc(v_val_1248_);
lean_dec_ref_known(v_doc_x3f_661_, 1);
v___x_1249_ = l_Array_mkArray1___redArg(v_val_1248_);
v___y_1115_ = v___y_1237_;
v___y_1116_ = v___x_1243_;
v___y_1117_ = v___y_1239_;
v___y_1118_ = v___y_1238_;
v___y_1119_ = v___y_1240_;
v___y_1120_ = v___x_1247_;
v___y_1121_ = v___x_1244_;
v___y_1122_ = v___x_1242_;
v___y_1123_ = v___x_1245_;
v___y_1124_ = v___x_1246_;
v___y_1125_ = v_a_1241_;
v___y_1126_ = v___x_1249_;
goto v___jp_1114_;
}
else
{
lean_object* v___x_1250_; 
lean_dec(v_doc_x3f_661_);
v___x_1250_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_1115_ = v___y_1237_;
v___y_1116_ = v___x_1243_;
v___y_1117_ = v___y_1239_;
v___y_1118_ = v___y_1238_;
v___y_1119_ = v___y_1240_;
v___y_1120_ = v___x_1247_;
v___y_1121_ = v___x_1244_;
v___y_1122_ = v___x_1242_;
v___y_1123_ = v___x_1245_;
v___y_1124_ = v___x_1246_;
v___y_1125_ = v_a_1241_;
v___y_1126_ = v___x_1250_;
goto v___jp_1114_;
}
}
v___jp_1251_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_inc_ref_n(v___y_1263_, 3);
v___x_1265_ = l_Array_append___redArg(v___y_1263_, v___y_1264_);
lean_dec_ref(v___y_1264_);
lean_inc_n(v___y_1260_, 7);
lean_inc_n(v___y_1259_, 26);
v___x_1266_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1266_, 0, v___y_1259_);
lean_ctor_set(v___x_1266_, 1, v___y_1260_);
lean_ctor_set(v___x_1266_, 2, v___x_1265_);
v___x_1267_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1268_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1269_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1258_, 8);
v___x_1270_ = l_Lean_Name_mkStr4(v___y_1258_, v___x_1267_, v___x_1268_, v___x_1269_);
v___x_1271_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1272_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___y_1259_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1274_ = l_Lean_Syntax_SepArray_ofElems(v___x_1273_, v___y_1253_);
lean_dec_ref(v___y_1253_);
v___x_1275_ = l_Array_append___redArg(v___y_1263_, v___x_1274_);
lean_dec_ref(v___x_1274_);
v___x_1276_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1276_, 0, v___y_1259_);
lean_ctor_set(v___x_1276_, 1, v___y_1260_);
lean_ctor_set(v___x_1276_, 2, v___x_1275_);
v___x_1277_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___y_1259_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = l_Lean_Syntax_node3(v___y_1259_, v___x_1270_, v___x_1272_, v___x_1276_, v___x_1278_);
v___x_1280_ = l_Lean_Syntax_node1(v___y_1259_, v___y_1260_, v___x_1279_);
lean_inc_ref(v___y_1252_);
v___x_1281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___y_1259_);
lean_ctor_set(v___x_1281_, 1, v___y_1252_);
v___x_1282_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1283_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1262_, 2);
lean_inc_n(v___y_1254_, 2);
v___x_1284_ = l_Lean_addMacroScope(v___y_1254_, v___x_1283_, v___y_1262_);
v___x_1285_ = lean_box(0);
v___x_1286_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1286_, 0, v___y_1259_);
lean_ctor_set(v___x_1286_, 1, v___x_1282_);
lean_ctor_set(v___x_1286_, 2, v___x_1284_);
lean_ctor_set(v___x_1286_, 3, v___x_1285_);
v___x_1287_ = l_Lean_mkIdent(v_k_664_);
v___x_1288_ = l_Lean_Syntax_node2(v___y_1259_, v___y_1260_, v___x_1286_, v___x_1287_);
v___x_1289_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___y_1259_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__51, &l_Lean_Elab_Command_elabElabRulesAux___closed__51_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__51);
v___x_1292_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__52));
lean_inc_ref(v___y_1255_);
lean_inc_ref_n(v___y_1257_, 2);
v___x_1293_ = l_Lean_Name_mkStr4(v___y_1258_, v___y_1257_, v___y_1255_, v___x_1292_);
lean_inc(v___x_1293_);
v___x_1294_ = l_Lean_addMacroScope(v___y_1254_, v___x_1293_, v___y_1262_);
v___x_1295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1293_);
lean_ctor_set(v___x_1295_, 1, v___x_1285_);
v___x_1296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
lean_ctor_set(v___x_1296_, 1, v___x_1285_);
v___x_1297_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1297_, 0, v___y_1259_);
lean_ctor_set(v___x_1297_, 1, v___x_1291_);
lean_ctor_set(v___x_1297_, 2, v___x_1294_);
lean_ctor_set(v___x_1297_, 3, v___x_1296_);
v___x_1298_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___y_1259_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
v___x_1300_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1301_ = l_Lean_Name_mkStr4(v___y_1258_, v___x_1267_, v___x_1268_, v___x_1300_);
v___x_1302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___y_1259_);
lean_ctor_set(v___x_1302_, 1, v___x_1300_);
v___x_1303_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1304_ = l_Lean_Name_mkStr4(v___y_1258_, v___x_1267_, v___x_1268_, v___x_1303_);
v___x_1305_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1306_ = l_Lean_Name_mkStr4(v___y_1258_, v___x_1267_, v___x_1268_, v___x_1305_);
v___x_1307_ = l_Array_append___redArg(v___y_1263_, v_a_674_);
lean_dec(v_a_674_);
v___x_1308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1309_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___y_1259_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1311_ = l_Lean_Name_mkStr4(v___y_1258_, v___x_1267_, v___x_1268_, v___x_1310_);
v___x_1312_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___y_1259_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = l_Lean_Syntax_node1(v___y_1259_, v___x_1311_, v___x_1313_);
v___x_1315_ = l_Lean_Syntax_node1(v___y_1259_, v___y_1260_, v___x_1314_);
v___x_1316_ = l_Lean_Syntax_node1(v___y_1259_, v___y_1260_, v___x_1315_);
v___x_1317_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1318_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___y_1259_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
v___x_1319_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1320_ = l_Lean_Name_mkStr4(v___y_1258_, v___x_1267_, v___x_1268_, v___x_1319_);
v___x_1321_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1322_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___y_1259_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___x_1323_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1324_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_1325_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1326_ = l_Lean_addMacroScope(v___y_1254_, v___x_1325_, v___y_1262_);
v___x_1327_ = l_Lean_Name_mkStr3(v___y_1258_, v___y_1257_, v___x_1323_);
v___x_1328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
lean_ctor_set(v___x_1328_, 1, v___x_1285_);
v___x_1329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
lean_ctor_set(v___x_1329_, 1, v___x_1285_);
v___x_1330_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1330_, 0, v___y_1259_);
lean_ctor_set(v___x_1330_, 1, v___x_1324_);
lean_ctor_set(v___x_1330_, 2, v___x_1326_);
lean_ctor_set(v___x_1330_, 3, v___x_1329_);
v___x_1331_ = l_Lean_Syntax_node2(v___y_1259_, v___x_1320_, v___x_1322_, v___x_1330_);
v___x_1332_ = l_Lean_Syntax_node4(v___y_1259_, v___x_1306_, v___x_1309_, v___x_1316_, v___x_1318_, v___x_1331_);
v___x_1333_ = lean_array_push(v___x_1307_, v___x_1332_);
v___x_1334_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1334_, 0, v___y_1259_);
lean_ctor_set(v___x_1334_, 1, v___y_1260_);
lean_ctor_set(v___x_1334_, 2, v___x_1333_);
v___x_1335_ = l_Lean_Syntax_node1(v___y_1259_, v___x_1304_, v___x_1334_);
v___x_1336_ = l_Lean_Syntax_node2(v___y_1259_, v___x_1301_, v___x_1302_, v___x_1335_);
v___x_1337_ = lean_unsigned_to_nat(9u);
v___x_1338_ = lean_mk_empty_array_with_capacity(v___x_1337_);
v___x_1339_ = lean_array_push(v___x_1338_, v___x_1266_);
v___x_1340_ = lean_array_push(v___x_1339_, v___x_1280_);
v___x_1341_ = lean_array_push(v___x_1340_, v___y_1256_);
v___x_1342_ = lean_array_push(v___x_1341_, v___x_1281_);
v___x_1343_ = lean_array_push(v___x_1342_, v___x_1288_);
v___x_1344_ = lean_array_push(v___x_1343_, v___x_1290_);
v___x_1345_ = lean_array_push(v___x_1344_, v___x_1297_);
v___x_1346_ = lean_array_push(v___x_1345_, v___x_1299_);
v___x_1347_ = lean_array_push(v___x_1346_, v___x_1336_);
lean_inc(v___y_1261_);
v___x_1348_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1348_, 0, v___y_1259_);
lean_ctor_set(v___x_1348_, 1, v___y_1261_);
lean_ctor_set(v___x_1348_, 2, v___x_1347_);
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
return v___x_1349_;
}
v___jp_1350_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1356_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1357_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1358_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_1359_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1360_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1361_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1362_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_661_) == 1)
{
lean_object* v_val_1363_; lean_object* v___x_1364_; 
v_val_1363_ = lean_ctor_get(v_doc_x3f_661_, 0);
lean_inc(v_val_1363_);
lean_dec_ref_known(v_doc_x3f_661_, 1);
v___x_1364_ = l_Array_mkArray1___redArg(v_val_1363_);
v___y_1252_ = v___x_1359_;
v___y_1253_ = v___y_1352_;
v___y_1254_ = v_a_1355_;
v___y_1255_ = v___x_1358_;
v___y_1256_ = v___y_1354_;
v___y_1257_ = v___x_1357_;
v___y_1258_ = v___x_1356_;
v___y_1259_ = v___y_1351_;
v___y_1260_ = v___x_1361_;
v___y_1261_ = v___x_1360_;
v___y_1262_ = v___y_1353_;
v___y_1263_ = v___x_1362_;
v___y_1264_ = v___x_1364_;
goto v___jp_1251_;
}
else
{
lean_object* v___x_1365_; 
lean_dec(v_doc_x3f_661_);
v___x_1365_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_1252_ = v___x_1359_;
v___y_1253_ = v___y_1352_;
v___y_1254_ = v_a_1355_;
v___y_1255_ = v___x_1358_;
v___y_1256_ = v___y_1354_;
v___y_1257_ = v___x_1357_;
v___y_1258_ = v___x_1356_;
v___y_1259_ = v___y_1351_;
v___y_1260_ = v___x_1361_;
v___y_1261_ = v___x_1360_;
v___y_1262_ = v___y_1353_;
v___y_1263_ = v___x_1362_;
v___y_1264_ = v___x_1365_;
goto v___jp_1251_;
}
}
v___jp_1366_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_inc_ref_n(v___y_1371_, 4);
v___x_1379_ = l_Array_append___redArg(v___y_1371_, v___y_1378_);
lean_dec_ref(v___y_1378_);
lean_inc_n(v___y_1377_, 10);
lean_inc_n(v___y_1367_, 35);
v___x_1380_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1380_, 0, v___y_1367_);
lean_ctor_set(v___x_1380_, 1, v___y_1377_);
lean_ctor_set(v___x_1380_, 2, v___x_1379_);
v___x_1381_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1382_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1383_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1370_, 11);
v___x_1384_ = l_Lean_Name_mkStr4(v___y_1370_, v___x_1381_, v___x_1382_, v___x_1383_);
v___x_1385_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___y_1367_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
v___x_1387_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1388_ = l_Lean_Syntax_SepArray_ofElems(v___x_1387_, v___y_1374_);
lean_dec_ref(v___y_1374_);
v___x_1389_ = l_Array_append___redArg(v___y_1371_, v___x_1388_);
lean_dec_ref(v___x_1388_);
v___x_1390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1390_, 0, v___y_1367_);
lean_ctor_set(v___x_1390_, 1, v___y_1377_);
lean_ctor_set(v___x_1390_, 2, v___x_1389_);
v___x_1391_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___y_1367_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = l_Lean_Syntax_node3(v___y_1367_, v___x_1384_, v___x_1386_, v___x_1390_, v___x_1392_);
v___x_1394_ = l_Lean_Syntax_node1(v___y_1367_, v___y_1377_, v___x_1393_);
lean_inc_ref(v___y_1376_);
v___x_1395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___y_1367_);
lean_ctor_set(v___x_1395_, 1, v___y_1376_);
v___x_1396_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1397_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1369_, 3);
lean_inc_n(v___y_1375_, 3);
v___x_1398_ = l_Lean_addMacroScope(v___y_1375_, v___x_1397_, v___y_1369_);
v___x_1399_ = lean_box(0);
v___x_1400_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1400_, 0, v___y_1367_);
lean_ctor_set(v___x_1400_, 1, v___x_1396_);
lean_ctor_set(v___x_1400_, 2, v___x_1398_);
lean_ctor_set(v___x_1400_, 3, v___x_1399_);
v___x_1401_ = l_Lean_mkIdent(v_k_664_);
v___x_1402_ = l_Lean_Syntax_node2(v___y_1367_, v___y_1377_, v___x_1400_, v___x_1401_);
v___x_1403_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1404_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___y_1367_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
v___x_1405_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__35, &l_Lean_Elab_Command_elabElabRulesAux___closed__35_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__35);
v___x_1406_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__36));
lean_inc_ref_n(v___y_1373_, 2);
v___x_1407_ = l_Lean_Name_mkStr4(v___y_1370_, v___y_1373_, v___x_1382_, v___x_1406_);
lean_inc(v___x_1407_);
v___x_1408_ = l_Lean_addMacroScope(v___y_1375_, v___x_1407_, v___y_1369_);
v___x_1409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1407_);
lean_ctor_set(v___x_1409_, 1, v___x_1399_);
v___x_1410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
lean_ctor_set(v___x_1410_, 1, v___x_1399_);
v___x_1411_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1411_, 0, v___y_1367_);
lean_ctor_set(v___x_1411_, 1, v___x_1405_);
lean_ctor_set(v___x_1411_, 2, v___x_1408_);
lean_ctor_set(v___x_1411_, 3, v___x_1410_);
v___x_1412_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1413_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___y_1367_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1415_ = l_Lean_Name_mkStr4(v___y_1370_, v___x_1381_, v___x_1382_, v___x_1414_);
v___x_1416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___y_1367_);
lean_ctor_set(v___x_1416_, 1, v___x_1414_);
v___x_1417_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_1418_ = l_Lean_Name_mkStr4(v___y_1370_, v___x_1381_, v___x_1382_, v___x_1417_);
v___x_1419_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__16, &l_Lean_Elab_Command_elabElabRulesAux___closed__16_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__16);
v___x_1420_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1421_ = l_Lean_addMacroScope(v___y_1375_, v___x_1420_, v___y_1369_);
v___x_1422_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1422_, 0, v___y_1367_);
lean_ctor_set(v___x_1422_, 1, v___x_1419_);
lean_ctor_set(v___x_1422_, 2, v___x_1421_);
lean_ctor_set(v___x_1422_, 3, v___x_1399_);
v___x_1423_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1424_ = l_Lean_Name_mkStr4(v___y_1370_, v___x_1381_, v___x_1382_, v___x_1423_);
v___x_1425_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1426_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___y_1367_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
v___x_1427_ = l_Lean_Syntax_node1(v___y_1367_, v___x_1424_, v___x_1426_);
lean_inc(v___x_1427_);
lean_inc_ref(v___x_1422_);
v___x_1428_ = l_Lean_Syntax_node2(v___y_1367_, v___y_1377_, v___x_1422_, v___x_1427_);
v___x_1429_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1429_, 0, v___y_1367_);
lean_ctor_set(v___x_1429_, 1, v___y_1377_);
lean_ctor_set(v___x_1429_, 2, v___y_1371_);
v___x_1430_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1431_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___y_1367_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1433_ = l_Lean_Name_mkStr4(v___y_1370_, v___x_1381_, v___x_1382_, v___x_1432_);
v___x_1434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___y_1367_);
lean_ctor_set(v___x_1434_, 1, v___x_1432_);
v___x_1435_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_1436_ = l_Lean_Name_mkStr4(v___y_1370_, v___x_1381_, v___x_1382_, v___x_1435_);
lean_inc_ref_n(v___x_1429_, 3);
v___x_1437_ = l_Lean_Syntax_node2(v___y_1367_, v___x_1436_, v___x_1429_, v___x_1422_);
v___x_1438_ = l_Lean_Syntax_node1(v___y_1367_, v___y_1377_, v___x_1437_);
v___x_1439_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_1440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___y_1367_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
v___x_1441_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1442_ = l_Lean_Name_mkStr4(v___y_1370_, v___x_1381_, v___x_1382_, v___x_1441_);
v___x_1443_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1444_ = l_Lean_Name_mkStr4(v___y_1370_, v___x_1381_, v___x_1382_, v___x_1443_);
v___x_1445_ = l_Array_append___redArg(v___y_1371_, v_a_674_);
lean_dec(v_a_674_);
v___x_1446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1447_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___y_1367_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = l_Lean_Syntax_node1(v___y_1367_, v___y_1377_, v___x_1427_);
v___x_1449_ = l_Lean_Syntax_node1(v___y_1367_, v___y_1377_, v___x_1448_);
v___x_1450_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1451_ = l_Lean_Name_mkStr4(v___y_1370_, v___x_1381_, v___x_1382_, v___x_1450_);
v___x_1452_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___y_1367_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
v___x_1454_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__26));
v___x_1455_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__27, &l_Lean_Elab_Command_elabElabRulesAux___closed__27_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__27);
v___x_1456_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1457_ = l_Lean_addMacroScope(v___y_1375_, v___x_1456_, v___y_1369_);
v___x_1458_ = l_Lean_Name_mkStr3(v___y_1370_, v___y_1373_, v___x_1454_);
v___x_1459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
lean_ctor_set(v___x_1459_, 1, v___x_1399_);
v___x_1460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
lean_ctor_set(v___x_1460_, 1, v___x_1399_);
v___x_1461_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1461_, 0, v___y_1367_);
lean_ctor_set(v___x_1461_, 1, v___x_1455_);
lean_ctor_set(v___x_1461_, 2, v___x_1457_);
lean_ctor_set(v___x_1461_, 3, v___x_1460_);
v___x_1462_ = l_Lean_Syntax_node2(v___y_1367_, v___x_1451_, v___x_1453_, v___x_1461_);
lean_inc_ref(v___x_1431_);
v___x_1463_ = l_Lean_Syntax_node4(v___y_1367_, v___x_1444_, v___x_1447_, v___x_1449_, v___x_1431_, v___x_1462_);
v___x_1464_ = lean_array_push(v___x_1445_, v___x_1463_);
v___x_1465_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1465_, 0, v___y_1367_);
lean_ctor_set(v___x_1465_, 1, v___y_1377_);
lean_ctor_set(v___x_1465_, 2, v___x_1464_);
v___x_1466_ = l_Lean_Syntax_node1(v___y_1367_, v___x_1442_, v___x_1465_);
v___x_1467_ = l_Lean_Syntax_node6(v___y_1367_, v___x_1433_, v___x_1434_, v___x_1429_, v___x_1429_, v___x_1438_, v___x_1440_, v___x_1466_);
v___x_1468_ = l_Lean_Syntax_node4(v___y_1367_, v___x_1418_, v___x_1428_, v___x_1429_, v___x_1431_, v___x_1467_);
v___x_1469_ = l_Lean_Syntax_node2(v___y_1367_, v___x_1415_, v___x_1416_, v___x_1468_);
v___x_1470_ = lean_unsigned_to_nat(9u);
v___x_1471_ = lean_mk_empty_array_with_capacity(v___x_1470_);
v___x_1472_ = lean_array_push(v___x_1471_, v___x_1380_);
v___x_1473_ = lean_array_push(v___x_1472_, v___x_1394_);
v___x_1474_ = lean_array_push(v___x_1473_, v___y_1372_);
v___x_1475_ = lean_array_push(v___x_1474_, v___x_1395_);
v___x_1476_ = lean_array_push(v___x_1475_, v___x_1402_);
v___x_1477_ = lean_array_push(v___x_1476_, v___x_1404_);
v___x_1478_ = lean_array_push(v___x_1477_, v___x_1411_);
v___x_1479_ = lean_array_push(v___x_1478_, v___x_1413_);
v___x_1480_ = lean_array_push(v___x_1479_, v___x_1469_);
lean_inc(v___y_1368_);
v___x_1481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1481_, 0, v___y_1367_);
lean_ctor_set(v___x_1481_, 1, v___y_1368_);
lean_ctor_set(v___x_1481_, 2, v___x_1480_);
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
return v___x_1482_;
}
v___jp_1483_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1489_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1490_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_1491_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1492_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___x_1493_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1494_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_661_) == 1)
{
lean_object* v_val_1495_; lean_object* v___x_1496_; 
v_val_1495_ = lean_ctor_get(v_doc_x3f_661_, 0);
lean_inc(v_val_1495_);
lean_dec_ref_known(v_doc_x3f_661_, 1);
v___x_1496_ = l_Array_mkArray1___redArg(v_val_1495_);
v___y_1367_ = v___y_1484_;
v___y_1368_ = v___x_1492_;
v___y_1369_ = v___y_1485_;
v___y_1370_ = v___x_1489_;
v___y_1371_ = v___x_1494_;
v___y_1372_ = v___y_1486_;
v___y_1373_ = v___x_1490_;
v___y_1374_ = v___y_1487_;
v___y_1375_ = v_a_1488_;
v___y_1376_ = v___x_1491_;
v___y_1377_ = v___x_1493_;
v___y_1378_ = v___x_1496_;
goto v___jp_1366_;
}
else
{
lean_object* v___x_1497_; 
lean_dec(v_doc_x3f_661_);
v___x_1497_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_1367_ = v___y_1484_;
v___y_1368_ = v___x_1492_;
v___y_1369_ = v___y_1485_;
v___y_1370_ = v___x_1489_;
v___y_1371_ = v___x_1494_;
v___y_1372_ = v___y_1486_;
v___y_1373_ = v___x_1490_;
v___y_1374_ = v___y_1487_;
v___y_1375_ = v_a_1488_;
v___y_1376_ = v___x_1491_;
v___y_1377_ = v___x_1493_;
v___y_1378_ = v___x_1497_;
goto v___jp_1366_;
}
}
v___jp_1498_:
{
lean_object* v___x_1502_; 
lean_inc(v_attrKind_663_);
v___x_1502_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_663_);
if (lean_obj_tag(v_expty_x3f_666_) == 1)
{
lean_object* v_val_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; 
v_val_1503_ = lean_ctor_get(v_expty_x3f_666_, 0);
lean_inc(v_val_1503_);
lean_dec_ref_known(v_expty_x3f_666_, 1);
v___x_1504_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v___x_1505_ = lean_name_eq(v_catName_1499_, v___x_1504_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1506_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__56));
v___x_1507_ = lean_name_eq(v_catName_1499_, v___x_1506_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_dec(v___x_1502_);
lean_del_object(v___x_676_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_attrKind_663_);
lean_dec(v_doc_x3f_661_);
v___x_1508_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__58, &l_Lean_Elab_Command_elabElabRulesAux___closed__58_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__58);
v___x_1509_ = l_Lean_MessageData_ofName(v_catName_1499_);
v___x_1510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1508_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
v___x_1511_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__60, &l_Lean_Elab_Command_elabElabRulesAux___closed__60_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__60);
v___x_1512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1510_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_val_1503_, v___x_1512_, v___y_1500_, v___y_1501_);
lean_dec(v_val_1503_);
return v___x_1513_;
}
else
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_dec(v_catName_1499_);
v___x_1514_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__62));
lean_inc(v_k_664_);
v___x_1515_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_664_, v_attrKind_663_, v_attrs_x3f_662_, v___x_1514_, v___y_1500_, v___y_1501_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1517_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v___x_1515_, 1);
v___x_1517_ = l_Lean_Elab_Command_getRef___redArg(v___y_1500_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
v___x_1519_ = l_Lean_SourceInfo_fromRef(v_a_1518_, v___x_1505_);
lean_dec(v_a_1518_);
v___x_1520_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1500_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_quotContext_x3f_1521_; 
v_quotContext_x3f_1521_ = lean_ctor_get(v___y_1500_, 5);
if (lean_obj_tag(v_quotContext_x3f_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1523_; lean_object* v_a_1524_; 
v_a_1522_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1520_, 1);
v___x_1523_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1501_);
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref(v___x_1523_);
v___y_800_ = v___x_1519_;
v___y_801_ = v_a_1516_;
v___y_802_ = v_val_1503_;
v___y_803_ = v___x_1502_;
v___y_804_ = v_a_1522_;
v_a_805_ = v_a_1524_;
goto v___jp_799_;
}
else
{
lean_object* v_a_1525_; lean_object* v_val_1526_; 
v_a_1525_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1520_, 1);
v_val_1526_ = lean_ctor_get(v_quotContext_x3f_1521_, 0);
lean_inc(v_val_1526_);
v___y_800_ = v___x_1519_;
v___y_801_ = v_a_1516_;
v___y_802_ = v_val_1503_;
v___y_803_ = v___x_1502_;
v___y_804_ = v_a_1525_;
v_a_805_ = v_val_1526_;
goto v___jp_799_;
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec(v___x_1519_);
lean_dec(v_a_1516_);
lean_dec(v_val_1503_);
lean_dec(v___x_1502_);
lean_del_object(v___x_676_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1527_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1520_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1520_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
else
{
lean_dec(v_a_1516_);
lean_dec(v_val_1503_);
lean_dec(v___x_1502_);
lean_del_object(v___x_676_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
return v___x_1517_;
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec(v_val_1503_);
lean_dec(v___x_1502_);
lean_del_object(v___x_676_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1535_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1515_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1515_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
else
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_dec(v_catName_1499_);
lean_del_object(v___x_676_);
v___x_1543_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__64));
lean_inc(v_k_664_);
v___x_1544_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_664_, v_attrKind_663_, v_attrs_x3f_662_, v___x_1543_, v___y_1500_, v___y_1501_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1546_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
v___x_1546_ = l_Lean_Elab_Command_getRef___redArg(v___y_1500_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; uint8_t v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1546_, 1);
v___x_1548_ = 0;
v___x_1549_ = l_Lean_SourceInfo_fromRef(v_a_1547_, v___x_1548_);
lean_dec(v_a_1547_);
v___x_1550_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1500_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_quotContext_x3f_1551_; 
v_quotContext_x3f_1551_ = lean_ctor_get(v___y_1500_, 5);
if (lean_obj_tag(v_quotContext_x3f_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1553_; lean_object* v_a_1554_; 
v_a_1552_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1550_, 1);
v___x_1553_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1501_);
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref(v___x_1553_);
v___y_952_ = v_val_1503_;
v___y_953_ = v___x_1502_;
v___y_954_ = v___x_1549_;
v___y_955_ = v_a_1552_;
v___y_956_ = v_a_1545_;
v_a_957_ = v_a_1554_;
goto v___jp_951_;
}
else
{
lean_object* v_a_1555_; lean_object* v_val_1556_; 
v_a_1555_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1550_, 1);
v_val_1556_ = lean_ctor_get(v_quotContext_x3f_1551_, 0);
lean_inc(v_val_1556_);
v___y_952_ = v_val_1503_;
v___y_953_ = v___x_1502_;
v___y_954_ = v___x_1549_;
v___y_955_ = v_a_1555_;
v___y_956_ = v_a_1545_;
v_a_957_ = v_val_1556_;
goto v___jp_951_;
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v___x_1549_);
lean_dec(v_a_1545_);
lean_dec(v_val_1503_);
lean_dec(v___x_1502_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1557_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1550_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1550_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_dec(v_a_1545_);
lean_dec(v_val_1503_);
lean_dec(v___x_1502_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
return v___x_1546_;
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v_val_1503_);
lean_dec(v___x_1502_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1565_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1544_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1544_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
else
{
lean_object* v___x_1573_; uint8_t v___x_1574_; 
lean_del_object(v___x_676_);
lean_dec(v_expty_x3f_666_);
v___x_1573_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v___x_1574_ = lean_name_eq(v_catName_1499_, v___x_1573_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; uint8_t v___x_1576_; 
v___x_1575_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__66));
v___x_1576_ = lean_name_eq(v_catName_1499_, v___x_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1577_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__68));
v___x_1578_ = lean_name_eq(v_catName_1499_, v___x_1577_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1579_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__70));
v___x_1580_ = lean_name_eq(v_catName_1499_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1581_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__56));
v___x_1582_ = lean_name_eq(v_catName_1499_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_dec(v___x_1502_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_attrKind_663_);
lean_dec(v_doc_x3f_661_);
v___x_1583_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__72, &l_Lean_Elab_Command_elabElabRulesAux___closed__72_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__72);
v___x_1584_ = l_Lean_MessageData_ofName(v_catName_1499_);
v___x_1585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v___x_1587_, v___y_1500_, v___y_1501_);
return v___x_1588_;
}
else
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec(v_catName_1499_);
v___x_1589_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__62));
lean_inc(v_k_664_);
v___x_1590_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_664_, v_attrKind_663_, v_attrs_x3f_662_, v___x_1589_, v___y_1500_, v___y_1501_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1592_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v___x_1592_ = l_Lean_Elab_Command_getRef___redArg(v___y_1500_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1592_, 1);
v___x_1594_ = l_Lean_SourceInfo_fromRef(v_a_1593_, v___x_1580_);
lean_dec(v_a_1593_);
v___x_1595_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1500_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_quotContext_x3f_1596_; 
v_quotContext_x3f_1596_ = lean_ctor_get(v___y_1500_, 5);
if (lean_obj_tag(v_quotContext_x3f_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v___x_1598_; lean_object* v_a_1599_; 
v_a_1597_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1597_);
lean_dec_ref_known(v___x_1595_, 1);
v___x_1598_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1501_);
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref(v___x_1598_);
v___y_1237_ = v_a_1597_;
v___y_1238_ = v___x_1594_;
v___y_1239_ = v_a_1591_;
v___y_1240_ = v___x_1502_;
v_a_1241_ = v_a_1599_;
goto v___jp_1236_;
}
else
{
lean_object* v_a_1600_; lean_object* v_val_1601_; 
v_a_1600_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1600_);
lean_dec_ref_known(v___x_1595_, 1);
v_val_1601_ = lean_ctor_get(v_quotContext_x3f_1596_, 0);
lean_inc(v_val_1601_);
v___y_1237_ = v_a_1600_;
v___y_1238_ = v___x_1594_;
v___y_1239_ = v_a_1591_;
v___y_1240_ = v___x_1502_;
v_a_1241_ = v_val_1601_;
goto v___jp_1236_;
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v___x_1594_);
lean_dec(v_a_1591_);
lean_dec(v___x_1502_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1602_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1595_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1595_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
else
{
lean_dec(v_a_1591_);
lean_dec(v___x_1502_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
return v___x_1592_;
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v___x_1502_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1610_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1590_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1590_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
else
{
lean_dec(v_catName_1499_);
v___y_1081_ = v___x_1577_;
v___y_1082_ = v___y_1501_;
v___y_1083_ = v___y_1500_;
v___y_1084_ = v___x_1502_;
v___y_1085_ = v___x_1576_;
goto v___jp_1080_;
}
}
else
{
lean_dec(v_catName_1499_);
v___y_1081_ = v___x_1577_;
v___y_1082_ = v___y_1501_;
v___y_1083_ = v___y_1500_;
v___y_1084_ = v___x_1502_;
v___y_1085_ = v___x_1576_;
goto v___jp_1080_;
}
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_dec(v_catName_1499_);
v___x_1618_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__74));
lean_inc(v_k_664_);
v___x_1619_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_664_, v_attrKind_663_, v_attrs_x3f_662_, v___x_1618_, v___y_1500_, v___y_1501_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1621_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
v___x_1621_ = l_Lean_Elab_Command_getRef___redArg(v___y_1500_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v___x_1623_ = l_Lean_SourceInfo_fromRef(v_a_1622_, v___x_1574_);
lean_dec(v_a_1622_);
v___x_1624_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1500_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_quotContext_x3f_1625_; 
v_quotContext_x3f_1625_ = lean_ctor_get(v___y_1500_, 5);
if (lean_obj_tag(v_quotContext_x3f_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1627_; lean_object* v_a_1628_; 
v_a_1626_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1624_, 1);
v___x_1627_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1501_);
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref(v___x_1627_);
v___y_1351_ = v___x_1623_;
v___y_1352_ = v_a_1620_;
v___y_1353_ = v_a_1626_;
v___y_1354_ = v___x_1502_;
v_a_1355_ = v_a_1628_;
goto v___jp_1350_;
}
else
{
lean_object* v_a_1629_; lean_object* v_val_1630_; 
v_a_1629_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1624_, 1);
v_val_1630_ = lean_ctor_get(v_quotContext_x3f_1625_, 0);
lean_inc(v_val_1630_);
v___y_1351_ = v___x_1623_;
v___y_1352_ = v_a_1620_;
v___y_1353_ = v_a_1629_;
v___y_1354_ = v___x_1502_;
v_a_1355_ = v_val_1630_;
goto v___jp_1350_;
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v___x_1623_);
lean_dec(v_a_1620_);
lean_dec(v___x_1502_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1631_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1624_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1624_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
lean_dec(v_a_1620_);
lean_dec(v___x_1502_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
return v___x_1621_;
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec(v___x_1502_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1639_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1619_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1619_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec(v_catName_1499_);
v___x_1647_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__64));
lean_inc(v_k_664_);
v___x_1648_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_664_, v_attrKind_663_, v_attrs_x3f_662_, v___x_1647_, v___y_1500_, v___y_1501_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1650_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v___x_1650_ = l_Lean_Elab_Command_getRef___redArg(v___y_1500_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; uint8_t v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1652_ = 0;
v___x_1653_ = l_Lean_SourceInfo_fromRef(v_a_1651_, v___x_1652_);
lean_dec(v_a_1651_);
v___x_1654_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1500_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_quotContext_x3f_1655_; 
v_quotContext_x3f_1655_ = lean_ctor_get(v___y_1500_, 5);
if (lean_obj_tag(v_quotContext_x3f_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1657_; lean_object* v_a_1658_; 
v_a_1656_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1654_, 1);
v___x_1657_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1501_);
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref(v___x_1657_);
v___y_1484_ = v___x_1653_;
v___y_1485_ = v_a_1656_;
v___y_1486_ = v___x_1502_;
v___y_1487_ = v_a_1649_;
v_a_1488_ = v_a_1658_;
goto v___jp_1483_;
}
else
{
lean_object* v_a_1659_; lean_object* v_val_1660_; 
v_a_1659_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1654_, 1);
v_val_1660_ = lean_ctor_get(v_quotContext_x3f_1655_, 0);
lean_inc(v_val_1660_);
v___y_1484_ = v___x_1653_;
v___y_1485_ = v_a_1659_;
v___y_1486_ = v___x_1502_;
v___y_1487_ = v_a_1649_;
v_a_1488_ = v_val_1660_;
goto v___jp_1483_;
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v___x_1653_);
lean_dec(v_a_1649_);
lean_dec(v___x_1502_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1661_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1654_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1654_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_dec(v_a_1649_);
lean_dec(v___x_1502_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
return v___x_1650_;
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_dec(v___x_1502_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1669_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1648_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1648_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
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
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec(v_expty_x3f_666_);
lean_dec(v_k_664_);
lean_dec(v_attrKind_663_);
lean_dec(v_doc_x3f_661_);
v_a_1691_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_673_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_673_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object* v_doc_x3f_1699_, lean_object* v_attrs_x3f_1700_, lean_object* v_attrKind_1701_, lean_object* v_k_1702_, lean_object* v_cat_x3f_1703_, lean_object* v_expty_x3f_1704_, lean_object* v_alts_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_Elab_Command_elabElabRulesAux(v_doc_x3f_1699_, v_attrs_x3f_1700_, v_attrKind_1701_, v_k_1702_, v_cat_x3f_1703_, v_expty_x3f_1704_, v_alts_1705_, v_a_1706_, v_a_1707_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_cat_x3f_1703_);
lean_dec(v_attrs_x3f_1700_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(lean_object* v_00_u03b1_1710_, lean_object* v_ref_1711_, lean_object* v_msg_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_1711_, v_msg_1712_, v___y_1713_, v___y_1714_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___boxed(lean_object* v_00_u03b1_1717_, lean_object* v_ref_1718_, lean_object* v_msg_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(v_00_u03b1_1717_, v_ref_1718_, v_msg_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v_ref_1718_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(lean_object* v_msgData_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msgData_1724_, v___y_1726_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___boxed(lean_object* v_msgData_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(v_msgData_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(lean_object* v_00_u03b1_1734_, lean_object* v_msg_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_1735_, v___y_1736_, v___y_1737_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___boxed(lean_object* v_00_u03b1_1740_, lean_object* v_msg_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(v_00_u03b1_1740_, v_msg_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(lean_object* v_msgData_1746_, lean_object* v_macroStack_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_msgData_1746_, v_macroStack_1747_, v___y_1749_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___boxed(lean_object* v_msgData_1752_, lean_object* v_macroStack_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(v_msgData_1752_, v_macroStack_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0(lean_object* v_x_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0___boxed(lean_object* v_x_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_Elab_Command_elabElabRules___lam__0(v_x_1760_);
lean_dec(v_x_1760_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1(lean_object* v___x_1766_, lean_object* v___x_1767_, lean_object* v_attrKind_1768_, lean_object* v_expty_x3f_1769_, lean_object* v___f_1770_, lean_object* v_cat_x3f_1771_, lean_object* v___x_1772_, lean_object* v___x_1773_, lean_object* v_attrs_x3f_1774_, lean_object* v___x_1775_, lean_object* v___x_1776_, lean_object* v___x_1777_, lean_object* v_doc_x3f_1778_, lean_object* v_kind_x3f_1779_, lean_object* v_alts_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_Elab_Command_getRef___redArg(v___y_1781_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1893_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1893_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1893_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___x_1882_; 
v___x_1789_ = 0;
v___x_1790_ = l_Lean_SourceInfo_fromRef(v_a_1785_, v___x_1789_);
lean_dec(v_a_1785_);
v___x_1882_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1781_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_quotContext_x3f_1883_; 
lean_dec_ref_known(v___x_1882_, 1);
v_quotContext_x3f_1883_ = lean_ctor_get(v___y_1781_, 5);
if (lean_obj_tag(v_quotContext_x3f_1883_) == 0)
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1782_);
lean_dec_ref(v___x_1884_);
goto v___jp_1876_;
}
else
{
goto v___jp_1876_;
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v___x_1790_);
lean_del_object(v___x_1787_);
lean_dec(v_kind_x3f_1779_);
lean_dec(v_doc_x3f_1778_);
lean_dec_ref(v___x_1777_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v___x_1775_);
lean_dec_ref(v___x_1772_);
lean_dec(v_cat_x3f_1771_);
lean_dec_ref(v___f_1770_);
lean_dec(v_expty_x3f_1769_);
lean_dec(v_attrKind_1768_);
lean_dec(v___x_1767_);
lean_dec(v___x_1766_);
v_a_1885_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1882_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1882_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
v___jp_1791_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1807_; 
lean_inc_ref_n(v___y_1793_, 2);
v___x_1800_ = l_Array_append___redArg(v___y_1793_, v___y_1799_);
lean_dec_ref(v___y_1799_);
lean_inc_n(v___y_1797_, 2);
lean_inc_n(v___x_1790_, 3);
v___x_1801_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1790_);
lean_ctor_set(v___x_1801_, 1, v___y_1797_);
lean_ctor_set(v___x_1801_, 2, v___x_1800_);
v___x_1802_ = l_Array_append___redArg(v___y_1793_, v_alts_1780_);
v___x_1803_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1790_);
lean_ctor_set(v___x_1803_, 1, v___y_1797_);
lean_ctor_set(v___x_1803_, 2, v___x_1802_);
v___x_1804_ = l_Lean_Syntax_node1(v___x_1790_, v___x_1766_, v___x_1803_);
v___x_1805_ = l_Lean_Syntax_node8(v___x_1790_, v___x_1767_, v___y_1795_, v___y_1794_, v_attrKind_1768_, v___y_1796_, v___y_1798_, v___y_1792_, v___x_1801_, v___x_1804_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1805_);
v___x_1807_ = v___x_1787_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
v___jp_1809_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_inc_ref(v___y_1810_);
v___x_1817_ = l_Array_append___redArg(v___y_1810_, v___y_1816_);
lean_dec_ref(v___y_1816_);
lean_inc(v___y_1814_);
lean_inc(v___x_1790_);
v___x_1818_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1790_);
lean_ctor_set(v___x_1818_, 1, v___y_1814_);
lean_ctor_set(v___x_1818_, 2, v___x_1817_);
if (lean_obj_tag(v_expty_x3f_1769_) == 1)
{
lean_object* v_val_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_dec_ref(v___f_1770_);
v_val_1819_ = lean_ctor_get(v_expty_x3f_1769_, 0);
lean_inc(v_val_1819_);
lean_dec_ref_known(v_expty_x3f_1769_, 1);
v___x_1820_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___x_1790_);
v___x_1821_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1790_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = l_Array_mkArray2___redArg(v___x_1821_, v_val_1819_);
v___y_1792_ = v___x_1818_;
v___y_1793_ = v___y_1810_;
v___y_1794_ = v___y_1811_;
v___y_1795_ = v___y_1812_;
v___y_1796_ = v___y_1813_;
v___y_1797_ = v___y_1814_;
v___y_1798_ = v___y_1815_;
v___y_1799_ = v___x_1822_;
goto v___jp_1791_;
}
else
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_apply_1(v___f_1770_, v_expty_x3f_1769_);
v___y_1792_ = v___x_1818_;
v___y_1793_ = v___y_1810_;
v___y_1794_ = v___y_1811_;
v___y_1795_ = v___y_1812_;
v___y_1796_ = v___y_1813_;
v___y_1797_ = v___y_1814_;
v___y_1798_ = v___y_1815_;
v___y_1799_ = v___x_1823_;
goto v___jp_1791_;
}
}
v___jp_1824_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_inc_ref(v___y_1825_);
v___x_1831_ = l_Array_append___redArg(v___y_1825_, v___y_1830_);
lean_dec_ref(v___y_1830_);
lean_inc(v___y_1829_);
lean_inc(v___x_1790_);
v___x_1832_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1790_);
lean_ctor_set(v___x_1832_, 1, v___y_1829_);
lean_ctor_set(v___x_1832_, 2, v___x_1831_);
if (lean_obj_tag(v_cat_x3f_1771_) == 1)
{
lean_object* v_val_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v_val_1833_ = lean_ctor_get(v_cat_x3f_1771_, 0);
lean_inc(v_val_1833_);
lean_dec_ref_known(v_cat_x3f_1771_, 1);
v___x_1834_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(v___x_1790_);
v___x_1835_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1790_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = l_Array_mkArray2___redArg(v___x_1835_, v_val_1833_);
v___y_1810_ = v___y_1825_;
v___y_1811_ = v___y_1826_;
v___y_1812_ = v___y_1827_;
v___y_1813_ = v___y_1828_;
v___y_1814_ = v___y_1829_;
v___y_1815_ = v___x_1832_;
v___y_1816_ = v___x_1836_;
goto v___jp_1809_;
}
else
{
lean_object* v___x_1837_; 
lean_inc_ref(v___f_1770_);
v___x_1837_ = lean_apply_1(v___f_1770_, v_cat_x3f_1771_);
v___y_1810_ = v___y_1825_;
v___y_1811_ = v___y_1826_;
v___y_1812_ = v___y_1827_;
v___y_1813_ = v___y_1828_;
v___y_1814_ = v___y_1829_;
v___y_1815_ = v___x_1832_;
v___y_1816_ = v___x_1837_;
goto v___jp_1809_;
}
}
v___jp_1838_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_inc_ref(v___y_1839_);
v___x_1843_ = l_Array_append___redArg(v___y_1839_, v___y_1842_);
lean_dec_ref(v___y_1842_);
lean_inc(v___y_1841_);
lean_inc_n(v___x_1790_, 2);
v___x_1844_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1790_);
lean_ctor_set(v___x_1844_, 1, v___y_1841_);
lean_ctor_set(v___x_1844_, 2, v___x_1843_);
v___x_1845_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1790_);
lean_ctor_set(v___x_1845_, 1, v___x_1772_);
if (lean_obj_tag(v_kind_x3f_1779_) == 0)
{
lean_object* v___x_1846_; 
v___x_1846_ = lean_mk_empty_array_with_capacity(v___x_1773_);
v___y_1825_ = v___y_1839_;
v___y_1826_ = v___x_1844_;
v___y_1827_ = v___y_1840_;
v___y_1828_ = v___x_1845_;
v___y_1829_ = v___y_1841_;
v___y_1830_ = v___x_1846_;
goto v___jp_1824_;
}
else
{
lean_object* v_val_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v_val_1847_ = lean_ctor_get(v_kind_x3f_1779_, 0);
lean_inc(v_val_1847_);
lean_dec_ref_known(v_kind_x3f_1779_, 1);
v___x_1848_ = l_Lean_mkIdent(v_val_1847_);
v___x_1849_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc_n(v___x_1790_, 4);
v___x_1850_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1790_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__2));
v___x_1852_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1790_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1790_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_1856_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1790_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = l_Array_mkArray5___redArg(v___x_1850_, v___x_1852_, v___x_1854_, v___x_1848_, v___x_1856_);
v___y_1825_ = v___y_1839_;
v___y_1826_ = v___x_1844_;
v___y_1827_ = v___y_1840_;
v___y_1828_ = v___x_1845_;
v___y_1829_ = v___y_1841_;
v___y_1830_ = v___x_1857_;
goto v___jp_1824_;
}
}
v___jp_1858_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_inc_ref(v___y_1859_);
v___x_1862_ = l_Array_append___redArg(v___y_1859_, v___y_1861_);
lean_dec_ref(v___y_1861_);
lean_inc(v___y_1860_);
lean_inc(v___x_1790_);
v___x_1863_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1790_);
lean_ctor_set(v___x_1863_, 1, v___y_1860_);
lean_ctor_set(v___x_1863_, 2, v___x_1862_);
if (lean_obj_tag(v_attrs_x3f_1774_) == 1)
{
lean_object* v_val_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v_val_1864_ = lean_ctor_get(v_attrs_x3f_1774_, 0);
v___x_1865_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
v___x_1866_ = l_Lean_Name_mkStr4(v___x_1775_, v___x_1776_, v___x_1777_, v___x_1865_);
v___x_1867_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc_n(v___x_1790_, 4);
v___x_1868_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1790_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
lean_inc_ref(v___y_1859_);
v___x_1869_ = l_Array_append___redArg(v___y_1859_, v_val_1864_);
lean_inc(v___y_1860_);
v___x_1870_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1790_);
lean_ctor_set(v___x_1870_, 1, v___y_1860_);
lean_ctor_set(v___x_1870_, 2, v___x_1869_);
v___x_1871_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1872_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1790_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = l_Lean_Syntax_node3(v___x_1790_, v___x_1866_, v___x_1868_, v___x_1870_, v___x_1872_);
v___x_1874_ = l_Array_mkArray1___redArg(v___x_1873_);
v___y_1839_ = v___y_1859_;
v___y_1840_ = v___x_1863_;
v___y_1841_ = v___y_1860_;
v___y_1842_ = v___x_1874_;
goto v___jp_1838_;
}
else
{
lean_object* v___x_1875_; 
lean_dec_ref(v___x_1777_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v___x_1775_);
v___x_1875_ = lean_mk_empty_array_with_capacity(v___x_1773_);
v___y_1839_ = v___y_1859_;
v___y_1840_ = v___x_1863_;
v___y_1841_ = v___y_1860_;
v___y_1842_ = v___x_1875_;
goto v___jp_1838_;
}
}
v___jp_1876_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1878_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_1778_) == 1)
{
lean_object* v_val_1879_; lean_object* v___x_1880_; 
v_val_1879_ = lean_ctor_get(v_doc_x3f_1778_, 0);
lean_inc(v_val_1879_);
lean_dec_ref_known(v_doc_x3f_1778_, 1);
v___x_1880_ = l_Array_mkArray1___redArg(v_val_1879_);
v___y_1859_ = v___x_1878_;
v___y_1860_ = v___x_1877_;
v___y_1861_ = v___x_1880_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1881_; 
lean_dec(v_doc_x3f_1778_);
v___x_1881_ = lean_mk_empty_array_with_capacity(v___x_1773_);
v___y_1859_ = v___x_1878_;
v___y_1860_ = v___x_1877_;
v___y_1861_ = v___x_1881_;
goto v___jp_1858_;
}
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec(v_kind_x3f_1779_);
lean_dec(v_doc_x3f_1778_);
lean_dec_ref(v___x_1777_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v___x_1775_);
lean_dec_ref(v___x_1772_);
lean_dec(v_cat_x3f_1771_);
lean_dec_ref(v___f_1770_);
lean_dec(v_expty_x3f_1769_);
lean_dec(v_attrKind_1768_);
lean_dec(v___x_1767_);
lean_dec(v___x_1766_);
v_a_1894_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1784_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1784_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___boxed(lean_object** _args){
lean_object* v___x_1902_ = _args[0];
lean_object* v___x_1903_ = _args[1];
lean_object* v_attrKind_1904_ = _args[2];
lean_object* v_expty_x3f_1905_ = _args[3];
lean_object* v___f_1906_ = _args[4];
lean_object* v_cat_x3f_1907_ = _args[5];
lean_object* v___x_1908_ = _args[6];
lean_object* v___x_1909_ = _args[7];
lean_object* v_attrs_x3f_1910_ = _args[8];
lean_object* v___x_1911_ = _args[9];
lean_object* v___x_1912_ = _args[10];
lean_object* v___x_1913_ = _args[11];
lean_object* v_doc_x3f_1914_ = _args[12];
lean_object* v_kind_x3f_1915_ = _args[13];
lean_object* v_alts_1916_ = _args[14];
lean_object* v___y_1917_ = _args[15];
lean_object* v___y_1918_ = _args[16];
lean_object* v___y_1919_ = _args[17];
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_Elab_Command_elabElabRules___lam__1(v___x_1902_, v___x_1903_, v_attrKind_1904_, v_expty_x3f_1905_, v___f_1906_, v_cat_x3f_1907_, v___x_1908_, v___x_1909_, v_attrs_x3f_1910_, v___x_1911_, v___x_1912_, v___x_1913_, v_doc_x3f_1914_, v_kind_x3f_1915_, v_alts_1916_, v___y_1917_, v___y_1918_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec_ref(v_alts_1916_);
lean_dec(v_attrs_x3f_1910_);
lean_dec(v___x_1909_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2(lean_object* v___f_1949_, lean_object* v_stx_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v___x_1954_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1955_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1956_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
v___x_1957_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
lean_inc(v_stx_1950_);
v___x_1958_ = l_Lean_Syntax_isOfKind(v_stx_1950_, v___x_1957_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; 
lean_dec(v_stx_1950_);
lean_dec_ref(v___f_1949_);
v___x_1959_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_1959_;
}
else
{
lean_object* v___x_1960_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v_expty_x3f_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v_cat_x3f_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v_expty_x3f_2017_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v_cat_x3f_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v_attrs_x3f_2066_; lean_object* v_doc_x3f_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___x_2113_; uint8_t v___x_2114_; 
v___x_1960_ = lean_unsigned_to_nat(0u);
v___x_2113_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_1960_);
v___x_2114_ = l_Lean_Syntax_isNone(v___x_2113_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2115_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2113_);
v___x_2116_ = l_Lean_Syntax_matchesNull(v___x_2113_, v___x_2115_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; 
lean_dec(v___x_2113_);
lean_dec(v_stx_1950_);
lean_dec_ref(v___f_1949_);
v___x_2117_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2117_;
}
else
{
lean_object* v_doc_x3f_2118_; 
v_doc_x3f_2118_ = l_Lean_Syntax_getArg(v___x_2113_, v___x_1960_);
lean_dec(v___x_2113_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2121_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7));
lean_inc(v_doc_x3f_2118_);
v___x_2122_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2118_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; 
lean_dec(v_doc_x3f_2118_);
lean_dec(v_stx_1950_);
lean_dec_ref(v___f_1949_);
v___x_2123_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2123_;
}
else
{
goto v___jp_2119_;
}
}
else
{
goto v___jp_2119_;
}
v___jp_2119_:
{
lean_object* v___x_2120_; 
v___x_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2120_, 0, v_doc_x3f_2118_);
v_doc_x3f_2097_ = v___x_2120_;
v___y_2098_ = v___y_1951_;
v___y_2099_ = v___y_1952_;
goto v___jp_2096_;
}
}
}
else
{
lean_object* v___x_2124_; 
lean_dec(v___x_2113_);
v___x_2124_ = lean_box(0);
v_doc_x3f_2097_ = v___x_2124_;
v___y_2098_ = v___y_1951_;
v___y_2099_ = v___y_1952_;
goto v___jp_2096_;
}
v___jp_1961_:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v___x_1971_ = lean_unsigned_to_nat(7u);
v___x_1972_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_1971_);
lean_dec(v_stx_1950_);
v___x_1973_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc_ref(v___y_1967_);
v___x_1974_ = l_Lean_Name_mkStr4(v___x_1954_, v___x_1955_, v___y_1967_, v___x_1973_);
lean_inc(v___x_1972_);
v___x_1975_ = l_Lean_Syntax_isOfKind(v___x_1972_, v___x_1974_);
lean_dec(v___x_1974_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; 
lean_dec(v___x_1972_);
lean_dec(v_expty_x3f_1968_);
lean_dec(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec(v___y_1962_);
v___x_1976_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_1976_;
}
else
{
lean_object* v___x_1977_; lean_object* v_alts_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1977_ = l_Lean_Syntax_getArg(v___x_1972_, v___x_1960_);
lean_dec(v___x_1972_);
v_alts_1978_ = l_Lean_Syntax_getArgs(v___x_1977_);
lean_dec(v___x_1977_);
v___x_1979_ = l_Lean_TSyntax_getId(v___y_1963_);
lean_dec(v___y_1963_);
v___x_1980_ = l_Lean_Elab_Command_resolveSyntaxKind(v___x_1979_, v___y_1969_, v___y_1970_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1982_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___x_1980_, 1);
v___x_1982_ = l_Lean_Elab_Command_elabElabRulesAux(v___y_1965_, v___y_1964_, v___y_1962_, v_a_1981_, v___y_1966_, v_expty_x3f_1968_, v_alts_1978_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1966_);
lean_dec(v___y_1964_);
return v___x_1982_;
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec_ref(v_alts_1978_);
lean_dec(v_expty_x3f_1968_);
lean_dec(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec(v___y_1962_);
v_a_1983_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1980_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1980_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
v___jp_1991_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; 
v___x_2002_ = lean_unsigned_to_nat(6u);
v___x_2003_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_2002_);
v___x_2004_ = l_Lean_Syntax_isNone(v___x_2003_);
if (v___x_2004_ == 0)
{
uint8_t v___x_2005_; 
lean_inc(v___x_2003_);
v___x_2005_ = l_Lean_Syntax_matchesNull(v___x_2003_, v___y_1994_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
lean_dec(v___x_2003_);
lean_dec(v_cat_x3f_1999_);
lean_dec(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec(v___y_1993_);
lean_dec(v_stx_1950_);
v___x_2006_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2006_;
}
else
{
lean_object* v_expty_x3f_2007_; lean_object* v___x_2008_; 
v_expty_x3f_2007_ = l_Lean_Syntax_getArg(v___x_2003_, v___y_1992_);
lean_dec(v___x_2003_);
v___x_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2008_, 0, v_expty_x3f_2007_);
v___y_1962_ = v___y_1993_;
v___y_1963_ = v___y_1995_;
v___y_1964_ = v___y_1997_;
v___y_1965_ = v___y_1996_;
v___y_1966_ = v_cat_x3f_1999_;
v___y_1967_ = v___y_1998_;
v_expty_x3f_1968_ = v___x_2008_;
v___y_1969_ = v___y_2000_;
v___y_1970_ = v___y_2001_;
goto v___jp_1961_;
}
}
else
{
lean_object* v___x_2009_; 
lean_dec(v___x_2003_);
v___x_2009_ = lean_box(0);
v___y_1962_ = v___y_1993_;
v___y_1963_ = v___y_1995_;
v___y_1964_ = v___y_1997_;
v___y_1965_ = v___y_1996_;
v___y_1966_ = v_cat_x3f_1999_;
v___y_1967_ = v___y_1998_;
v_expty_x3f_1968_ = v___x_2009_;
v___y_1969_ = v___y_2000_;
v___y_1970_ = v___y_2001_;
goto v___jp_1961_;
}
}
v___jp_2010_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2018_ = lean_unsigned_to_nat(7u);
v___x_2019_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_2018_);
lean_dec(v_stx_1950_);
v___x_2020_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_2021_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__2));
lean_inc(v___x_2019_);
v___x_2022_ = l_Lean_Syntax_isOfKind(v___x_2019_, v___x_2021_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; 
lean_dec(v___x_2019_);
lean_dec(v_expty_x3f_2017_);
lean_dec(v___y_2016_);
lean_dec(v___y_2014_);
lean_dec(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___f_1949_);
v___x_2023_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2023_;
}
else
{
lean_object* v___f_2024_; lean_object* v___x_2025_; lean_object* v_alts_2026_; lean_object* v___x_2027_; 
v___f_2024_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___lam__1___boxed), 18, 13);
lean_closure_set(v___f_2024_, 0, v___x_2021_);
lean_closure_set(v___f_2024_, 1, v___x_1957_);
lean_closure_set(v___f_2024_, 2, v___y_2016_);
lean_closure_set(v___f_2024_, 3, v_expty_x3f_2017_);
lean_closure_set(v___f_2024_, 4, v___f_1949_);
lean_closure_set(v___f_2024_, 5, v___y_2014_);
lean_closure_set(v___f_2024_, 6, v___x_1956_);
lean_closure_set(v___f_2024_, 7, v___x_1960_);
lean_closure_set(v___f_2024_, 8, v___y_2011_);
lean_closure_set(v___f_2024_, 9, v___x_1954_);
lean_closure_set(v___f_2024_, 10, v___x_1955_);
lean_closure_set(v___f_2024_, 11, v___x_2020_);
lean_closure_set(v___f_2024_, 12, v___y_2012_);
v___x_2025_ = l_Lean_Syntax_getArg(v___x_2019_, v___x_1960_);
lean_dec(v___x_2019_);
v_alts_2026_ = l_Lean_Syntax_getArgs(v___x_2025_);
lean_dec(v___x_2025_);
v___x_2027_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(v_alts_2026_, v___x_1956_, v___f_2024_, v___y_2013_, v___y_2015_);
lean_dec_ref(v_alts_2026_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
v_a_2036_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2027_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2027_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
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
}
v___jp_2044_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2053_ = lean_unsigned_to_nat(6u);
v___x_2054_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_2053_);
v___x_2055_ = l_Lean_Syntax_isNone(v___x_2054_);
if (v___x_2055_ == 0)
{
uint8_t v___x_2056_; 
lean_inc(v___x_2054_);
v___x_2056_ = l_Lean_Syntax_matchesNull(v___x_2054_, v___y_2049_);
if (v___x_2056_ == 0)
{
lean_object* v___x_2057_; 
lean_dec(v___x_2054_);
lean_dec(v_cat_x3f_2050_);
lean_dec(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec(v_stx_1950_);
lean_dec_ref(v___f_1949_);
v___x_2057_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2057_;
}
else
{
lean_object* v_expty_x3f_2058_; lean_object* v___x_2059_; 
v_expty_x3f_2058_ = l_Lean_Syntax_getArg(v___x_2054_, v___y_2048_);
lean_dec(v___x_2054_);
v___x_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2059_, 0, v_expty_x3f_2058_);
v___y_2011_ = v___y_2045_;
v___y_2012_ = v___y_2046_;
v___y_2013_ = v___y_2051_;
v___y_2014_ = v_cat_x3f_2050_;
v___y_2015_ = v___y_2052_;
v___y_2016_ = v___y_2047_;
v_expty_x3f_2017_ = v___x_2059_;
goto v___jp_2010_;
}
}
else
{
lean_object* v___x_2060_; 
lean_dec(v___x_2054_);
v___x_2060_ = lean_box(0);
v___y_2011_ = v___y_2045_;
v___y_2012_ = v___y_2046_;
v___y_2013_ = v___y_2051_;
v___y_2014_ = v_cat_x3f_2050_;
v___y_2015_ = v___y_2052_;
v___y_2016_ = v___y_2047_;
v_expty_x3f_2017_ = v___x_2060_;
goto v___jp_2010_;
}
}
v___jp_2061_:
{
lean_object* v___x_2067_; lean_object* v_attrKind_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_2067_ = lean_unsigned_to_nat(2u);
v_attrKind_2068_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_2067_);
v___x_2069_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_2070_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v_attrKind_2068_);
v___x_2071_ = l_Lean_Syntax_isOfKind(v_attrKind_2068_, v___x_2070_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; 
lean_dec(v_attrKind_2068_);
lean_dec(v_attrs_x3f_2066_);
lean_dec(v___y_2063_);
lean_dec(v_stx_1950_);
lean_dec_ref(v___f_1949_);
v___x_2072_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2072_;
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2073_ = lean_unsigned_to_nat(4u);
v___x_2074_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_2073_);
lean_inc(v___x_2074_);
v___x_2075_ = l_Lean_Syntax_matchesNull(v___x_2074_, v___x_1960_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; uint8_t v___x_2077_; 
lean_dec_ref(v___f_1949_);
v___x_2076_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2074_);
v___x_2077_ = l_Lean_Syntax_matchesNull(v___x_2074_, v___x_2076_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; 
lean_dec(v___x_2074_);
lean_dec(v_attrKind_2068_);
lean_dec(v_attrs_x3f_2066_);
lean_dec(v___y_2063_);
lean_dec(v_stx_1950_);
v___x_2078_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2078_;
}
else
{
lean_object* v___x_2079_; lean_object* v_kind_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v___x_2079_ = lean_unsigned_to_nat(3u);
v_kind_2080_ = l_Lean_Syntax_getArg(v___x_2074_, v___x_2079_);
lean_dec(v___x_2074_);
v___x_2081_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_2076_);
v___x_2082_ = l_Lean_Syntax_isNone(v___x_2081_);
if (v___x_2082_ == 0)
{
uint8_t v___x_2083_; 
lean_inc(v___x_2081_);
v___x_2083_ = l_Lean_Syntax_matchesNull(v___x_2081_, v___x_2067_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; 
lean_dec(v___x_2081_);
lean_dec(v_kind_2080_);
lean_dec(v_attrKind_2068_);
lean_dec(v_attrs_x3f_2066_);
lean_dec(v___y_2063_);
lean_dec(v_stx_1950_);
v___x_2084_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2084_;
}
else
{
lean_object* v_cat_x3f_2085_; lean_object* v___x_2086_; 
v_cat_x3f_2085_ = l_Lean_Syntax_getArg(v___x_2081_, v___y_2065_);
lean_dec(v___x_2081_);
v___x_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2086_, 0, v_cat_x3f_2085_);
v___y_1992_ = v___y_2065_;
v___y_1993_ = v_attrKind_2068_;
v___y_1994_ = v___x_2067_;
v___y_1995_ = v_kind_2080_;
v___y_1996_ = v___y_2063_;
v___y_1997_ = v_attrs_x3f_2066_;
v___y_1998_ = v___x_2069_;
v_cat_x3f_1999_ = v___x_2086_;
v___y_2000_ = v___y_2064_;
v___y_2001_ = v___y_2062_;
goto v___jp_1991_;
}
}
else
{
lean_object* v___x_2087_; 
lean_dec(v___x_2081_);
v___x_2087_ = lean_box(0);
v___y_1992_ = v___y_2065_;
v___y_1993_ = v_attrKind_2068_;
v___y_1994_ = v___x_2067_;
v___y_1995_ = v_kind_2080_;
v___y_1996_ = v___y_2063_;
v___y_1997_ = v_attrs_x3f_2066_;
v___y_1998_ = v___x_2069_;
v_cat_x3f_1999_ = v___x_2087_;
v___y_2000_ = v___y_2064_;
v___y_2001_ = v___y_2062_;
goto v___jp_1991_;
}
}
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
lean_dec(v___x_2074_);
v___x_2088_ = lean_unsigned_to_nat(5u);
v___x_2089_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_2088_);
v___x_2090_ = l_Lean_Syntax_isNone(v___x_2089_);
if (v___x_2090_ == 0)
{
uint8_t v___x_2091_; 
lean_inc(v___x_2089_);
v___x_2091_ = l_Lean_Syntax_matchesNull(v___x_2089_, v___x_2067_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; 
lean_dec(v___x_2089_);
lean_dec(v_attrKind_2068_);
lean_dec(v_attrs_x3f_2066_);
lean_dec(v___y_2063_);
lean_dec(v_stx_1950_);
lean_dec_ref(v___f_1949_);
v___x_2092_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2092_;
}
else
{
lean_object* v_cat_x3f_2093_; lean_object* v___x_2094_; 
v_cat_x3f_2093_ = l_Lean_Syntax_getArg(v___x_2089_, v___y_2065_);
lean_dec(v___x_2089_);
v___x_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2094_, 0, v_cat_x3f_2093_);
v___y_2045_ = v_attrs_x3f_2066_;
v___y_2046_ = v___y_2063_;
v___y_2047_ = v_attrKind_2068_;
v___y_2048_ = v___y_2065_;
v___y_2049_ = v___x_2067_;
v_cat_x3f_2050_ = v___x_2094_;
v___y_2051_ = v___y_2064_;
v___y_2052_ = v___y_2062_;
goto v___jp_2044_;
}
}
else
{
lean_object* v___x_2095_; 
lean_dec(v___x_2089_);
v___x_2095_ = lean_box(0);
v___y_2045_ = v_attrs_x3f_2066_;
v___y_2046_ = v___y_2063_;
v___y_2047_ = v_attrKind_2068_;
v___y_2048_ = v___y_2065_;
v___y_2049_ = v___x_2067_;
v_cat_x3f_2050_ = v___x_2095_;
v___y_2051_ = v___y_2064_;
v___y_2052_ = v___y_2062_;
goto v___jp_2044_;
}
}
}
}
v___jp_2096_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2100_ = lean_unsigned_to_nat(1u);
v___x_2101_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_2100_);
v___x_2102_ = l_Lean_Syntax_isNone(v___x_2101_);
if (v___x_2102_ == 0)
{
uint8_t v___x_2103_; 
lean_inc(v___x_2101_);
v___x_2103_ = l_Lean_Syntax_matchesNull(v___x_2101_, v___x_2100_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; 
lean_dec(v___x_2101_);
lean_dec(v_doc_x3f_2097_);
lean_dec(v_stx_1950_);
lean_dec_ref(v___f_1949_);
v___x_2104_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2104_;
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v___x_2105_ = l_Lean_Syntax_getArg(v___x_2101_, v___x_1960_);
lean_dec(v___x_2101_);
v___x_2106_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5));
lean_inc(v___x_2105_);
v___x_2107_ = l_Lean_Syntax_isOfKind(v___x_2105_, v___x_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; 
lean_dec(v___x_2105_);
lean_dec(v_doc_x3f_2097_);
lean_dec(v_stx_1950_);
lean_dec_ref(v___f_1949_);
v___x_2108_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2108_;
}
else
{
lean_object* v___x_2109_; lean_object* v_attrs_x3f_2110_; lean_object* v___x_2111_; 
v___x_2109_ = l_Lean_Syntax_getArg(v___x_2105_, v___x_2100_);
lean_dec(v___x_2105_);
v_attrs_x3f_2110_ = l_Lean_Syntax_getArgs(v___x_2109_);
lean_dec(v___x_2109_);
v___x_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2111_, 0, v_attrs_x3f_2110_);
v___y_2062_ = v___y_2099_;
v___y_2063_ = v_doc_x3f_2097_;
v___y_2064_ = v___y_2098_;
v___y_2065_ = v___x_2100_;
v_attrs_x3f_2066_ = v___x_2111_;
goto v___jp_2061_;
}
}
}
else
{
lean_object* v___x_2112_; 
lean_dec(v___x_2101_);
v___x_2112_ = lean_box(0);
v___y_2062_ = v___y_2099_;
v___y_2063_ = v_doc_x3f_2097_;
v___y_2064_ = v___y_2098_;
v___y_2065_ = v___x_2100_;
v_attrs_x3f_2066_ = v___x_2112_;
goto v___jp_2061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___boxed(lean_object* v___f_2125_, lean_object* v_stx_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_Elab_Command_elabElabRules___lam__2(v___f_2125_, v_stx_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_){
_start:
{
lean_object* v___f_2138_; lean_object* v___x_2139_; 
v___f_2138_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___closed__1));
v___x_2139_ = l_Lean_Elab_Command_adaptExpander(v___f_2138_, v_a_2134_, v_a_2135_, v_a_2136_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___boxed(lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_Elab_Command_elabElabRules(v_a_2140_, v_a_2141_, v_a_2142_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1(){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2152_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2153_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
v___x_2154_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2155_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___boxed), 4, 0);
v___x_2156_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2152_, v___x_2153_, v___x_2154_, v___x_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___boxed(lean_object* v_a_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3(){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2186_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6));
v___x_2187_ = l_Lean_addBuiltinDeclarationRanges(v___x_2185_, v___x_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___boxed(lean_object* v_a_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(size_t v_sz_2190_, size_t v_i_2191_, lean_object* v_bs_2192_){
_start:
{
uint8_t v___x_2193_; 
v___x_2193_ = lean_usize_dec_lt(v_i_2191_, v_sz_2190_);
if (v___x_2193_ == 0)
{
return v_bs_2192_;
}
else
{
lean_object* v_v_2194_; lean_object* v___x_2195_; lean_object* v_bs_x27_2196_; size_t v___x_2197_; size_t v___x_2198_; lean_object* v___x_2199_; 
v_v_2194_ = lean_array_uget(v_bs_2192_, v_i_2191_);
v___x_2195_ = lean_unsigned_to_nat(0u);
v_bs_x27_2196_ = lean_array_uset(v_bs_2192_, v_i_2191_, v___x_2195_);
v___x_2197_ = ((size_t)1ULL);
v___x_2198_ = lean_usize_add(v_i_2191_, v___x_2197_);
v___x_2199_ = lean_array_uset(v_bs_x27_2196_, v_i_2191_, v_v_2194_);
v_i_2191_ = v___x_2198_;
v_bs_2192_ = v___x_2199_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2___boxed(lean_object* v_sz_2201_, lean_object* v_i_2202_, lean_object* v_bs_2203_){
_start:
{
size_t v_sz_boxed_2204_; size_t v_i_boxed_2205_; lean_object* v_res_2206_; 
v_sz_boxed_2204_ = lean_unbox_usize(v_sz_2201_);
lean_dec(v_sz_2201_);
v_i_boxed_2205_ = lean_unbox_usize(v_i_2202_);
lean_dec(v_i_2202_);
v_res_2206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_boxed_2204_, v_i_boxed_2205_, v_bs_2203_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(size_t v_sz_2207_, size_t v_i_2208_, lean_object* v_bs_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
uint8_t v___x_2213_; 
v___x_2213_ = lean_usize_dec_lt(v_i_2208_, v_sz_2207_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; 
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v_bs_2209_);
return v___x_2214_;
}
else
{
lean_object* v_v_2215_; lean_object* v___x_2216_; lean_object* v_bs_x27_2217_; lean_object* v___x_2218_; 
v_v_2215_ = lean_array_uget(v_bs_2209_, v_i_2208_);
v___x_2216_ = lean_unsigned_to_nat(0u);
v_bs_x27_2217_ = lean_array_uset(v_bs_2209_, v_i_2208_, v___x_2216_);
v___x_2218_ = l_Lean_Elab_Command_expandMacroArg(v_v_2215_, v___y_2210_, v___y_2211_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; size_t v___x_2220_; size_t v___x_2221_; lean_object* v___x_2222_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v___x_2218_, 1);
v___x_2220_ = ((size_t)1ULL);
v___x_2221_ = lean_usize_add(v_i_2208_, v___x_2220_);
v___x_2222_ = lean_array_uset(v_bs_x27_2217_, v_i_2208_, v_a_2219_);
v_i_2208_ = v___x_2221_;
v_bs_2209_ = v___x_2222_;
goto _start;
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec_ref(v_bs_x27_2217_);
v_a_2224_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2218_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2218_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1___boxed(lean_object* v_sz_2232_, lean_object* v_i_2233_, lean_object* v_bs_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
size_t v_sz_boxed_2238_; size_t v_i_boxed_2239_; lean_object* v_res_2240_; 
v_sz_boxed_2238_ = lean_unbox_usize(v_sz_2232_);
lean_dec(v_sz_2232_);
v_i_boxed_2239_ = lean_unbox_usize(v_i_2233_);
lean_dec(v_i_2233_);
v_res_2240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_boxed_2238_, v_i_boxed_2239_, v_bs_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
return v_res_2240_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(lean_object* v_keys_2241_, lean_object* v_i_2242_, lean_object* v_k_2243_){
_start:
{
lean_object* v___x_2244_; uint8_t v___x_2245_; 
v___x_2244_ = lean_array_get_size(v_keys_2241_);
v___x_2245_ = lean_nat_dec_lt(v_i_2242_, v___x_2244_);
if (v___x_2245_ == 0)
{
lean_dec(v_i_2242_);
return v___x_2245_;
}
else
{
lean_object* v_k_x27_2246_; uint8_t v___x_2247_; 
v_k_x27_2246_ = lean_array_fget_borrowed(v_keys_2241_, v_i_2242_);
v___x_2247_ = l_Lean_instBEqExtraModUse_beq(v_k_2243_, v_k_x27_2246_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = lean_unsigned_to_nat(1u);
v___x_2249_ = lean_nat_add(v_i_2242_, v___x_2248_);
lean_dec(v_i_2242_);
v_i_2242_ = v___x_2249_;
goto _start;
}
else
{
lean_dec(v_i_2242_);
return v___x_2245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_keys_2251_, lean_object* v_i_2252_, lean_object* v_k_2253_){
_start:
{
uint8_t v_res_2254_; lean_object* v_r_2255_; 
v_res_2254_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_2251_, v_i_2252_, v_k_2253_);
lean_dec_ref(v_k_2253_);
lean_dec_ref(v_keys_2251_);
v_r_2255_ = lean_box(v_res_2254_);
return v_r_2255_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(lean_object* v_x_2256_, size_t v_x_2257_, lean_object* v_x_2258_){
_start:
{
if (lean_obj_tag(v_x_2256_) == 0)
{
lean_object* v_es_2259_; lean_object* v___x_2260_; size_t v___x_2261_; size_t v___x_2262_; lean_object* v_j_2263_; lean_object* v___x_2264_; 
v_es_2259_ = lean_ctor_get(v_x_2256_, 0);
v___x_2260_ = lean_box(2);
v___x_2261_ = ((size_t)31ULL);
v___x_2262_ = lean_usize_land(v_x_2257_, v___x_2261_);
v_j_2263_ = lean_usize_to_nat(v___x_2262_);
v___x_2264_ = lean_array_get_borrowed(v___x_2260_, v_es_2259_, v_j_2263_);
lean_dec(v_j_2263_);
switch(lean_obj_tag(v___x_2264_))
{
case 0:
{
lean_object* v_key_2265_; uint8_t v___x_2266_; 
v_key_2265_ = lean_ctor_get(v___x_2264_, 0);
v___x_2266_ = l_Lean_instBEqExtraModUse_beq(v_x_2258_, v_key_2265_);
return v___x_2266_;
}
case 1:
{
lean_object* v_node_2267_; size_t v___x_2268_; size_t v___x_2269_; 
v_node_2267_ = lean_ctor_get(v___x_2264_, 0);
v___x_2268_ = ((size_t)5ULL);
v___x_2269_ = lean_usize_shift_right(v_x_2257_, v___x_2268_);
v_x_2256_ = v_node_2267_;
v_x_2257_ = v___x_2269_;
goto _start;
}
default: 
{
uint8_t v___x_2271_; 
v___x_2271_ = 0;
return v___x_2271_;
}
}
}
else
{
lean_object* v_ks_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v_ks_2272_ = lean_ctor_get(v_x_2256_, 0);
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_ks_2272_, v___x_2273_, v_x_2258_);
return v___x_2274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_x_2275_, lean_object* v_x_2276_, lean_object* v_x_2277_){
_start:
{
size_t v_x_16583__boxed_2278_; uint8_t v_res_2279_; lean_object* v_r_2280_; 
v_x_16583__boxed_2278_ = lean_unbox_usize(v_x_2276_);
lean_dec(v_x_2276_);
v_res_2279_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2275_, v_x_16583__boxed_2278_, v_x_2277_);
lean_dec_ref(v_x_2277_);
lean_dec_ref(v_x_2275_);
v_r_2280_ = lean_box(v_res_2279_);
return v_r_2280_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(lean_object* v_x_2281_, lean_object* v_x_2282_){
_start:
{
uint64_t v___x_2283_; size_t v___x_2284_; uint8_t v___x_2285_; 
v___x_2283_ = l_Lean_instHashableExtraModUse_hash(v_x_2282_);
v___x_2284_ = lean_uint64_to_usize(v___x_2283_);
v___x_2285_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2281_, v___x_2284_, v_x_2282_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_x_2286_, lean_object* v_x_2287_){
_start:
{
uint8_t v_res_2288_; lean_object* v_r_2289_; 
v_res_2288_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_2286_, v_x_2287_);
lean_dec_ref(v_x_2287_);
lean_dec_ref(v_x_2286_);
v_r_2289_ = lean_box(v_res_2288_);
return v_r_2289_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2290_; double v___x_2291_; 
v___x_2290_ = lean_unsigned_to_nat(0u);
v___x_2291_ = lean_float_of_nat(v___x_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(lean_object* v_cls_2295_, lean_object* v_msg_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_Elab_Command_getRef___redArg(v___y_2297_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2302_; lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2351_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2301_);
lean_dec_ref_known(v___x_2300_, 1);
v___x_2302_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msg_2296_, v___y_2298_);
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2351_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2351_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2307_; lean_object* v_traceState_2308_; lean_object* v_env_2309_; lean_object* v_messages_2310_; lean_object* v_scopes_2311_; lean_object* v_usedQuotCtxts_2312_; lean_object* v_nextMacroScope_2313_; lean_object* v_maxRecDepth_2314_; lean_object* v_ngen_2315_; lean_object* v_auxDeclNGen_2316_; lean_object* v_infoState_2317_; lean_object* v_snapshotTasks_2318_; lean_object* v_prevLinterStates_2319_; lean_object* v_codeQualityEntryTasks_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2350_; 
v___x_2307_ = lean_st_ref_take(v___y_2298_);
v_traceState_2308_ = lean_ctor_get(v___x_2307_, 9);
v_env_2309_ = lean_ctor_get(v___x_2307_, 0);
v_messages_2310_ = lean_ctor_get(v___x_2307_, 1);
v_scopes_2311_ = lean_ctor_get(v___x_2307_, 2);
v_usedQuotCtxts_2312_ = lean_ctor_get(v___x_2307_, 3);
v_nextMacroScope_2313_ = lean_ctor_get(v___x_2307_, 4);
v_maxRecDepth_2314_ = lean_ctor_get(v___x_2307_, 5);
v_ngen_2315_ = lean_ctor_get(v___x_2307_, 6);
v_auxDeclNGen_2316_ = lean_ctor_get(v___x_2307_, 7);
v_infoState_2317_ = lean_ctor_get(v___x_2307_, 8);
v_snapshotTasks_2318_ = lean_ctor_get(v___x_2307_, 10);
v_prevLinterStates_2319_ = lean_ctor_get(v___x_2307_, 11);
v_codeQualityEntryTasks_2320_ = lean_ctor_get(v___x_2307_, 12);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2322_ = v___x_2307_;
v_isShared_2323_ = v_isSharedCheck_2350_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2320_);
lean_inc(v_prevLinterStates_2319_);
lean_inc(v_snapshotTasks_2318_);
lean_inc(v_traceState_2308_);
lean_inc(v_infoState_2317_);
lean_inc(v_auxDeclNGen_2316_);
lean_inc(v_ngen_2315_);
lean_inc(v_maxRecDepth_2314_);
lean_inc(v_nextMacroScope_2313_);
lean_inc(v_usedQuotCtxts_2312_);
lean_inc(v_scopes_2311_);
lean_inc(v_messages_2310_);
lean_inc(v_env_2309_);
lean_dec(v___x_2307_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2350_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
uint64_t v_tid_2324_; lean_object* v_traces_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2349_; 
v_tid_2324_ = lean_ctor_get_uint64(v_traceState_2308_, sizeof(void*)*1);
v_traces_2325_ = lean_ctor_get(v_traceState_2308_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_traceState_2308_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2327_ = v_traceState_2308_;
v_isShared_2328_ = v_isSharedCheck_2349_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_traces_2325_);
lean_dec(v_traceState_2308_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2349_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; double v___x_2331_; uint8_t v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2329_ = lean_box(0);
v___x_2330_ = lean_box(0);
v___x_2331_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0);
v___x_2332_ = 0;
v___x_2333_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1));
v___x_2334_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2334_, 0, v_cls_2295_);
lean_ctor_set(v___x_2334_, 1, v___x_2330_);
lean_ctor_set(v___x_2334_, 2, v___x_2333_);
lean_ctor_set_float(v___x_2334_, sizeof(void*)*3, v___x_2331_);
lean_ctor_set_float(v___x_2334_, sizeof(void*)*3 + 8, v___x_2331_);
lean_ctor_set_uint8(v___x_2334_, sizeof(void*)*3 + 16, v___x_2332_);
v___x_2335_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2));
v___x_2336_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set(v___x_2336_, 1, v_a_2303_);
lean_ctor_set(v___x_2336_, 2, v___x_2335_);
v___x_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2337_, 0, v_a_2301_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
v___x_2338_ = l_Lean_PersistentArray_push___redArg(v_traces_2325_, v___x_2337_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v___x_2338_);
v___x_2340_ = v___x_2327_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2338_);
lean_ctor_set_uint64(v_reuseFailAlloc_2348_, sizeof(void*)*1, v_tid_2324_);
v___x_2340_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_object* v___x_2342_; 
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 9, v___x_2340_);
v___x_2342_ = v___x_2322_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_env_2309_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_messages_2310_);
lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_scopes_2311_);
lean_ctor_set(v_reuseFailAlloc_2347_, 3, v_usedQuotCtxts_2312_);
lean_ctor_set(v_reuseFailAlloc_2347_, 4, v_nextMacroScope_2313_);
lean_ctor_set(v_reuseFailAlloc_2347_, 5, v_maxRecDepth_2314_);
lean_ctor_set(v_reuseFailAlloc_2347_, 6, v_ngen_2315_);
lean_ctor_set(v_reuseFailAlloc_2347_, 7, v_auxDeclNGen_2316_);
lean_ctor_set(v_reuseFailAlloc_2347_, 8, v_infoState_2317_);
lean_ctor_set(v_reuseFailAlloc_2347_, 9, v___x_2340_);
lean_ctor_set(v_reuseFailAlloc_2347_, 10, v_snapshotTasks_2318_);
lean_ctor_set(v_reuseFailAlloc_2347_, 11, v_prevLinterStates_2319_);
lean_ctor_set(v_reuseFailAlloc_2347_, 12, v_codeQualityEntryTasks_2320_);
v___x_2342_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
lean_object* v___x_2343_; lean_object* v___x_2345_; 
v___x_2343_ = lean_st_ref_put(v___y_2298_, v___x_2342_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v___x_2329_);
v___x_2345_ = v___x_2305_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2329_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec_ref(v_msg_2296_);
lean_dec(v_cls_2295_);
v_a_2352_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2300_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2300_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___boxed(lean_object* v_cls_2360_, lean_object* v_msg_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_2360_, v_msg_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___lam__0(lean_object* v___x_2366_, lean_object* v_entry_2367_, lean_object* v_s_2368_){
_start:
{
lean_object* v_addEntryFn_2369_; lean_object* v_importedEntries_2370_; lean_object* v_state_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2379_; 
v_addEntryFn_2369_ = lean_ctor_get(v___x_2366_, 3);
lean_inc(v_addEntryFn_2369_);
lean_dec_ref(v___x_2366_);
v_importedEntries_2370_ = lean_ctor_get(v_s_2368_, 0);
v_state_2371_ = lean_ctor_get(v_s_2368_, 1);
v_isSharedCheck_2379_ = !lean_is_exclusive(v_s_2368_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2373_ = v_s_2368_;
v_isShared_2374_ = v_isSharedCheck_2379_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_state_2371_);
lean_inc(v_importedEntries_2370_);
lean_dec(v_s_2368_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2379_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v_state_2375_; lean_object* v___x_2377_; 
v_state_2375_ = lean_apply_2(v_addEntryFn_2369_, v_state_2371_, v_entry_2367_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 1, v_state_2375_);
v___x_2377_ = v___x_2373_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_importedEntries_2370_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v_state_2375_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2380_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3));
v___x_2386_ = l_Lean_stringToMessageData(v___x_2385_);
return v___x_2386_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5));
v___x_2389_ = l_Lean_stringToMessageData(v___x_2388_);
return v___x_2389_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1));
v___x_2391_ = l_Lean_stringToMessageData(v___x_2390_);
return v___x_2391_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v_cls_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_cls_2395_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2));
v___x_2396_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9));
v___x_2397_ = l_Lean_Name_append(v___x_2396_, v_cls_2395_);
return v___x_2397_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11));
v___x_2400_ = l_Lean_stringToMessageData(v___x_2399_);
return v___x_2400_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13));
v___x_2403_ = l_Lean_stringToMessageData(v___x_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(lean_object* v_mod_2408_, uint8_t v_isMeta_2409_, lean_object* v_hint_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v_env_2435_; uint8_t v_isExporting_2436_; lean_object* v_entry_2437_; lean_object* v___x_2438_; lean_object* v_env_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; uint8_t v___x_2444_; 
v___x_2433_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0);
v___x_2434_ = lean_st_ref_get(v___y_2412_);
v_env_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc_ref(v_env_2435_);
lean_dec(v___x_2434_);
v_isExporting_2436_ = lean_ctor_get_uint8(v_env_2435_, sizeof(void*)*13);
lean_dec_ref(v_env_2435_);
lean_inc(v_mod_2408_);
v_entry_2437_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2437_, 0, v_mod_2408_);
lean_ctor_set_uint8(v_entry_2437_, sizeof(void*)*1, v_isExporting_2436_);
lean_ctor_set_uint8(v_entry_2437_, sizeof(void*)*1 + 1, v_isMeta_2409_);
v___x_2438_ = lean_st_ref_get(v___y_2412_);
v_env_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc_ref(v_env_2439_);
lean_dec(v___x_2438_);
v___x_2440_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2441_ = lean_box(1);
v___x_2442_ = lean_box(0);
v___x_2443_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2433_, v___x_2440_, v_env_2439_, v___x_2441_, v___x_2442_);
v___x_2444_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v___x_2443_, v_entry_2437_);
lean_dec(v___x_2443_);
if (v___x_2444_ == 0)
{
lean_object* v___f_2445_; uint8_t v___x_2446_; lean_object* v___y_2448_; lean_object* v_cls_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v_scopes_2494_; lean_object* v___x_2495_; lean_object* v_opts_2496_; uint8_t v_hasTrace_2497_; 
v___f_2445_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_2445_, 0, v___x_2440_);
lean_closure_set(v___f_2445_, 1, v_entry_2437_);
v___x_2446_ = 1;
v_cls_2470_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2));
v___x_2471_ = l_Lean_inheritedTraceOptions;
v___x_2472_ = lean_st_ref_get(v___x_2471_);
v___x_2473_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2474_ = lean_st_ref_get(v___y_2412_);
v_scopes_2494_ = lean_ctor_get(v___x_2474_, 2);
lean_inc(v_scopes_2494_);
lean_dec(v___x_2474_);
v___x_2495_ = l_List_head_x21___redArg(v___x_2473_, v_scopes_2494_);
lean_dec(v_scopes_2494_);
v_opts_2496_ = lean_ctor_get(v___x_2495_, 1);
lean_inc_ref(v_opts_2496_);
lean_dec(v___x_2495_);
v_hasTrace_2497_ = lean_ctor_get_uint8(v_opts_2496_, sizeof(void*)*1);
if (v_hasTrace_2497_ == 0)
{
lean_dec_ref(v_opts_2496_);
lean_dec(v___x_2472_);
lean_dec(v_hint_2410_);
lean_dec(v_mod_2408_);
v___y_2448_ = v___y_2412_;
goto v___jp_2447_;
}
else
{
lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___x_2498_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10);
v___x_2499_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2472_, v_opts_2496_, v___x_2498_);
lean_dec_ref(v_opts_2496_);
lean_dec(v___x_2472_);
if (v___x_2499_ == 0)
{
lean_dec(v_hint_2410_);
lean_dec(v_mod_2408_);
v___y_2448_ = v___y_2412_;
goto v___jp_2447_;
}
else
{
lean_object* v___x_2500_; lean_object* v___y_2502_; 
v___x_2500_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12);
if (v_isExporting_2436_ == 0)
{
lean_object* v___x_2509_; 
v___x_2509_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17));
v___y_2502_ = v___x_2509_;
goto v___jp_2501_;
}
else
{
lean_object* v___x_2510_; 
v___x_2510_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18));
v___y_2502_ = v___x_2510_;
goto v___jp_2501_;
}
v___jp_2501_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_inc_ref(v___y_2502_);
v___x_2503_ = l_Lean_stringToMessageData(v___y_2502_);
v___x_2504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2500_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14);
v___x_2506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2504_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
if (v_isMeta_2409_ == 0)
{
lean_object* v___x_2507_; 
v___x_2507_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15));
v___y_2481_ = v___x_2506_;
v___y_2482_ = v___x_2507_;
goto v___jp_2480_;
}
else
{
lean_object* v___x_2508_; 
v___x_2508_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16));
v___y_2481_ = v___x_2506_;
v___y_2482_ = v___x_2508_;
goto v___jp_2480_;
}
}
}
}
v___jp_2447_:
{
lean_object* v___x_2449_; lean_object* v_toEnvExtension_2450_; lean_object* v_env_2451_; lean_object* v_messages_2452_; lean_object* v_scopes_2453_; lean_object* v_usedQuotCtxts_2454_; lean_object* v_nextMacroScope_2455_; lean_object* v_maxRecDepth_2456_; lean_object* v_ngen_2457_; lean_object* v_auxDeclNGen_2458_; lean_object* v_infoState_2459_; lean_object* v_traceState_2460_; lean_object* v_snapshotTasks_2461_; lean_object* v_prevLinterStates_2462_; lean_object* v_codeQualityEntryTasks_2463_; lean_object* v_asyncMode_2464_; uint8_t v_logWrites_2465_; lean_object* v___x_2466_; 
v___x_2449_ = lean_st_ref_take(v___y_2448_);
v_toEnvExtension_2450_ = lean_ctor_get(v___x_2440_, 0);
v_env_2451_ = lean_ctor_get(v___x_2449_, 0);
lean_inc_ref(v_env_2451_);
v_messages_2452_ = lean_ctor_get(v___x_2449_, 1);
lean_inc_ref(v_messages_2452_);
v_scopes_2453_ = lean_ctor_get(v___x_2449_, 2);
lean_inc(v_scopes_2453_);
v_usedQuotCtxts_2454_ = lean_ctor_get(v___x_2449_, 3);
lean_inc(v_usedQuotCtxts_2454_);
v_nextMacroScope_2455_ = lean_ctor_get(v___x_2449_, 4);
lean_inc(v_nextMacroScope_2455_);
v_maxRecDepth_2456_ = lean_ctor_get(v___x_2449_, 5);
lean_inc(v_maxRecDepth_2456_);
v_ngen_2457_ = lean_ctor_get(v___x_2449_, 6);
lean_inc_ref(v_ngen_2457_);
v_auxDeclNGen_2458_ = lean_ctor_get(v___x_2449_, 7);
lean_inc_ref(v_auxDeclNGen_2458_);
v_infoState_2459_ = lean_ctor_get(v___x_2449_, 8);
lean_inc_ref(v_infoState_2459_);
v_traceState_2460_ = lean_ctor_get(v___x_2449_, 9);
lean_inc_ref(v_traceState_2460_);
v_snapshotTasks_2461_ = lean_ctor_get(v___x_2449_, 10);
lean_inc_ref(v_snapshotTasks_2461_);
v_prevLinterStates_2462_ = lean_ctor_get(v___x_2449_, 11);
lean_inc(v_prevLinterStates_2462_);
v_codeQualityEntryTasks_2463_ = lean_ctor_get(v___x_2449_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2463_);
lean_dec(v___x_2449_);
v_asyncMode_2464_ = lean_ctor_get(v_toEnvExtension_2450_, 2);
v_logWrites_2465_ = lean_ctor_get_uint8(v_toEnvExtension_2450_, sizeof(void*)*6);
v___x_2466_ = lean_box(0);
if (v_logWrites_2465_ == 0)
{
lean_object* v___x_2467_; 
lean_inc_ref(v_toEnvExtension_2450_);
v___x_2467_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2450_, v_env_2451_, v___f_2445_, v_asyncMode_2464_, v___x_2442_, v___x_2446_);
v___y_2415_ = v_messages_2452_;
v___y_2416_ = v_scopes_2453_;
v___y_2417_ = v_usedQuotCtxts_2454_;
v___y_2418_ = v_prevLinterStates_2462_;
v___y_2419_ = v_infoState_2459_;
v___y_2420_ = v_ngen_2457_;
v___y_2421_ = v_codeQualityEntryTasks_2463_;
v___y_2422_ = v_traceState_2460_;
v___y_2423_ = v_nextMacroScope_2455_;
v___y_2424_ = v_snapshotTasks_2461_;
v___y_2425_ = v_maxRecDepth_2456_;
v___y_2426_ = v___y_2448_;
v___y_2427_ = v_auxDeclNGen_2458_;
v___y_2428_ = v___x_2466_;
v___y_2429_ = v___x_2467_;
goto v___jp_2414_;
}
else
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
lean_inc_ref_n(v_toEnvExtension_2450_, 2);
v___x_2468_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2450_, v_env_2451_);
lean_dec_ref(v_env_2451_);
v___x_2469_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2450_, v___x_2468_, v___f_2445_, v_asyncMode_2464_, v___x_2442_, v___x_2446_);
v___y_2415_ = v_messages_2452_;
v___y_2416_ = v_scopes_2453_;
v___y_2417_ = v_usedQuotCtxts_2454_;
v___y_2418_ = v_prevLinterStates_2462_;
v___y_2419_ = v_infoState_2459_;
v___y_2420_ = v_ngen_2457_;
v___y_2421_ = v_codeQualityEntryTasks_2463_;
v___y_2422_ = v_traceState_2460_;
v___y_2423_ = v_nextMacroScope_2455_;
v___y_2424_ = v_snapshotTasks_2461_;
v___y_2425_ = v_maxRecDepth_2456_;
v___y_2426_ = v___y_2448_;
v___y_2427_ = v_auxDeclNGen_2458_;
v___y_2428_ = v___x_2466_;
v___y_2429_ = v___x_2469_;
goto v___jp_2414_;
}
}
v___jp_2475_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___y_2476_);
lean_ctor_set(v___x_2478_, 1, v___y_2477_);
v___x_2479_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_2470_, v___x_2478_, v___y_2411_, v___y_2412_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_dec_ref_known(v___x_2479_, 1);
v___y_2448_ = v___y_2412_;
goto v___jp_2447_;
}
else
{
lean_dec_ref(v___f_2445_);
return v___x_2479_;
}
}
v___jp_2480_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; 
lean_inc_ref(v___y_2482_);
v___x_2483_ = l_Lean_stringToMessageData(v___y_2482_);
v___x_2484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___y_2481_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
v___x_2485_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4);
v___x_2486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2484_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = l_Lean_MessageData_ofName(v_mod_2408_);
v___x_2488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = l_Lean_Name_isAnonymous(v_hint_2410_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6);
v___x_2491_ = l_Lean_MessageData_ofName(v_hint_2410_);
v___x_2492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2490_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
v___y_2476_ = v___x_2488_;
v___y_2477_ = v___x_2492_;
goto v___jp_2475_;
}
else
{
lean_object* v___x_2493_; 
lean_dec(v_hint_2410_);
v___x_2493_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7);
v___y_2476_ = v___x_2488_;
v___y_2477_ = v___x_2493_;
goto v___jp_2475_;
}
}
}
else
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
lean_dec_ref_known(v_entry_2437_, 1);
lean_dec(v_hint_2410_);
lean_dec(v_mod_2408_);
v___x_2511_ = lean_box(0);
v___x_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
return v___x_2512_;
}
v___jp_2414_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2430_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2430_, 0, v___y_2429_);
lean_ctor_set(v___x_2430_, 1, v___y_2415_);
lean_ctor_set(v___x_2430_, 2, v___y_2416_);
lean_ctor_set(v___x_2430_, 3, v___y_2417_);
lean_ctor_set(v___x_2430_, 4, v___y_2423_);
lean_ctor_set(v___x_2430_, 5, v___y_2425_);
lean_ctor_set(v___x_2430_, 6, v___y_2420_);
lean_ctor_set(v___x_2430_, 7, v___y_2427_);
lean_ctor_set(v___x_2430_, 8, v___y_2419_);
lean_ctor_set(v___x_2430_, 9, v___y_2422_);
lean_ctor_set(v___x_2430_, 10, v___y_2424_);
lean_ctor_set(v___x_2430_, 11, v___y_2418_);
lean_ctor_set(v___x_2430_, 12, v___y_2421_);
v___x_2431_ = lean_st_ref_put(v___y_2426_, v___x_2430_);
v___x_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2432_, 0, v___y_2428_);
return v___x_2432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___boxed(lean_object* v_mod_2513_, lean_object* v_isMeta_2514_, lean_object* v_hint_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
uint8_t v_isMeta_boxed_2519_; lean_object* v_res_2520_; 
v_isMeta_boxed_2519_ = lean_unbox(v_isMeta_2514_);
v_res_2520_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_mod_2513_, v_isMeta_boxed_2519_, v_hint_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(lean_object* v___x_2521_, lean_object* v_declName_2522_, lean_object* v_as_2523_, size_t v_sz_2524_, size_t v_i_2525_, lean_object* v_b_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
uint8_t v___x_2530_; 
v___x_2530_ = lean_usize_dec_lt(v_i_2525_, v_sz_2524_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; 
lean_dec(v_declName_2522_);
v___x_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2531_, 0, v_b_2526_);
return v___x_2531_;
}
else
{
lean_object* v___x_2532_; lean_object* v_modules_2533_; lean_object* v___x_2534_; lean_object* v_a_2535_; lean_object* v___x_2536_; lean_object* v_toImport_2537_; lean_object* v_module_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; lean_object* v___x_2541_; 
v___x_2532_ = l_Lean_Environment_header(v___x_2521_);
v_modules_2533_ = lean_ctor_get(v___x_2532_, 3);
lean_inc_ref(v_modules_2533_);
lean_dec_ref(v___x_2532_);
v___x_2534_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2535_ = lean_array_uget_borrowed(v_as_2523_, v_i_2525_);
v___x_2536_ = lean_array_get(v___x_2534_, v_modules_2533_, v_a_2535_);
lean_dec_ref(v_modules_2533_);
v_toImport_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc_ref(v_toImport_2537_);
lean_dec(v___x_2536_);
v_module_2538_ = lean_ctor_get(v_toImport_2537_, 0);
lean_inc(v_module_2538_);
lean_dec_ref(v_toImport_2537_);
v___x_2539_ = lean_box(0);
v___x_2540_ = 0;
lean_inc(v_declName_2522_);
v___x_2541_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_2538_, v___x_2540_, v_declName_2522_, v___y_2527_, v___y_2528_);
if (lean_obj_tag(v___x_2541_) == 0)
{
size_t v___x_2542_; size_t v___x_2543_; 
lean_dec_ref_known(v___x_2541_, 1);
v___x_2542_ = ((size_t)1ULL);
v___x_2543_ = lean_usize_add(v_i_2525_, v___x_2542_);
v_i_2525_ = v___x_2543_;
v_b_2526_ = v___x_2539_;
goto _start;
}
else
{
lean_dec(v_declName_2522_);
return v___x_2541_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4___boxed(lean_object* v___x_2545_, lean_object* v_declName_2546_, lean_object* v_as_2547_, lean_object* v_sz_2548_, lean_object* v_i_2549_, lean_object* v_b_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
size_t v_sz_boxed_2554_; size_t v_i_boxed_2555_; lean_object* v_res_2556_; 
v_sz_boxed_2554_ = lean_unbox_usize(v_sz_2548_);
lean_dec(v_sz_2548_);
v_i_boxed_2555_ = lean_unbox_usize(v_i_2549_);
lean_dec(v_i_2549_);
v_res_2556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v___x_2545_, v_declName_2546_, v_as_2547_, v_sz_boxed_2554_, v_i_boxed_2555_, v_b_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec_ref(v_as_2547_);
lean_dec_ref(v___x_2545_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(lean_object* v_a_2557_, lean_object* v_x_2558_){
_start:
{
if (lean_obj_tag(v_x_2558_) == 0)
{
lean_object* v___x_2559_; 
v___x_2559_ = lean_box(0);
return v___x_2559_;
}
else
{
lean_object* v_key_2560_; lean_object* v_value_2561_; lean_object* v_tail_2562_; uint8_t v___x_2563_; 
v_key_2560_ = lean_ctor_get(v_x_2558_, 0);
v_value_2561_ = lean_ctor_get(v_x_2558_, 1);
v_tail_2562_ = lean_ctor_get(v_x_2558_, 2);
v___x_2563_ = lean_name_eq(v_key_2560_, v_a_2557_);
if (v___x_2563_ == 0)
{
v_x_2558_ = v_tail_2562_;
goto _start;
}
else
{
lean_object* v___x_2565_; 
lean_inc(v_value_2561_);
v___x_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2565_, 0, v_value_2561_);
return v___x_2565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v_a_2566_, lean_object* v_x_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_2566_, v_x_2567_);
lean_dec(v_x_2567_);
lean_dec(v_a_2566_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(lean_object* v_m_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v_buckets_2571_; lean_object* v___x_2572_; uint64_t v___y_2574_; 
v_buckets_2571_ = lean_ctor_get(v_m_2569_, 1);
v___x_2572_ = lean_array_get_size(v_buckets_2571_);
if (lean_obj_tag(v_a_2570_) == 0)
{
uint64_t v___x_2588_; 
v___x_2588_ = 1723ULL;
v___y_2574_ = v___x_2588_;
goto v___jp_2573_;
}
else
{
uint64_t v_hash_2589_; 
v_hash_2589_ = lean_ctor_get_uint64(v_a_2570_, sizeof(void*)*2);
v___y_2574_ = v_hash_2589_;
goto v___jp_2573_;
}
v___jp_2573_:
{
uint64_t v___x_2575_; uint64_t v___x_2576_; uint64_t v_fold_2577_; uint64_t v___x_2578_; uint64_t v___x_2579_; uint64_t v___x_2580_; size_t v___x_2581_; size_t v___x_2582_; size_t v___x_2583_; size_t v___x_2584_; size_t v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2575_ = 32ULL;
v___x_2576_ = lean_uint64_shift_right(v___y_2574_, v___x_2575_);
v_fold_2577_ = lean_uint64_xor(v___y_2574_, v___x_2576_);
v___x_2578_ = 16ULL;
v___x_2579_ = lean_uint64_shift_right(v_fold_2577_, v___x_2578_);
v___x_2580_ = lean_uint64_xor(v_fold_2577_, v___x_2579_);
v___x_2581_ = lean_uint64_to_usize(v___x_2580_);
v___x_2582_ = lean_usize_of_nat(v___x_2572_);
v___x_2583_ = ((size_t)1ULL);
v___x_2584_ = lean_usize_sub(v___x_2582_, v___x_2583_);
v___x_2585_ = lean_usize_land(v___x_2581_, v___x_2584_);
v___x_2586_ = lean_array_uget_borrowed(v_buckets_2571_, v___x_2585_);
v___x_2587_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_2570_, v___x_2586_);
return v___x_2587_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_m_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_2590_, v_a_2591_);
lean_dec(v_a_2591_);
lean_dec_ref(v_m_2590_);
return v_res_2592_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(lean_object* v_declName_2596_, uint8_t v_isMeta_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v_env_2606_; lean_object* v___y_2608_; lean_object* v___x_2621_; 
v___x_2601_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0);
v___x_2602_ = lean_st_ref_get(v___y_2599_);
v_env_2606_ = lean_ctor_get(v___x_2602_, 0);
lean_inc_ref(v_env_2606_);
lean_dec(v___x_2602_);
v___x_2621_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2606_, v_declName_2596_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_dec_ref(v_env_2606_);
lean_dec(v_declName_2596_);
goto v___jp_2603_;
}
else
{
lean_object* v_val_2622_; lean_object* v___x_2623_; lean_object* v_modules_2624_; lean_object* v___x_2625_; uint8_t v___x_2626_; 
v_val_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_val_2622_);
lean_dec_ref_known(v___x_2621_, 1);
v___x_2623_ = l_Lean_Environment_header(v_env_2606_);
v_modules_2624_ = lean_ctor_get(v___x_2623_, 3);
lean_inc_ref(v_modules_2624_);
lean_dec_ref(v___x_2623_);
v___x_2625_ = lean_array_get_size(v_modules_2624_);
v___x_2626_ = lean_nat_dec_lt(v_val_2622_, v___x_2625_);
if (v___x_2626_ == 0)
{
lean_dec_ref(v_modules_2624_);
lean_dec(v_val_2622_);
lean_dec_ref(v_env_2606_);
lean_dec(v_declName_2596_);
goto v___jp_2603_;
}
else
{
lean_object* v___x_2627_; lean_object* v___x_2628_; uint8_t v___y_2630_; 
v___x_2627_ = lean_array_fget(v_modules_2624_, v_val_2622_);
lean_dec(v_val_2622_);
lean_dec_ref(v_modules_2624_);
v___x_2628_ = lean_st_ref_get(v___y_2599_);
if (v_isMeta_2597_ == 0)
{
lean_dec(v___x_2628_);
v___y_2630_ = v_isMeta_2597_;
goto v___jp_2629_;
}
else
{
lean_object* v_env_2641_; uint8_t v___x_2642_; 
v_env_2641_ = lean_ctor_get(v___x_2628_, 0);
lean_inc_ref(v_env_2641_);
lean_dec(v___x_2628_);
lean_inc(v_declName_2596_);
v___x_2642_ = l_Lean_isMarkedMeta(v_env_2641_, v_declName_2596_);
if (v___x_2642_ == 0)
{
v___y_2630_ = v_isMeta_2597_;
goto v___jp_2629_;
}
else
{
uint8_t v___x_2643_; 
v___x_2643_ = 0;
v___y_2630_ = v___x_2643_;
goto v___jp_2629_;
}
}
v___jp_2629_:
{
lean_object* v_toImport_2631_; lean_object* v_module_2632_; lean_object* v___x_2633_; 
v_toImport_2631_ = lean_ctor_get(v___x_2627_, 0);
lean_inc_ref(v_toImport_2631_);
lean_dec(v___x_2627_);
v_module_2632_ = lean_ctor_get(v_toImport_2631_, 0);
lean_inc(v_module_2632_);
lean_dec_ref(v_toImport_2631_);
lean_inc(v_declName_2596_);
v___x_2633_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_2632_, v___y_2630_, v_declName_2596_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
lean_dec_ref_known(v___x_2633_, 1);
v___x_2634_ = l_Lean_indirectModUseExt;
v___x_2635_ = lean_box(1);
v___x_2636_ = lean_box(0);
lean_inc_ref(v_env_2606_);
v___x_2637_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2601_, v___x_2634_, v_env_2606_, v___x_2635_, v___x_2636_);
v___x_2638_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v___x_2637_, v_declName_2596_);
lean_dec(v___x_2637_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v___x_2639_; 
v___x_2639_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1));
v___y_2608_ = v___x_2639_;
goto v___jp_2607_;
}
else
{
lean_object* v_val_2640_; 
v_val_2640_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_val_2640_);
lean_dec_ref_known(v___x_2638_, 1);
v___y_2608_ = v_val_2640_;
goto v___jp_2607_;
}
}
else
{
lean_dec_ref(v_env_2606_);
lean_dec(v_declName_2596_);
return v___x_2633_;
}
}
}
}
v___jp_2603_:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = lean_box(0);
v___x_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
return v___x_2605_;
}
v___jp_2607_:
{
lean_object* v___x_2609_; size_t v_sz_2610_; size_t v___x_2611_; lean_object* v___x_2612_; 
v___x_2609_ = lean_box(0);
v_sz_2610_ = lean_array_size(v___y_2608_);
v___x_2611_ = ((size_t)0ULL);
v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v_env_2606_, v_declName_2596_, v___y_2608_, v_sz_2610_, v___x_2611_, v___x_2609_, v___y_2598_, v___y_2599_);
lean_dec_ref(v___y_2608_);
lean_dec_ref(v_env_2606_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2619_ == 0)
{
lean_object* v_unused_2620_; 
v_unused_2620_ = lean_ctor_get(v___x_2612_, 0);
lean_dec(v_unused_2620_);
v___x_2614_ = v___x_2612_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_dec(v___x_2612_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v___x_2609_);
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2609_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
else
{
return v___x_2612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___boxed(lean_object* v_declName_2644_, lean_object* v_isMeta_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
uint8_t v_isMeta_boxed_2649_; lean_object* v_res_2650_; 
v_isMeta_boxed_2649_ = lean_unbox(v_isMeta_2645_);
v_res_2650_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_declName_2644_, v_isMeta_boxed_2649_, v___y_2646_, v___y_2647_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(lean_object* v_as_x27_2651_, lean_object* v_b_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
if (lean_obj_tag(v_as_x27_2651_) == 0)
{
lean_object* v___x_2656_; 
v___x_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2656_, 0, v_b_2652_);
return v___x_2656_;
}
else
{
lean_object* v_head_2657_; lean_object* v_tail_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; lean_object* v___x_2661_; 
v_head_2657_ = lean_ctor_get(v_as_x27_2651_, 0);
v_tail_2658_ = lean_ctor_get(v_as_x27_2651_, 1);
v___x_2659_ = lean_box(0);
v___x_2660_ = 1;
lean_inc(v_head_2657_);
v___x_2661_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_head_2657_, v___x_2660_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_dec_ref_known(v___x_2661_, 1);
v_as_x27_2651_ = v_tail_2658_;
v_b_2652_ = v___x_2659_;
goto _start;
}
else
{
return v___x_2661_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_2663_, lean_object* v_b_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_2663_, v_b_2664_, v___y_2665_, v___y_2666_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v_as_x27_2663_);
return v_res_2668_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2674_ = l_Lean_maxRecDepthErrorMessage;
v___x_2675_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
return v___x_2675_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2676_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3);
v___x_2677_ = l_Lean_MessageData_ofFormat(v___x_2676_);
return v___x_2677_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2678_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4);
v___x_2679_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2));
v___x_2680_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2679_);
lean_ctor_set(v___x_2680_, 1, v___x_2678_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(lean_object* v_ref_2681_){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5);
v___x_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2684_, 0, v_ref_2681_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___boxed(lean_object* v_ref_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_2686_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(lean_object* v_currNamespace_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2692_, 0, v_currNamespace_2689_);
lean_ctor_set(v___x_2692_, 1, v___y_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(v_currNamespace_2693_, v___y_2694_, v___y_2695_);
lean_dec_ref(v___y_2694_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(lean_object* v_env_2697_, lean_object* v_declName_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
uint8_t v___x_2701_; lean_object* v_env_2702_; lean_object* v___x_2703_; uint8_t v___x_2704_; uint8_t v___x_2705_; 
v___x_2701_ = 0;
v_env_2702_ = l_Lean_Environment_setExporting(v_env_2697_, v___x_2701_);
lean_inc(v_declName_2698_);
v___x_2703_ = l_Lean_mkPrivateName(v_env_2702_, v_declName_2698_);
v___x_2704_ = 1;
lean_inc_ref(v_env_2702_);
v___x_2705_ = l_Lean_Environment_contains(v_env_2702_, v___x_2703_, v___x_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; uint8_t v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2706_ = l_Lean_privateToUserName(v_declName_2698_);
v___x_2707_ = l_Lean_Environment_contains(v_env_2702_, v___x_2706_, v___x_2704_);
v___x_2708_ = lean_box(v___x_2707_);
v___x_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
lean_ctor_set(v___x_2709_, 1, v___y_2700_);
return v___x_2709_;
}
else
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_dec_ref(v_env_2702_);
lean_dec(v_declName_2698_);
v___x_2710_ = lean_box(v___x_2705_);
v___x_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
lean_ctor_set(v___x_2711_, 1, v___y_2700_);
return v___x_2711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed(lean_object* v_env_2712_, lean_object* v_declName_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(v_env_2712_, v_declName_2713_, v___y_2714_, v___y_2715_);
lean_dec_ref(v___y_2714_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(lean_object* v_x_2717_, lean_object* v___y_2718_){
_start:
{
if (lean_obj_tag(v_x_2717_) == 0)
{
lean_object* v_a_2719_; lean_object* v___x_2720_; 
v_a_2719_ = lean_ctor_get(v_x_2717_, 0);
lean_inc(v_a_2719_);
v___x_2720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2720_, 0, v_a_2719_);
lean_ctor_set(v___x_2720_, 1, v___y_2718_);
return v___x_2720_;
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2722_; 
v_a_2721_ = lean_ctor_get(v_x_2717_, 0);
lean_inc(v_a_2721_);
v___x_2722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2722_, 0, v_a_2721_);
lean_ctor_set(v___x_2722_, 1, v___y_2718_);
return v___x_2722_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg___boxed(lean_object* v_x_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_2723_, v___y_2724_);
lean_dec_ref(v_x_2723_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(lean_object* v_env_2726_, lean_object* v_stx_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v___x_2730_; 
v___x_2730_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2726_, v_stx_2727_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
if (lean_obj_tag(v_a_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2740_; 
v_a_2732_ = lean_ctor_get(v___x_2730_, 1);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2740_ == 0)
{
lean_object* v_unused_2741_; 
v_unused_2741_ = lean_ctor_get(v___x_2730_, 0);
lean_dec(v_unused_2741_);
v___x_2734_ = v___x_2730_;
v_isShared_2735_ = v_isSharedCheck_2740_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2730_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2740_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2736_; lean_object* v___x_2738_; 
v___x_2736_ = lean_box(0);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 0, v___x_2736_);
v___x_2738_ = v___x_2734_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_a_2732_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
else
{
lean_object* v_val_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2770_; 
v_val_2742_ = lean_ctor_get(v_a_2731_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v_a_2731_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2744_ = v_a_2731_;
v_isShared_2745_ = v_isSharedCheck_2770_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_val_2742_);
lean_dec(v_a_2731_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2770_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v_snd_2746_; 
v_snd_2746_ = lean_ctor_get(v_val_2742_, 1);
lean_inc(v_snd_2746_);
lean_dec(v_val_2742_);
if (lean_obj_tag(v_snd_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2756_; 
lean_del_object(v___x_2744_);
v_a_2747_ = lean_ctor_get(v___x_2730_, 1);
lean_inc(v_a_2747_);
lean_dec_ref_known(v___x_2730_, 2);
v_a_2748_ = lean_ctor_get(v_snd_2746_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_snd_2746_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2750_ = v_snd_2746_;
v_isShared_2751_ = v_isSharedCheck_2756_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v_snd_2746_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2756_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_2753_, v_a_2747_);
lean_dec_ref(v___x_2753_);
return v___x_2754_;
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2769_; 
v_a_2757_ = lean_ctor_get(v___x_2730_, 1);
lean_inc(v_a_2757_);
lean_dec_ref_known(v___x_2730_, 2);
v_a_2758_ = lean_ctor_get(v_snd_2746_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v_snd_2746_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2760_ = v_snd_2746_;
v_isShared_2761_ = v_isSharedCheck_2769_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v_snd_2746_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2769_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 0, v_a_2758_);
v___x_2763_ = v___x_2744_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v___x_2765_; 
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2763_);
v___x_2765_ = v___x_2760_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2763_);
v___x_2765_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v___x_2766_; 
v___x_2766_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_2765_, v_a_2757_);
lean_dec_ref(v___x_2765_);
return v___x_2766_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
v_a_2771_ = lean_ctor_get(v___x_2730_, 0);
v_a_2772_ = lean_ctor_get(v___x_2730_, 1);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2730_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_inc(v_a_2771_);
lean_dec(v___x_2730_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2771_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed(lean_object* v_env_2780_, lean_object* v_stx_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(v_env_2780_, v_stx_2781_, v___y_2782_, v___y_2783_);
lean_dec_ref(v___y_2782_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(lean_object* v_env_2785_, lean_object* v_currNamespace_2786_, lean_object* v_openDecls_2787_, lean_object* v_n_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = l_Lean_ResolveName_resolveNamespace(v_env_2785_, v_currNamespace_2786_, v_openDecls_2787_, v_n_2788_);
v___x_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
lean_ctor_set(v___x_2792_, 1, v___y_2790_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed(lean_object* v_env_2793_, lean_object* v_currNamespace_2794_, lean_object* v_openDecls_2795_, lean_object* v_n_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(v_env_2793_, v_currNamespace_2794_, v_openDecls_2795_, v_n_2796_, v___y_2797_, v___y_2798_);
lean_dec_ref(v___y_2797_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(lean_object* v_as_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
if (lean_obj_tag(v_as_2800_) == 0)
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2804_ = lean_box(0);
v___x_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
return v___x_2805_;
}
else
{
lean_object* v_head_2806_; lean_object* v_tail_2807_; lean_object* v_fst_2808_; lean_object* v_snd_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v_scopes_2814_; lean_object* v___x_2815_; lean_object* v_opts_2816_; uint8_t v_hasTrace_2817_; 
v_head_2806_ = lean_ctor_get(v_as_2800_, 0);
lean_inc(v_head_2806_);
v_tail_2807_ = lean_ctor_get(v_as_2800_, 1);
lean_inc(v_tail_2807_);
lean_dec_ref_known(v_as_2800_, 2);
v_fst_2808_ = lean_ctor_get(v_head_2806_, 0);
lean_inc(v_fst_2808_);
v_snd_2809_ = lean_ctor_get(v_head_2806_, 1);
lean_inc(v_snd_2809_);
lean_dec(v_head_2806_);
v___x_2810_ = l_Lean_inheritedTraceOptions;
v___x_2811_ = lean_st_ref_get(v___x_2810_);
v___x_2812_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2813_ = lean_st_ref_get(v___y_2802_);
v_scopes_2814_ = lean_ctor_get(v___x_2813_, 2);
lean_inc(v_scopes_2814_);
lean_dec(v___x_2813_);
v___x_2815_ = l_List_head_x21___redArg(v___x_2812_, v_scopes_2814_);
lean_dec(v_scopes_2814_);
v_opts_2816_ = lean_ctor_get(v___x_2815_, 1);
lean_inc_ref(v_opts_2816_);
lean_dec(v___x_2815_);
v_hasTrace_2817_ = lean_ctor_get_uint8(v_opts_2816_, sizeof(void*)*1);
if (v_hasTrace_2817_ == 0)
{
lean_dec_ref(v_opts_2816_);
lean_dec(v___x_2811_);
lean_dec(v_snd_2809_);
lean_dec(v_fst_2808_);
v_as_2800_ = v_tail_2807_;
goto _start;
}
else
{
lean_object* v___x_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; 
v___x_2819_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9));
lean_inc(v_fst_2808_);
v___x_2820_ = l_Lean_Name_append(v___x_2819_, v_fst_2808_);
v___x_2821_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2811_, v_opts_2816_, v___x_2820_);
lean_dec(v___x_2820_);
lean_dec_ref(v_opts_2816_);
lean_dec(v___x_2811_);
if (v___x_2821_ == 0)
{
lean_dec(v_snd_2809_);
lean_dec(v_fst_2808_);
v_as_2800_ = v_tail_2807_;
goto _start;
}
else
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2823_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2823_, 0, v_snd_2809_);
v___x_2824_ = l_Lean_MessageData_ofFormat(v___x_2823_);
v___x_2825_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_fst_2808_, v___x_2824_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_dec_ref_known(v___x_2825_, 1);
v_as_2800_ = v_tail_2807_;
goto _start;
}
else
{
lean_dec(v_tail_2807_);
return v___x_2825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___boxed(lean_object* v_as_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v_as_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(lean_object* v_env_2832_, lean_object* v_opts_2833_, lean_object* v_currNamespace_2834_, lean_object* v_openDecls_2835_, lean_object* v_n_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = l_Lean_ResolveName_resolveGlobalName(v_env_2832_, v_opts_2833_, v_currNamespace_2834_, v_openDecls_2835_, v_n_2836_);
v___x_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
lean_ctor_set(v___x_2840_, 1, v___y_2838_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed(lean_object* v_env_2841_, lean_object* v_opts_2842_, lean_object* v_currNamespace_2843_, lean_object* v_openDecls_2844_, lean_object* v_n_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(v_env_2841_, v_opts_2842_, v_currNamespace_2843_, v_openDecls_2844_, v_n_2845_, v___y_2846_, v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec_ref(v_opts_2842_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(lean_object* v_x_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v___x_2854_; lean_object* v_env_2855_; lean_object* v___f_2856_; lean_object* v___f_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v_scopes_2860_; lean_object* v___x_2861_; lean_object* v_opts_2862_; lean_object* v___x_2863_; 
v___x_2854_ = lean_st_ref_get(v___y_2852_);
v_env_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc_ref_n(v_env_2855_, 3);
lean_dec(v___x_2854_);
v___f_2856_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2856_, 0, v_env_2855_);
v___f_2857_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2857_, 0, v_env_2855_);
v___x_2858_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2859_ = lean_st_ref_get(v___y_2852_);
v_scopes_2860_ = lean_ctor_get(v___x_2859_, 2);
lean_inc(v_scopes_2860_);
lean_dec(v___x_2859_);
v___x_2861_ = l_List_head_x21___redArg(v___x_2858_, v_scopes_2860_);
lean_dec(v_scopes_2860_);
v_opts_2862_ = lean_ctor_get(v___x_2861_, 1);
lean_inc_ref(v_opts_2862_);
lean_dec(v___x_2861_);
v___x_2863_ = l_Lean_Elab_Command_getScope___redArg(v___y_2852_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v_currNamespace_2865_; lean_object* v___f_2866_; lean_object* v___x_2867_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2863_, 1);
v_currNamespace_2865_ = lean_ctor_get(v_a_2864_, 2);
lean_inc_n(v_currNamespace_2865_, 2);
lean_dec(v_a_2864_);
v___f_2866_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2866_, 0, v_currNamespace_2865_);
v___x_2867_ = l_Lean_Elab_Command_getScope___redArg(v___y_2852_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v_openDecls_2869_; lean_object* v___f_2870_; lean_object* v___f_2871_; lean_object* v_methods_2872_; lean_object* v___x_2873_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref_known(v___x_2867_, 1);
v_openDecls_2869_ = lean_ctor_get(v_a_2868_, 3);
lean_inc_n(v_openDecls_2869_, 2);
lean_dec(v_a_2868_);
lean_inc(v_currNamespace_2865_);
lean_inc_ref(v_env_2855_);
v___f_2870_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_2870_, 0, v_env_2855_);
lean_closure_set(v___f_2870_, 1, v_currNamespace_2865_);
lean_closure_set(v___f_2870_, 2, v_openDecls_2869_);
v___f_2871_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2871_, 0, v_env_2855_);
lean_closure_set(v___f_2871_, 1, v_opts_2862_);
lean_closure_set(v___f_2871_, 2, v_currNamespace_2865_);
lean_closure_set(v___f_2871_, 3, v_openDecls_2869_);
v_methods_2872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2872_, 0, v___f_2857_);
lean_ctor_set(v_methods_2872_, 1, v___f_2866_);
lean_ctor_set(v_methods_2872_, 2, v___f_2856_);
lean_ctor_set(v_methods_2872_, 3, v___f_2870_);
lean_ctor_set(v_methods_2872_, 4, v___f_2871_);
v___x_2873_ = l_Lean_Elab_Command_getRef___redArg(v___y_2851_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2875_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v___x_2875_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2851_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v_currRecDepth_2877_; lean_object* v_quotContext_x3f_2878_; lean_object* v_a_2880_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
lean_dec_ref_known(v___x_2875_, 1);
v_currRecDepth_2877_ = lean_ctor_get(v___y_2851_, 2);
v_quotContext_x3f_2878_ = lean_ctor_get(v___y_2851_, 5);
if (lean_obj_tag(v_quotContext_x3f_2878_) == 0)
{
lean_object* v___x_2954_; lean_object* v_a_2955_; 
v___x_2954_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_2852_);
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
lean_dec_ref(v___x_2954_);
v_a_2880_ = v_a_2955_;
goto v___jp_2879_;
}
else
{
lean_object* v_val_2956_; 
v_val_2956_ = lean_ctor_get(v_quotContext_x3f_2878_, 0);
lean_inc(v_val_2956_);
v_a_2880_ = v_val_2956_;
goto v___jp_2879_;
}
v___jp_2879_:
{
lean_object* v___x_2881_; lean_object* v_maxRecDepth_2882_; lean_object* v___x_2883_; lean_object* v_nextMacroScope_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2881_ = lean_st_ref_get(v___y_2852_);
v_maxRecDepth_2882_ = lean_ctor_get(v___x_2881_, 5);
lean_inc(v_maxRecDepth_2882_);
lean_dec(v___x_2881_);
v___x_2883_ = lean_st_ref_get(v___y_2852_);
v_nextMacroScope_2884_ = lean_ctor_get(v___x_2883_, 4);
lean_inc(v_nextMacroScope_2884_);
lean_dec(v___x_2883_);
lean_inc(v_currRecDepth_2877_);
v___x_2885_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2885_, 0, v_methods_2872_);
lean_ctor_set(v___x_2885_, 1, v_a_2880_);
lean_ctor_set(v___x_2885_, 2, v_a_2876_);
lean_ctor_set(v___x_2885_, 3, v_currRecDepth_2877_);
lean_ctor_set(v___x_2885_, 4, v_maxRecDepth_2882_);
lean_ctor_set(v___x_2885_, 5, v_a_2874_);
v___x_2886_ = lean_box(0);
v___x_2887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2887_, 0, v_nextMacroScope_2884_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
lean_ctor_set(v___x_2887_, 2, v___x_2886_);
v___x_2888_ = lean_apply_2(v_x_2850_, v___x_2885_, v___x_2887_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; lean_object* v_a_2890_; lean_object* v_macroScope_2891_; lean_object* v_traceMsgs_2892_; lean_object* v_expandedMacroDecls_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 1);
lean_inc(v_a_2889_);
v_a_2890_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2890_);
lean_dec_ref_known(v___x_2888_, 2);
v_macroScope_2891_ = lean_ctor_get(v_a_2889_, 0);
lean_inc(v_macroScope_2891_);
v_traceMsgs_2892_ = lean_ctor_get(v_a_2889_, 1);
lean_inc(v_traceMsgs_2892_);
v_expandedMacroDecls_2893_ = lean_ctor_get(v_a_2889_, 2);
lean_inc(v_expandedMacroDecls_2893_);
lean_dec(v_a_2889_);
v___x_2894_ = lean_box(0);
v___x_2895_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_expandedMacroDecls_2893_, v___x_2894_, v___y_2851_, v___y_2852_);
lean_dec(v_expandedMacroDecls_2893_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v___x_2896_; lean_object* v_env_2897_; lean_object* v_messages_2898_; lean_object* v_scopes_2899_; lean_object* v_usedQuotCtxts_2900_; lean_object* v_maxRecDepth_2901_; lean_object* v_ngen_2902_; lean_object* v_auxDeclNGen_2903_; lean_object* v_infoState_2904_; lean_object* v_traceState_2905_; lean_object* v_snapshotTasks_2906_; lean_object* v_prevLinterStates_2907_; lean_object* v_codeQualityEntryTasks_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2934_; 
lean_dec_ref_known(v___x_2895_, 1);
v___x_2896_ = lean_st_ref_take(v___y_2852_);
v_env_2897_ = lean_ctor_get(v___x_2896_, 0);
v_messages_2898_ = lean_ctor_get(v___x_2896_, 1);
v_scopes_2899_ = lean_ctor_get(v___x_2896_, 2);
v_usedQuotCtxts_2900_ = lean_ctor_get(v___x_2896_, 3);
v_maxRecDepth_2901_ = lean_ctor_get(v___x_2896_, 5);
v_ngen_2902_ = lean_ctor_get(v___x_2896_, 6);
v_auxDeclNGen_2903_ = lean_ctor_get(v___x_2896_, 7);
v_infoState_2904_ = lean_ctor_get(v___x_2896_, 8);
v_traceState_2905_ = lean_ctor_get(v___x_2896_, 9);
v_snapshotTasks_2906_ = lean_ctor_get(v___x_2896_, 10);
v_prevLinterStates_2907_ = lean_ctor_get(v___x_2896_, 11);
v_codeQualityEntryTasks_2908_ = lean_ctor_get(v___x_2896_, 12);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2934_ == 0)
{
lean_object* v_unused_2935_; 
v_unused_2935_ = lean_ctor_get(v___x_2896_, 4);
lean_dec(v_unused_2935_);
v___x_2910_ = v___x_2896_;
v_isShared_2911_ = v_isSharedCheck_2934_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2908_);
lean_inc(v_prevLinterStates_2907_);
lean_inc(v_snapshotTasks_2906_);
lean_inc(v_traceState_2905_);
lean_inc(v_infoState_2904_);
lean_inc(v_auxDeclNGen_2903_);
lean_inc(v_ngen_2902_);
lean_inc(v_maxRecDepth_2901_);
lean_inc(v_usedQuotCtxts_2900_);
lean_inc(v_scopes_2899_);
lean_inc(v_messages_2898_);
lean_inc(v_env_2897_);
lean_dec(v___x_2896_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2934_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 4, v_macroScope_2891_);
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_env_2897_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_messages_2898_);
lean_ctor_set(v_reuseFailAlloc_2933_, 2, v_scopes_2899_);
lean_ctor_set(v_reuseFailAlloc_2933_, 3, v_usedQuotCtxts_2900_);
lean_ctor_set(v_reuseFailAlloc_2933_, 4, v_macroScope_2891_);
lean_ctor_set(v_reuseFailAlloc_2933_, 5, v_maxRecDepth_2901_);
lean_ctor_set(v_reuseFailAlloc_2933_, 6, v_ngen_2902_);
lean_ctor_set(v_reuseFailAlloc_2933_, 7, v_auxDeclNGen_2903_);
lean_ctor_set(v_reuseFailAlloc_2933_, 8, v_infoState_2904_);
lean_ctor_set(v_reuseFailAlloc_2933_, 9, v_traceState_2905_);
lean_ctor_set(v_reuseFailAlloc_2933_, 10, v_snapshotTasks_2906_);
lean_ctor_set(v_reuseFailAlloc_2933_, 11, v_prevLinterStates_2907_);
lean_ctor_set(v_reuseFailAlloc_2933_, 12, v_codeQualityEntryTasks_2908_);
v___x_2913_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2914_ = lean_st_ref_put(v___y_2852_, v___x_2913_);
v___x_2915_ = l_List_reverse___redArg(v_traceMsgs_2892_);
v___x_2916_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v___x_2915_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2923_ == 0)
{
lean_object* v_unused_2924_; 
v_unused_2924_ = lean_ctor_get(v___x_2916_, 0);
lean_dec(v_unused_2924_);
v___x_2918_ = v___x_2916_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_dec(v___x_2916_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 0, v_a_2890_);
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2890_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec(v_a_2890_);
v_a_2925_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2916_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2916_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
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
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_dec(v_traceMsgs_2892_);
lean_dec(v_macroScope_2891_);
lean_dec(v_a_2890_);
v_a_2936_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2895_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2895_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
else
{
lean_object* v_a_2944_; 
v_a_2944_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2944_);
lean_dec_ref_known(v___x_2888_, 2);
if (lean_obj_tag(v_a_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v_a_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; 
v_a_2945_ = lean_ctor_get(v_a_2944_, 0);
lean_inc(v_a_2945_);
v_a_2946_ = lean_ctor_get(v_a_2944_, 1);
lean_inc_ref(v_a_2946_);
lean_dec_ref_known(v_a_2944_, 2);
v___x_2947_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0));
v___x_2948_ = lean_string_dec_eq(v_a_2946_, v___x_2947_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2949_, 0, v_a_2946_);
v___x_2950_ = l_Lean_MessageData_ofFormat(v___x_2949_);
v___x_2951_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_a_2945_, v___x_2950_, v___y_2851_, v___y_2852_);
lean_dec(v_a_2945_);
return v___x_2951_;
}
else
{
lean_object* v___x_2952_; 
lean_dec_ref(v_a_2946_);
v___x_2952_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_a_2945_);
return v___x_2952_;
}
}
else
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2953_;
}
}
}
}
else
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
lean_dec(v_a_2874_);
lean_dec_ref_known(v_methods_2872_, 5);
lean_dec_ref(v_x_2850_);
v_a_2957_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2875_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2875_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec_ref_known(v_methods_2872_, 5);
lean_dec_ref(v_x_2850_);
v_a_2965_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2873_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2873_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec_ref(v___f_2866_);
lean_dec(v_currNamespace_2865_);
lean_dec_ref(v_opts_2862_);
lean_dec_ref(v___f_2857_);
lean_dec_ref(v___f_2856_);
lean_dec_ref(v_env_2855_);
lean_dec_ref(v_x_2850_);
v_a_2973_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2867_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2867_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec_ref(v_opts_2862_);
lean_dec_ref(v___f_2857_);
lean_dec_ref(v___f_2856_);
lean_dec_ref(v_env_2855_);
lean_dec_ref(v_x_2850_);
v_a_2981_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2863_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2863_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___boxed(lean_object* v_x_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object* v_x_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___x_3079_; uint8_t v___x_3080_; 
v___x_3037_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_3038_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_3079_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
lean_inc(v_x_3033_);
v___x_3080_ = l_Lean_Syntax_isOfKind(v_x_3033_, v___x_3079_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3081_; 
lean_dec(v_x_3033_);
v___x_3081_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3081_;
}
else
{
lean_object* v___x_3082_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; size_t v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; uint8_t v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; size_t v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; uint8_t v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; size_t v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; uint8_t v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; size_t v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; uint8_t v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; size_t v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; uint8_t v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v_expectedType_x3f_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v_prio_x3f_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v_name_x3f_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v_prec_x3f_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v_attrs_x3f_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v_doc_x3f_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___x_3559_; uint8_t v___x_3560_; 
v___x_3082_ = lean_unsigned_to_nat(0u);
v___x_3559_ = l_Lean_Syntax_getArg(v_x_3033_, v___x_3082_);
v___x_3560_ = l_Lean_Syntax_isNone(v___x_3559_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3561_; uint8_t v___x_3562_; 
v___x_3561_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3559_);
v___x_3562_ = l_Lean_Syntax_matchesNull(v___x_3559_, v___x_3561_);
if (v___x_3562_ == 0)
{
lean_object* v___x_3563_; 
lean_dec(v___x_3559_);
lean_dec(v_x_3033_);
v___x_3563_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3563_;
}
else
{
lean_object* v_doc_x3f_3564_; 
v_doc_x3f_3564_ = l_Lean_Syntax_getArg(v___x_3559_, v___x_3082_);
lean_dec(v___x_3559_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3567_; uint8_t v___x_3568_; 
v___x_3567_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7));
lean_inc(v_doc_x3f_3564_);
v___x_3568_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3564_, v___x_3567_);
if (v___x_3568_ == 0)
{
lean_object* v___x_3569_; 
lean_dec(v_doc_x3f_3564_);
lean_dec(v_x_3033_);
v___x_3569_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3569_;
}
else
{
goto v___jp_3565_;
}
}
else
{
goto v___jp_3565_;
}
v___jp_3565_:
{
lean_object* v___x_3566_; 
v___x_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3566_, 0, v_doc_x3f_3564_);
v_doc_x3f_3543_ = v___x_3566_;
v___y_3544_ = v_a_3034_;
v___y_3545_ = v_a_3035_;
goto v___jp_3542_;
}
}
}
else
{
lean_object* v___x_3570_; 
lean_dec(v___x_3559_);
v___x_3570_ = lean_box(0);
v_doc_x3f_3543_ = v___x_3570_;
v___y_3544_ = v_a_3034_;
v___y_3545_ = v_a_3035_;
goto v___jp_3542_;
}
v___jp_3083_:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
lean_inc_ref_n(v___y_3089_, 2);
v___x_3100_ = l_Array_append___redArg(v___y_3089_, v___y_3099_);
lean_dec_ref(v___y_3099_);
lean_inc_n(v___y_3086_, 3);
lean_inc_n(v___y_3088_, 6);
v___x_3101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3101_, 0, v___y_3088_);
lean_ctor_set(v___x_3101_, 1, v___y_3086_);
lean_ctor_set(v___x_3101_, 2, v___x_3100_);
v___x_3102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3102_, 0, v___y_3088_);
lean_ctor_set(v___x_3102_, 1, v___y_3086_);
lean_ctor_set(v___x_3102_, 2, v___y_3089_);
lean_inc_ref(v___x_3102_);
lean_inc(v___y_3091_);
v___x_3103_ = l_Lean_Syntax_node1(v___y_3088_, v___y_3091_, v___x_3102_);
lean_inc_ref(v___y_3093_);
v___x_3104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___y_3088_);
lean_ctor_set(v___x_3104_, 1, v___y_3093_);
lean_inc_ref(v___y_3098_);
v___x_3105_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___y_3088_);
lean_ctor_set(v___x_3105_, 1, v___y_3098_);
v___x_3106_ = l_Lean_Syntax_node2(v___y_3088_, v___y_3086_, v___x_3105_, v___y_3092_);
if (lean_obj_tag(v___y_3084_) == 1)
{
lean_object* v_val_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v_val_3107_ = lean_ctor_get(v___y_3084_, 0);
lean_inc(v_val_3107_);
lean_dec_ref_known(v___y_3084_, 1);
v___x_3108_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___y_3088_);
v___x_3109_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___y_3088_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
v___x_3110_ = l_Array_mkArray2___redArg(v___x_3109_, v_val_3107_);
v___y_3040_ = v___y_3085_;
v___y_3041_ = v___x_3101_;
v___y_3042_ = v___y_3086_;
v___y_3043_ = v___y_3087_;
v___y_3044_ = v___y_3088_;
v___y_3045_ = v___x_3106_;
v___y_3046_ = v___y_3090_;
v___y_3047_ = v___y_3089_;
v___y_3048_ = v___x_3103_;
v___y_3049_ = v___x_3104_;
v___y_3050_ = v___y_3094_;
v___y_3051_ = v___x_3102_;
v___y_3052_ = v___y_3095_;
v___y_3053_ = v___y_3096_;
v___y_3054_ = v___y_3097_;
v___y_3055_ = v___x_3110_;
goto v___jp_3039_;
}
else
{
lean_object* v___x_3111_; 
lean_dec(v___y_3084_);
v___x_3111_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3040_ = v___y_3085_;
v___y_3041_ = v___x_3101_;
v___y_3042_ = v___y_3086_;
v___y_3043_ = v___y_3087_;
v___y_3044_ = v___y_3088_;
v___y_3045_ = v___x_3106_;
v___y_3046_ = v___y_3090_;
v___y_3047_ = v___y_3089_;
v___y_3048_ = v___x_3103_;
v___y_3049_ = v___x_3104_;
v___y_3050_ = v___y_3094_;
v___y_3051_ = v___x_3102_;
v___y_3052_ = v___y_3095_;
v___y_3053_ = v___y_3096_;
v___y_3054_ = v___y_3097_;
v___y_3055_ = v___x_3111_;
goto v___jp_3039_;
}
}
v___jp_3112_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3127_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
v___x_3128_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
if (lean_obj_tag(v___y_3121_) == 1)
{
lean_object* v_val_3129_; lean_object* v___x_3130_; 
v_val_3129_ = lean_ctor_get(v___y_3121_, 0);
lean_inc(v_val_3129_);
lean_dec_ref_known(v___y_3121_, 1);
v___x_3130_ = l_Array_mkArray1___redArg(v_val_3129_);
v___y_3084_ = v___y_3113_;
v___y_3085_ = v___y_3114_;
v___y_3086_ = v___y_3115_;
v___y_3087_ = v___x_3128_;
v___y_3088_ = v___y_3116_;
v___y_3089_ = v___y_3117_;
v___y_3090_ = v___y_3118_;
v___y_3091_ = v___y_3119_;
v___y_3092_ = v___y_3120_;
v___y_3093_ = v___x_3127_;
v___y_3094_ = v___y_3122_;
v___y_3095_ = v___y_3123_;
v___y_3096_ = v___y_3124_;
v___y_3097_ = v___y_3125_;
v___y_3098_ = v___y_3126_;
v___y_3099_ = v___x_3130_;
goto v___jp_3083_;
}
else
{
lean_object* v___x_3131_; 
lean_dec(v___y_3121_);
v___x_3131_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3084_ = v___y_3113_;
v___y_3085_ = v___y_3114_;
v___y_3086_ = v___y_3115_;
v___y_3087_ = v___x_3128_;
v___y_3088_ = v___y_3116_;
v___y_3089_ = v___y_3117_;
v___y_3090_ = v___y_3118_;
v___y_3091_ = v___y_3119_;
v___y_3092_ = v___y_3120_;
v___y_3093_ = v___x_3127_;
v___y_3094_ = v___y_3122_;
v___y_3095_ = v___y_3123_;
v___y_3096_ = v___y_3124_;
v___y_3097_ = v___y_3125_;
v___y_3098_ = v___y_3126_;
v___y_3099_ = v___x_3131_;
goto v___jp_3083_;
}
}
v___jp_3132_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; size_t v_sz_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
lean_inc_ref_n(v___y_3141_, 2);
v___x_3156_ = l_Array_append___redArg(v___y_3141_, v___y_3155_);
lean_dec_ref(v___y_3155_);
lean_inc_n(v___y_3136_, 3);
lean_inc_n(v___y_3137_, 9);
v___x_3157_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3157_, 0, v___y_3137_);
lean_ctor_set(v___x_3157_, 1, v___y_3136_);
lean_ctor_set(v___x_3157_, 2, v___x_3156_);
v___x_3158_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
v___x_3159_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
v___x_3160_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___y_3137_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
v___x_3161_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__6));
v___x_3162_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___y_3137_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_3164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___y_3137_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___x_3165_ = l_Nat_reprFast(v___y_3139_);
v___x_3166_ = lean_box(2);
v___x_3167_ = l_Lean_Syntax_mkNumLit(v___x_3165_, v___x_3166_);
v___x_3168_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_3169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___y_3137_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = l_Lean_Syntax_node5(v___y_3137_, v___x_3158_, v___x_3160_, v___x_3162_, v___x_3164_, v___x_3167_, v___x_3169_);
v___x_3171_ = l_Lean_Syntax_node1(v___y_3137_, v___y_3136_, v___x_3170_);
v_sz_3172_ = lean_array_size(v___y_3144_);
v___x_3173_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_3172_, v___y_3138_, v___y_3144_);
v___x_3174_ = l_Array_append___redArg(v___y_3141_, v___x_3173_);
lean_dec_ref(v___x_3173_);
v___x_3175_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3175_, 0, v___y_3137_);
lean_ctor_set(v___x_3175_, 1, v___y_3136_);
lean_ctor_set(v___x_3175_, 2, v___x_3174_);
v___x_3176_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_3177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___y_3137_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = lean_unsigned_to_nat(10u);
v___x_3179_ = lean_mk_empty_array_with_capacity(v___x_3178_);
v___x_3180_ = lean_array_push(v___x_3179_, v___y_3146_);
v___x_3181_ = lean_array_push(v___x_3180_, v___y_3147_);
v___x_3182_ = lean_array_push(v___x_3181_, v___y_3135_);
v___x_3183_ = lean_array_push(v___x_3182_, v___y_3150_);
v___x_3184_ = lean_array_push(v___x_3183_, v___y_3145_);
v___x_3185_ = lean_array_push(v___x_3184_, v___x_3157_);
v___x_3186_ = lean_array_push(v___x_3185_, v___x_3171_);
v___x_3187_ = lean_array_push(v___x_3186_, v___x_3175_);
v___x_3188_ = lean_array_push(v___x_3187_, v___x_3177_);
lean_inc(v___y_3143_);
v___x_3189_ = lean_array_push(v___x_3188_, v___y_3143_);
lean_inc(v___y_3151_);
v___x_3190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3190_, 0, v___y_3137_);
lean_ctor_set(v___x_3190_, 1, v___y_3151_);
lean_ctor_set(v___x_3190_, 2, v___x_3189_);
v___x_3191_ = l_Lean_Elab_Command_elabSyntax(v___x_3190_, v___y_3134_, v___y_3140_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_a_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
lean_inc(v_a_3192_);
lean_dec_ref_known(v___x_3191_, 1);
v___x_3193_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3166_);
lean_ctor_set(v___x_3193_, 1, v_a_3192_);
lean_ctor_set(v___x_3193_, 2, v___y_3153_);
v___x_3194_ = l_Lean_Elab_Command_getRef___redArg(v___y_3134_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
lean_inc(v_a_3195_);
lean_dec_ref_known(v___x_3194_, 1);
v___x_3196_ = l_Lean_SourceInfo_fromRef(v_a_3195_, v___y_3154_);
lean_dec(v_a_3195_);
v___x_3197_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3134_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_quotContext_x3f_3198_; 
lean_dec_ref_known(v___x_3197_, 1);
v_quotContext_x3f_3198_ = lean_ctor_get(v___y_3134_, 5);
if (lean_obj_tag(v_quotContext_x3f_3198_) == 0)
{
lean_object* v___x_3199_; 
v___x_3199_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3140_);
lean_dec_ref(v___x_3199_);
v___y_3113_ = v___y_3133_;
v___y_3114_ = v___y_3134_;
v___y_3115_ = v___y_3136_;
v___y_3116_ = v___x_3196_;
v___y_3117_ = v___y_3141_;
v___y_3118_ = v___y_3140_;
v___y_3119_ = v___y_3142_;
v___y_3120_ = v___y_3143_;
v___y_3121_ = v___y_3148_;
v___y_3122_ = v___x_3193_;
v___y_3123_ = v___y_3149_;
v___y_3124_ = v___y_3152_;
v___y_3125_ = v___x_3168_;
v___y_3126_ = v___x_3176_;
goto v___jp_3112_;
}
else
{
v___y_3113_ = v___y_3133_;
v___y_3114_ = v___y_3134_;
v___y_3115_ = v___y_3136_;
v___y_3116_ = v___x_3196_;
v___y_3117_ = v___y_3141_;
v___y_3118_ = v___y_3140_;
v___y_3119_ = v___y_3142_;
v___y_3120_ = v___y_3143_;
v___y_3121_ = v___y_3148_;
v___y_3122_ = v___x_3193_;
v___y_3123_ = v___y_3149_;
v___y_3124_ = v___y_3152_;
v___y_3125_ = v___x_3168_;
v___y_3126_ = v___x_3176_;
goto v___jp_3112_;
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec(v___x_3196_);
lean_dec_ref_known(v___x_3193_, 3);
lean_dec(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec(v___y_3143_);
lean_dec(v___y_3133_);
v_a_3200_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3197_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3197_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_dec_ref_known(v___x_3193_, 3);
lean_dec(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec(v___y_3143_);
lean_dec(v___y_3133_);
v_a_3208_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3194_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3194_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec(v___y_3143_);
lean_dec(v___y_3133_);
v_a_3216_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3191_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3191_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
v___jp_3224_:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
lean_inc_ref(v___y_3232_);
v___x_3248_ = l_Array_append___redArg(v___y_3232_, v___y_3247_);
lean_dec_ref(v___y_3247_);
lean_inc(v___y_3228_);
lean_inc(v___y_3229_);
v___x_3249_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3249_, 0, v___y_3229_);
lean_ctor_set(v___x_3249_, 1, v___y_3228_);
lean_ctor_set(v___x_3249_, 2, v___x_3248_);
if (lean_obj_tag(v___y_3239_) == 1)
{
lean_object* v_val_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v_val_3250_ = lean_ctor_get(v___y_3239_, 0);
lean_inc(v_val_3250_);
lean_dec_ref_known(v___y_3239_, 1);
v___x_3251_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
v___x_3252_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc_n(v___y_3229_, 5);
v___x_3253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___y_3229_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
v___x_3254_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__9));
v___x_3255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___y_3229_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_3257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___y_3229_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
v___x_3258_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_3259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___y_3229_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
v___x_3260_ = l_Lean_Syntax_node5(v___y_3229_, v___x_3251_, v___x_3253_, v___x_3255_, v___x_3257_, v_val_3250_, v___x_3259_);
v___x_3261_ = l_Array_mkArray1___redArg(v___x_3260_);
v___y_3133_ = v___y_3225_;
v___y_3134_ = v___y_3226_;
v___y_3135_ = v___y_3227_;
v___y_3136_ = v___y_3228_;
v___y_3137_ = v___y_3229_;
v___y_3138_ = v___y_3230_;
v___y_3139_ = v___y_3231_;
v___y_3140_ = v___y_3233_;
v___y_3141_ = v___y_3232_;
v___y_3142_ = v___y_3234_;
v___y_3143_ = v___y_3235_;
v___y_3144_ = v___y_3236_;
v___y_3145_ = v___x_3249_;
v___y_3146_ = v___y_3238_;
v___y_3147_ = v___y_3237_;
v___y_3148_ = v___y_3240_;
v___y_3149_ = v___y_3242_;
v___y_3150_ = v___y_3241_;
v___y_3151_ = v___y_3243_;
v___y_3152_ = v___y_3245_;
v___y_3153_ = v___y_3244_;
v___y_3154_ = v___y_3246_;
v___y_3155_ = v___x_3261_;
goto v___jp_3132_;
}
else
{
lean_object* v___x_3262_; 
lean_dec(v___y_3239_);
v___x_3262_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3133_ = v___y_3225_;
v___y_3134_ = v___y_3226_;
v___y_3135_ = v___y_3227_;
v___y_3136_ = v___y_3228_;
v___y_3137_ = v___y_3229_;
v___y_3138_ = v___y_3230_;
v___y_3139_ = v___y_3231_;
v___y_3140_ = v___y_3233_;
v___y_3141_ = v___y_3232_;
v___y_3142_ = v___y_3234_;
v___y_3143_ = v___y_3235_;
v___y_3144_ = v___y_3236_;
v___y_3145_ = v___x_3249_;
v___y_3146_ = v___y_3238_;
v___y_3147_ = v___y_3237_;
v___y_3148_ = v___y_3240_;
v___y_3149_ = v___y_3242_;
v___y_3150_ = v___y_3241_;
v___y_3151_ = v___y_3243_;
v___y_3152_ = v___y_3245_;
v___y_3153_ = v___y_3244_;
v___y_3154_ = v___y_3246_;
v___y_3155_ = v___x_3262_;
goto v___jp_3132_;
}
}
v___jp_3263_:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
lean_inc_ref(v___y_3272_);
v___x_3288_ = l_Array_append___redArg(v___y_3272_, v___y_3287_);
lean_dec_ref(v___y_3287_);
lean_inc(v___y_3267_);
lean_inc(v___y_3268_);
v___x_3289_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3289_, 0, v___y_3268_);
lean_ctor_set(v___x_3289_, 1, v___y_3267_);
lean_ctor_set(v___x_3289_, 2, v___x_3288_);
v___x_3290_ = l_Lean_SourceInfo_fromRef(v___y_3277_, v___x_3080_);
lean_dec(v___y_3277_);
lean_inc_ref(v___y_3279_);
v___x_3291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3290_);
lean_ctor_set(v___x_3291_, 1, v___y_3279_);
if (lean_obj_tag(v___y_3271_) == 1)
{
lean_object* v_val_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v_val_3292_ = lean_ctor_get(v___y_3271_, 0);
lean_inc(v_val_3292_);
lean_dec_ref_known(v___y_3271_, 1);
v___x_3293_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
v___x_3294_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc_n(v___y_3268_, 2);
v___x_3295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___y_3268_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
v___x_3296_ = l_Lean_Syntax_node2(v___y_3268_, v___x_3293_, v___x_3295_, v_val_3292_);
v___x_3297_ = l_Array_mkArray1___redArg(v___x_3296_);
v___y_3225_ = v___y_3264_;
v___y_3226_ = v___y_3265_;
v___y_3227_ = v___y_3266_;
v___y_3228_ = v___y_3267_;
v___y_3229_ = v___y_3268_;
v___y_3230_ = v___y_3269_;
v___y_3231_ = v___y_3270_;
v___y_3232_ = v___y_3272_;
v___y_3233_ = v___y_3273_;
v___y_3234_ = v___y_3275_;
v___y_3235_ = v___y_3274_;
v___y_3236_ = v___y_3276_;
v___y_3237_ = v___x_3289_;
v___y_3238_ = v___y_3278_;
v___y_3239_ = v___y_3280_;
v___y_3240_ = v___y_3281_;
v___y_3241_ = v___x_3291_;
v___y_3242_ = v___y_3282_;
v___y_3243_ = v___y_3283_;
v___y_3244_ = v___y_3285_;
v___y_3245_ = v___y_3284_;
v___y_3246_ = v___y_3286_;
v___y_3247_ = v___x_3297_;
goto v___jp_3224_;
}
else
{
lean_object* v___x_3298_; 
lean_dec(v___y_3271_);
v___x_3298_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3225_ = v___y_3264_;
v___y_3226_ = v___y_3265_;
v___y_3227_ = v___y_3266_;
v___y_3228_ = v___y_3267_;
v___y_3229_ = v___y_3268_;
v___y_3230_ = v___y_3269_;
v___y_3231_ = v___y_3270_;
v___y_3232_ = v___y_3272_;
v___y_3233_ = v___y_3273_;
v___y_3234_ = v___y_3275_;
v___y_3235_ = v___y_3274_;
v___y_3236_ = v___y_3276_;
v___y_3237_ = v___x_3289_;
v___y_3238_ = v___y_3278_;
v___y_3239_ = v___y_3280_;
v___y_3240_ = v___y_3281_;
v___y_3241_ = v___x_3291_;
v___y_3242_ = v___y_3282_;
v___y_3243_ = v___y_3283_;
v___y_3244_ = v___y_3285_;
v___y_3245_ = v___y_3284_;
v___y_3246_ = v___y_3286_;
v___y_3247_ = v___x_3298_;
goto v___jp_3224_;
}
}
v___jp_3299_:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
lean_inc_ref(v___y_3307_);
v___x_3324_ = l_Array_append___redArg(v___y_3307_, v___y_3323_);
lean_dec_ref(v___y_3323_);
lean_inc(v___y_3303_);
lean_inc(v___y_3304_);
v___x_3325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3325_, 0, v___y_3304_);
lean_ctor_set(v___x_3325_, 1, v___y_3303_);
lean_ctor_set(v___x_3325_, 2, v___x_3324_);
if (lean_obj_tag(v___y_3322_) == 1)
{
lean_object* v_val_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v_val_3326_ = lean_ctor_get(v___y_3322_, 0);
lean_inc(v_val_3326_);
lean_dec_ref_known(v___y_3322_, 1);
v___x_3327_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(v___y_3320_);
v___x_3328_ = l_Lean_Name_mkStr4(v___x_3037_, v___x_3038_, v___y_3320_, v___x_3327_);
v___x_3329_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc_n(v___y_3304_, 4);
v___x_3330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___y_3304_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
lean_inc_ref(v___y_3307_);
v___x_3331_ = l_Array_append___redArg(v___y_3307_, v_val_3326_);
lean_dec(v_val_3326_);
lean_inc(v___y_3303_);
v___x_3332_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3332_, 0, v___y_3304_);
lean_ctor_set(v___x_3332_, 1, v___y_3303_);
lean_ctor_set(v___x_3332_, 2, v___x_3331_);
v___x_3333_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_3334_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___y_3304_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
v___x_3335_ = l_Lean_Syntax_node3(v___y_3304_, v___x_3328_, v___x_3330_, v___x_3332_, v___x_3334_);
v___x_3336_ = l_Array_mkArray1___redArg(v___x_3335_);
v___y_3264_ = v___y_3300_;
v___y_3265_ = v___y_3301_;
v___y_3266_ = v___y_3302_;
v___y_3267_ = v___y_3303_;
v___y_3268_ = v___y_3304_;
v___y_3269_ = v___y_3305_;
v___y_3270_ = v___y_3306_;
v___y_3271_ = v___y_3308_;
v___y_3272_ = v___y_3307_;
v___y_3273_ = v___y_3309_;
v___y_3274_ = v___y_3310_;
v___y_3275_ = v___y_3311_;
v___y_3276_ = v___y_3313_;
v___y_3277_ = v___y_3312_;
v___y_3278_ = v___x_3325_;
v___y_3279_ = v___y_3314_;
v___y_3280_ = v___y_3315_;
v___y_3281_ = v___y_3316_;
v___y_3282_ = v___y_3317_;
v___y_3283_ = v___y_3318_;
v___y_3284_ = v___y_3320_;
v___y_3285_ = v___y_3319_;
v___y_3286_ = v___y_3321_;
v___y_3287_ = v___x_3336_;
goto v___jp_3263_;
}
else
{
lean_object* v___x_3337_; 
lean_dec(v___y_3322_);
v___x_3337_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3264_ = v___y_3300_;
v___y_3265_ = v___y_3301_;
v___y_3266_ = v___y_3302_;
v___y_3267_ = v___y_3303_;
v___y_3268_ = v___y_3304_;
v___y_3269_ = v___y_3305_;
v___y_3270_ = v___y_3306_;
v___y_3271_ = v___y_3308_;
v___y_3272_ = v___y_3307_;
v___y_3273_ = v___y_3309_;
v___y_3274_ = v___y_3310_;
v___y_3275_ = v___y_3311_;
v___y_3276_ = v___y_3313_;
v___y_3277_ = v___y_3312_;
v___y_3278_ = v___x_3325_;
v___y_3279_ = v___y_3314_;
v___y_3280_ = v___y_3315_;
v___y_3281_ = v___y_3316_;
v___y_3282_ = v___y_3317_;
v___y_3283_ = v___y_3318_;
v___y_3284_ = v___y_3320_;
v___y_3285_ = v___y_3319_;
v___y_3286_ = v___y_3321_;
v___y_3287_ = v___x_3337_;
goto v___jp_3263_;
}
}
v___jp_3338_:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3358_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__12));
v___x_3359_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__13));
v___x_3360_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_3361_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v___y_3352_) == 1)
{
lean_object* v_val_3362_; lean_object* v___x_3363_; 
v_val_3362_ = lean_ctor_get(v___y_3352_, 0);
lean_inc(v_val_3362_);
v___x_3363_ = l_Array_mkArray1___redArg(v_val_3362_);
v___y_3300_ = v___y_3339_;
v___y_3301_ = v___y_3340_;
v___y_3302_ = v___y_3341_;
v___y_3303_ = v___x_3360_;
v___y_3304_ = v___y_3342_;
v___y_3305_ = v___y_3343_;
v___y_3306_ = v___y_3344_;
v___y_3307_ = v___x_3361_;
v___y_3308_ = v___y_3345_;
v___y_3309_ = v___y_3346_;
v___y_3310_ = v___y_3347_;
v___y_3311_ = v___y_3348_;
v___y_3312_ = v___y_3349_;
v___y_3313_ = v___y_3350_;
v___y_3314_ = v___x_3358_;
v___y_3315_ = v___y_3351_;
v___y_3316_ = v___y_3352_;
v___y_3317_ = v___y_3353_;
v___y_3318_ = v___x_3359_;
v___y_3319_ = v___y_3355_;
v___y_3320_ = v___y_3354_;
v___y_3321_ = v___y_3356_;
v___y_3322_ = v___y_3357_;
v___y_3323_ = v___x_3363_;
goto v___jp_3299_;
}
else
{
lean_object* v___x_3364_; 
v___x_3364_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___y_3300_ = v___y_3339_;
v___y_3301_ = v___y_3340_;
v___y_3302_ = v___y_3341_;
v___y_3303_ = v___x_3360_;
v___y_3304_ = v___y_3342_;
v___y_3305_ = v___y_3343_;
v___y_3306_ = v___y_3344_;
v___y_3307_ = v___x_3361_;
v___y_3308_ = v___y_3345_;
v___y_3309_ = v___y_3346_;
v___y_3310_ = v___y_3347_;
v___y_3311_ = v___y_3348_;
v___y_3312_ = v___y_3349_;
v___y_3313_ = v___y_3350_;
v___y_3314_ = v___x_3358_;
v___y_3315_ = v___y_3351_;
v___y_3316_ = v___y_3352_;
v___y_3317_ = v___y_3353_;
v___y_3318_ = v___x_3359_;
v___y_3319_ = v___y_3355_;
v___y_3320_ = v___y_3354_;
v___y_3321_ = v___y_3356_;
v___y_3322_ = v___y_3357_;
v___y_3323_ = v___x_3364_;
goto v___jp_3299_;
}
}
v___jp_3365_:
{
lean_object* v___x_3382_; lean_object* v_args_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3382_ = l_Lean_Syntax_getArg(v___y_3376_, v___y_3374_);
lean_dec(v___y_3376_);
v_args_3383_ = l_Lean_Syntax_getArgs(v___y_3377_);
lean_dec(v___y_3377_);
v___x_3384_ = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(v___x_3384_, 0, v___y_3373_);
v___x_3385_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v___x_3384_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; size_t v_sz_3387_; size_t v___x_3388_; lean_object* v___x_3389_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3386_);
lean_dec_ref_known(v___x_3385_, 1);
v_sz_3387_ = lean_array_size(v_args_3383_);
v___x_3388_ = ((size_t)0ULL);
v___x_3389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_3387_, v___x_3388_, v_args_3383_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3390_; lean_object* v___x_3391_; lean_object* v_fst_3392_; lean_object* v_snd_3393_; lean_object* v___x_3394_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3390_);
lean_dec_ref_known(v___x_3389_, 1);
v___x_3391_ = l_Array_unzip___redArg(v_a_3390_);
lean_dec(v_a_3390_);
v_fst_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_fst_3392_);
v_snd_3393_ = lean_ctor_get(v___x_3391_, 1);
lean_inc(v_snd_3393_);
lean_dec_ref(v___x_3391_);
v___x_3394_ = l_Lean_Elab_Command_getRef___redArg(v___y_3380_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; uint8_t v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3395_);
lean_dec_ref_known(v___x_3394_, 1);
v___x_3396_ = 0;
v___x_3397_ = l_Lean_SourceInfo_fromRef(v_a_3395_, v___x_3396_);
lean_dec(v_a_3395_);
v___x_3398_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3380_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_quotContext_x3f_3399_; 
lean_dec_ref_known(v___x_3398_, 1);
v_quotContext_x3f_3399_ = lean_ctor_get(v___y_3380_, 5);
if (lean_obj_tag(v_quotContext_x3f_3399_) == 0)
{
lean_object* v___x_3400_; 
v___x_3400_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3381_);
lean_dec_ref(v___x_3400_);
v___y_3339_ = v_expectedType_x3f_3379_;
v___y_3340_ = v___y_3380_;
v___y_3341_ = v___y_3366_;
v___y_3342_ = v___x_3397_;
v___y_3343_ = v___x_3388_;
v___y_3344_ = v_a_3386_;
v___y_3345_ = v___y_3367_;
v___y_3346_ = v___y_3381_;
v___y_3347_ = v___y_3368_;
v___y_3348_ = v___y_3369_;
v___y_3349_ = v___y_3370_;
v___y_3350_ = v_fst_3392_;
v___y_3351_ = v___y_3371_;
v___y_3352_ = v___y_3372_;
v___y_3353_ = v___x_3382_;
v___y_3354_ = v___y_3375_;
v___y_3355_ = v_snd_3393_;
v___y_3356_ = v___x_3396_;
v___y_3357_ = v___y_3378_;
goto v___jp_3338_;
}
else
{
v___y_3339_ = v_expectedType_x3f_3379_;
v___y_3340_ = v___y_3380_;
v___y_3341_ = v___y_3366_;
v___y_3342_ = v___x_3397_;
v___y_3343_ = v___x_3388_;
v___y_3344_ = v_a_3386_;
v___y_3345_ = v___y_3367_;
v___y_3346_ = v___y_3381_;
v___y_3347_ = v___y_3368_;
v___y_3348_ = v___y_3369_;
v___y_3349_ = v___y_3370_;
v___y_3350_ = v_fst_3392_;
v___y_3351_ = v___y_3371_;
v___y_3352_ = v___y_3372_;
v___y_3353_ = v___x_3382_;
v___y_3354_ = v___y_3375_;
v___y_3355_ = v_snd_3393_;
v___y_3356_ = v___x_3396_;
v___y_3357_ = v___y_3378_;
goto v___jp_3338_;
}
}
else
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_dec(v___x_3397_);
lean_dec(v_snd_3393_);
lean_dec(v_fst_3392_);
lean_dec(v_a_3386_);
lean_dec(v___x_3382_);
lean_dec(v_expectedType_x3f_3379_);
lean_dec(v___y_3378_);
lean_dec(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v___y_3366_);
v_a_3401_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3398_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3398_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3401_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec(v_snd_3393_);
lean_dec(v_fst_3392_);
lean_dec(v_a_3386_);
lean_dec(v___x_3382_);
lean_dec(v_expectedType_x3f_3379_);
lean_dec(v___y_3378_);
lean_dec(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v___y_3366_);
v_a_3409_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3394_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3394_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_dec(v_a_3386_);
lean_dec(v___x_3382_);
lean_dec(v_expectedType_x3f_3379_);
lean_dec(v___y_3378_);
lean_dec(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v___y_3366_);
v_a_3417_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3389_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3389_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
lean_dec_ref(v_args_3383_);
lean_dec(v___x_3382_);
lean_dec(v_expectedType_x3f_3379_);
lean_dec(v___y_3378_);
lean_dec(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v___y_3366_);
v_a_3425_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3385_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3385_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
v___jp_3433_:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; uint8_t v___x_3451_; 
v___x_3448_ = lean_unsigned_to_nat(8u);
v___x_3449_ = l_Lean_Syntax_getArg(v_x_3033_, v___x_3448_);
v___x_3450_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__15));
lean_inc(v___x_3449_);
v___x_3451_ = l_Lean_Syntax_isOfKind(v___x_3449_, v___x_3450_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3452_; 
lean_dec(v___x_3449_);
lean_dec(v_prio_x3f_3445_);
lean_dec(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec(v___y_3441_);
lean_dec(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec(v_x_3033_);
v___x_3452_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3452_;
}
else
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; uint8_t v___x_3457_; 
v___x_3453_ = lean_unsigned_to_nat(7u);
v___x_3454_ = l_Lean_Syntax_getArg(v_x_3033_, v___x_3453_);
lean_dec(v_x_3033_);
v___x_3455_ = l_Lean_Syntax_getArg(v___x_3449_, v___y_3439_);
v___x_3456_ = l_Lean_Syntax_getArg(v___x_3449_, v___y_3434_);
v___x_3457_ = l_Lean_Syntax_isNone(v___x_3456_);
if (v___x_3457_ == 0)
{
uint8_t v___x_3458_; 
lean_inc(v___x_3456_);
v___x_3458_ = l_Lean_Syntax_matchesNull(v___x_3456_, v___y_3434_);
if (v___x_3458_ == 0)
{
lean_object* v___x_3459_; 
lean_dec(v___x_3456_);
lean_dec(v___x_3455_);
lean_dec(v___x_3454_);
lean_dec(v___x_3449_);
lean_dec(v_prio_x3f_3445_);
lean_dec(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec(v___y_3441_);
lean_dec(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec(v___y_3435_);
v___x_3459_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3459_;
}
else
{
lean_object* v_expectedType_x3f_3460_; lean_object* v___x_3461_; 
v_expectedType_x3f_3460_ = l_Lean_Syntax_getArg(v___x_3456_, v___y_3439_);
lean_dec(v___x_3456_);
v___x_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3461_, 0, v_expectedType_x3f_3460_);
v___y_3366_ = v___y_3436_;
v___y_3367_ = v___y_3441_;
v___y_3368_ = v___x_3455_;
v___y_3369_ = v___y_3442_;
v___y_3370_ = v___y_3444_;
v___y_3371_ = v___y_3435_;
v___y_3372_ = v___y_3437_;
v___y_3373_ = v_prio_x3f_3445_;
v___y_3374_ = v___y_3438_;
v___y_3375_ = v___y_3440_;
v___y_3376_ = v___x_3449_;
v___y_3377_ = v___x_3454_;
v___y_3378_ = v___y_3443_;
v_expectedType_x3f_3379_ = v___x_3461_;
v___y_3380_ = v___y_3446_;
v___y_3381_ = v___y_3447_;
goto v___jp_3365_;
}
}
else
{
lean_object* v___x_3462_; 
lean_dec(v___x_3456_);
v___x_3462_ = lean_box(0);
v___y_3366_ = v___y_3436_;
v___y_3367_ = v___y_3441_;
v___y_3368_ = v___x_3455_;
v___y_3369_ = v___y_3442_;
v___y_3370_ = v___y_3444_;
v___y_3371_ = v___y_3435_;
v___y_3372_ = v___y_3437_;
v___y_3373_ = v_prio_x3f_3445_;
v___y_3374_ = v___y_3438_;
v___y_3375_ = v___y_3440_;
v___y_3376_ = v___x_3449_;
v___y_3377_ = v___x_3454_;
v___y_3378_ = v___y_3443_;
v_expectedType_x3f_3379_ = v___x_3462_;
v___y_3380_ = v___y_3446_;
v___y_3381_ = v___y_3447_;
goto v___jp_3365_;
}
}
}
v___jp_3463_:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; uint8_t v___x_3480_; 
v___x_3478_ = lean_unsigned_to_nat(6u);
v___x_3479_ = l_Lean_Syntax_getArg(v_x_3033_, v___x_3478_);
v___x_3480_ = l_Lean_Syntax_isNone(v___x_3479_);
if (v___x_3480_ == 0)
{
uint8_t v___x_3481_; 
lean_inc(v___x_3479_);
v___x_3481_ = l_Lean_Syntax_matchesNull(v___x_3479_, v___y_3468_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; 
lean_dec(v___x_3479_);
lean_dec(v_name_x3f_3475_);
lean_dec(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec(v___y_3471_);
lean_dec(v___y_3466_);
lean_dec(v___y_3464_);
lean_dec(v_x_3033_);
v___x_3482_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3482_;
}
else
{
lean_object* v___x_3483_; lean_object* v___x_3484_; uint8_t v___x_3485_; 
v___x_3483_ = l_Lean_Syntax_getArg(v___x_3479_, v___x_3082_);
lean_dec(v___x_3479_);
v___x_3484_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
lean_inc(v___x_3483_);
v___x_3485_ = l_Lean_Syntax_isOfKind(v___x_3483_, v___x_3484_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3486_; 
lean_dec(v___x_3483_);
lean_dec(v_name_x3f_3475_);
lean_dec(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec(v___y_3471_);
lean_dec(v___y_3466_);
lean_dec(v___y_3464_);
lean_dec(v_x_3033_);
v___x_3486_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3486_;
}
else
{
lean_object* v_prio_x3f_3487_; lean_object* v___x_3488_; 
v_prio_x3f_3487_ = l_Lean_Syntax_getArg(v___x_3483_, v___y_3467_);
lean_dec(v___x_3483_);
v___x_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3488_, 0, v_prio_x3f_3487_);
v___y_3434_ = v___y_3465_;
v___y_3435_ = v_name_x3f_3475_;
v___y_3436_ = v___y_3464_;
v___y_3437_ = v___y_3466_;
v___y_3438_ = v___y_3469_;
v___y_3439_ = v___y_3468_;
v___y_3440_ = v___y_3470_;
v___y_3441_ = v___y_3471_;
v___y_3442_ = v___y_3472_;
v___y_3443_ = v___y_3474_;
v___y_3444_ = v___y_3473_;
v_prio_x3f_3445_ = v___x_3488_;
v___y_3446_ = v___y_3476_;
v___y_3447_ = v___y_3477_;
goto v___jp_3433_;
}
}
}
else
{
lean_object* v___x_3489_; 
lean_dec(v___x_3479_);
v___x_3489_ = lean_box(0);
v___y_3434_ = v___y_3465_;
v___y_3435_ = v_name_x3f_3475_;
v___y_3436_ = v___y_3464_;
v___y_3437_ = v___y_3466_;
v___y_3438_ = v___y_3469_;
v___y_3439_ = v___y_3468_;
v___y_3440_ = v___y_3470_;
v___y_3441_ = v___y_3471_;
v___y_3442_ = v___y_3472_;
v___y_3443_ = v___y_3474_;
v___y_3444_ = v___y_3473_;
v_prio_x3f_3445_ = v___x_3489_;
v___y_3446_ = v___y_3476_;
v___y_3447_ = v___y_3477_;
goto v___jp_3433_;
}
}
v___jp_3490_:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
v___x_3504_ = lean_unsigned_to_nat(5u);
v___x_3505_ = l_Lean_Syntax_getArg(v_x_3033_, v___x_3504_);
v___x_3506_ = l_Lean_Syntax_isNone(v___x_3505_);
if (v___x_3506_ == 0)
{
uint8_t v___x_3507_; 
lean_inc(v___x_3505_);
v___x_3507_ = l_Lean_Syntax_matchesNull(v___x_3505_, v___y_3496_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; 
lean_dec(v___x_3505_);
lean_dec(v_prec_x3f_3501_);
lean_dec(v___y_3500_);
lean_dec(v___y_3499_);
lean_dec(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec(v_x_3033_);
v___x_3508_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3508_;
}
else
{
lean_object* v___x_3509_; lean_object* v___x_3510_; uint8_t v___x_3511_; 
v___x_3509_ = l_Lean_Syntax_getArg(v___x_3505_, v___x_3082_);
lean_dec(v___x_3505_);
v___x_3510_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
lean_inc(v___x_3509_);
v___x_3511_ = l_Lean_Syntax_isOfKind(v___x_3509_, v___x_3510_);
if (v___x_3511_ == 0)
{
lean_object* v___x_3512_; 
lean_dec(v___x_3509_);
lean_dec(v_prec_x3f_3501_);
lean_dec(v___y_3500_);
lean_dec(v___y_3499_);
lean_dec(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec(v_x_3033_);
v___x_3512_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3512_;
}
else
{
lean_object* v_name_x3f_3513_; lean_object* v___x_3514_; 
v_name_x3f_3513_ = l_Lean_Syntax_getArg(v___x_3509_, v___y_3494_);
lean_dec(v___x_3509_);
v___x_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3514_, 0, v_name_x3f_3513_);
v___y_3464_ = v___y_3492_;
v___y_3465_ = v___y_3491_;
v___y_3466_ = v___y_3493_;
v___y_3467_ = v___y_3494_;
v___y_3468_ = v___y_3496_;
v___y_3469_ = v___y_3495_;
v___y_3470_ = v___y_3497_;
v___y_3471_ = v_prec_x3f_3501_;
v___y_3472_ = v___y_3498_;
v___y_3473_ = v___y_3500_;
v___y_3474_ = v___y_3499_;
v_name_x3f_3475_ = v___x_3514_;
v___y_3476_ = v___y_3502_;
v___y_3477_ = v___y_3503_;
goto v___jp_3463_;
}
}
}
else
{
lean_object* v___x_3515_; 
lean_dec(v___x_3505_);
v___x_3515_ = lean_box(0);
v___y_3464_ = v___y_3492_;
v___y_3465_ = v___y_3491_;
v___y_3466_ = v___y_3493_;
v___y_3467_ = v___y_3494_;
v___y_3468_ = v___y_3496_;
v___y_3469_ = v___y_3495_;
v___y_3470_ = v___y_3497_;
v___y_3471_ = v_prec_x3f_3501_;
v___y_3472_ = v___y_3498_;
v___y_3473_ = v___y_3500_;
v___y_3474_ = v___y_3499_;
v_name_x3f_3475_ = v___x_3515_;
v___y_3476_ = v___y_3502_;
v___y_3477_ = v___y_3503_;
goto v___jp_3463_;
}
}
v___jp_3516_:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; uint8_t v___x_3526_; 
v___x_3522_ = lean_unsigned_to_nat(2u);
v___x_3523_ = l_Lean_Syntax_getArg(v_x_3033_, v___x_3522_);
v___x_3524_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_3525_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v___x_3523_);
v___x_3526_ = l_Lean_Syntax_isOfKind(v___x_3523_, v___x_3525_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3527_; 
lean_dec(v___x_3523_);
lean_dec(v_attrs_x3f_3519_);
lean_dec(v___y_3517_);
lean_dec(v_x_3033_);
v___x_3527_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3527_;
}
else
{
lean_object* v___x_3528_; lean_object* v_tk_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; uint8_t v___x_3532_; 
v___x_3528_ = lean_unsigned_to_nat(3u);
v_tk_3529_ = l_Lean_Syntax_getArg(v_x_3033_, v___x_3528_);
v___x_3530_ = lean_unsigned_to_nat(4u);
v___x_3531_ = l_Lean_Syntax_getArg(v_x_3033_, v___x_3530_);
v___x_3532_ = l_Lean_Syntax_isNone(v___x_3531_);
if (v___x_3532_ == 0)
{
uint8_t v___x_3533_; 
lean_inc(v___x_3531_);
v___x_3533_ = l_Lean_Syntax_matchesNull(v___x_3531_, v___y_3518_);
if (v___x_3533_ == 0)
{
lean_object* v___x_3534_; 
lean_dec(v___x_3531_);
lean_dec(v_tk_3529_);
lean_dec(v___x_3523_);
lean_dec(v_attrs_x3f_3519_);
lean_dec(v___y_3517_);
lean_dec(v_x_3033_);
v___x_3534_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3534_;
}
else
{
lean_object* v___x_3535_; lean_object* v___x_3536_; uint8_t v___x_3537_; 
v___x_3535_ = l_Lean_Syntax_getArg(v___x_3531_, v___x_3082_);
lean_dec(v___x_3531_);
v___x_3536_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
lean_inc(v___x_3535_);
v___x_3537_ = l_Lean_Syntax_isOfKind(v___x_3535_, v___x_3536_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; 
lean_dec(v___x_3535_);
lean_dec(v_tk_3529_);
lean_dec(v___x_3523_);
lean_dec(v_attrs_x3f_3519_);
lean_dec(v___y_3517_);
lean_dec(v_x_3033_);
v___x_3538_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3538_;
}
else
{
lean_object* v_prec_x3f_3539_; lean_object* v___x_3540_; 
v_prec_x3f_3539_ = l_Lean_Syntax_getArg(v___x_3535_, v___y_3518_);
lean_dec(v___x_3535_);
v___x_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3540_, 0, v_prec_x3f_3539_);
v___y_3491_ = v___x_3522_;
v___y_3492_ = v___x_3523_;
v___y_3493_ = v___y_3517_;
v___y_3494_ = v___x_3528_;
v___y_3495_ = v___x_3530_;
v___y_3496_ = v___y_3518_;
v___y_3497_ = v___x_3524_;
v___y_3498_ = v___x_3525_;
v___y_3499_ = v_attrs_x3f_3519_;
v___y_3500_ = v_tk_3529_;
v_prec_x3f_3501_ = v___x_3540_;
v___y_3502_ = v___y_3520_;
v___y_3503_ = v___y_3521_;
goto v___jp_3490_;
}
}
}
else
{
lean_object* v___x_3541_; 
lean_dec(v___x_3531_);
v___x_3541_ = lean_box(0);
v___y_3491_ = v___x_3522_;
v___y_3492_ = v___x_3523_;
v___y_3493_ = v___y_3517_;
v___y_3494_ = v___x_3528_;
v___y_3495_ = v___x_3530_;
v___y_3496_ = v___y_3518_;
v___y_3497_ = v___x_3524_;
v___y_3498_ = v___x_3525_;
v___y_3499_ = v_attrs_x3f_3519_;
v___y_3500_ = v_tk_3529_;
v_prec_x3f_3501_ = v___x_3541_;
v___y_3502_ = v___y_3520_;
v___y_3503_ = v___y_3521_;
goto v___jp_3490_;
}
}
}
v___jp_3542_:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; 
v___x_3546_ = lean_unsigned_to_nat(1u);
v___x_3547_ = l_Lean_Syntax_getArg(v_x_3033_, v___x_3546_);
v___x_3548_ = l_Lean_Syntax_isNone(v___x_3547_);
if (v___x_3548_ == 0)
{
uint8_t v___x_3549_; 
lean_inc(v___x_3547_);
v___x_3549_ = l_Lean_Syntax_matchesNull(v___x_3547_, v___x_3546_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3550_; 
lean_dec(v___x_3547_);
lean_dec(v_doc_x3f_3543_);
lean_dec(v_x_3033_);
v___x_3550_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3550_;
}
else
{
lean_object* v___x_3551_; lean_object* v___x_3552_; uint8_t v___x_3553_; 
v___x_3551_ = l_Lean_Syntax_getArg(v___x_3547_, v___x_3082_);
lean_dec(v___x_3547_);
v___x_3552_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5));
lean_inc(v___x_3551_);
v___x_3553_ = l_Lean_Syntax_isOfKind(v___x_3551_, v___x_3552_);
if (v___x_3553_ == 0)
{
lean_object* v___x_3554_; 
lean_dec(v___x_3551_);
lean_dec(v_doc_x3f_3543_);
lean_dec(v_x_3033_);
v___x_3554_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3554_;
}
else
{
lean_object* v___x_3555_; lean_object* v_attrs_x3f_3556_; lean_object* v___x_3557_; 
v___x_3555_ = l_Lean_Syntax_getArg(v___x_3551_, v___x_3546_);
lean_dec(v___x_3551_);
v_attrs_x3f_3556_ = l_Lean_Syntax_getArgs(v___x_3555_);
lean_dec(v___x_3555_);
v___x_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3557_, 0, v_attrs_x3f_3556_);
v___y_3517_ = v_doc_x3f_3543_;
v___y_3518_ = v___x_3546_;
v_attrs_x3f_3519_ = v___x_3557_;
v___y_3520_ = v___y_3544_;
v___y_3521_ = v___y_3545_;
goto v___jp_3516_;
}
}
}
else
{
lean_object* v___x_3558_; 
lean_dec(v___x_3547_);
v___x_3558_ = lean_box(0);
v___y_3517_ = v_doc_x3f_3543_;
v___y_3518_ = v___x_3546_;
v_attrs_x3f_3519_ = v___x_3558_;
v___y_3520_ = v___y_3544_;
v___y_3521_ = v___y_3545_;
goto v___jp_3516_;
}
}
}
v___jp_3039_:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
lean_inc_ref(v___y_3047_);
v___x_3056_ = l_Array_append___redArg(v___y_3047_, v___y_3055_);
lean_dec_ref(v___y_3055_);
lean_inc_n(v___y_3042_, 4);
lean_inc_n(v___y_3044_, 11);
v___x_3057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3057_, 0, v___y_3044_);
lean_ctor_set(v___x_3057_, 1, v___y_3042_);
lean_ctor_set(v___x_3057_, 2, v___x_3056_);
v___x_3058_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc_ref_n(v___y_3053_, 3);
v___x_3059_ = l_Lean_Name_mkStr4(v___x_3037_, v___x_3038_, v___y_3053_, v___x_3058_);
v___x_3060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_3061_ = l_Lean_Name_mkStr4(v___x_3037_, v___x_3038_, v___y_3053_, v___x_3060_);
v___x_3062_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_3063_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___y_3044_);
lean_ctor_set(v___x_3063_, 1, v___x_3062_);
v___x_3064_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__0));
v___x_3065_ = l_Lean_Name_mkStr4(v___x_3037_, v___x_3038_, v___y_3053_, v___x_3064_);
v___x_3066_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__1));
v___x_3067_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___y_3044_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
lean_inc_ref(v___y_3054_);
v___x_3068_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___y_3044_);
lean_ctor_set(v___x_3068_, 1, v___y_3054_);
v___x_3069_ = l_Lean_Syntax_node3(v___y_3044_, v___x_3065_, v___x_3067_, v___y_3050_, v___x_3068_);
v___x_3070_ = l_Lean_Syntax_node1(v___y_3044_, v___y_3042_, v___x_3069_);
v___x_3071_ = l_Lean_Syntax_node1(v___y_3044_, v___y_3042_, v___x_3070_);
v___x_3072_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_3073_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___y_3044_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
v___x_3074_ = l_Lean_Syntax_node4(v___y_3044_, v___x_3061_, v___x_3063_, v___x_3071_, v___x_3073_, v___y_3052_);
v___x_3075_ = l_Lean_Syntax_node1(v___y_3044_, v___y_3042_, v___x_3074_);
v___x_3076_ = l_Lean_Syntax_node1(v___y_3044_, v___x_3059_, v___x_3075_);
lean_inc(v___y_3051_);
lean_inc(v___y_3043_);
v___x_3077_ = l_Lean_Syntax_node8(v___y_3044_, v___y_3043_, v___y_3041_, v___y_3051_, v___y_3048_, v___y_3049_, v___y_3051_, v___y_3045_, v___x_3057_, v___x_3076_);
v___x_3078_ = l_Lean_Elab_Command_elabCommand(v___x_3077_, v___y_3040_, v___y_3046_);
return v___x_3078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___boxed(lean_object* v_x_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_Lean_Elab_Command_elabElab(v_x_3571_, v_a_3572_, v_a_3573_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(lean_object* v_00_u03b1_3576_, lean_object* v_x_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v___x_3580_; 
v___x_3580_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_3577_, v___y_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3581_, lean_object* v_x_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(v_00_u03b1_3581_, v_x_3582_, v___y_3583_, v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec_ref(v_x_3582_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(lean_object* v_00_u03b1_3586_, lean_object* v_ref_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v___x_3591_; 
v___x_3591_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_3587_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___boxed(lean_object* v_00_u03b1_3592_, lean_object* v_ref_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(v_00_u03b1_3592_, v_ref_3593_, v___y_3594_, v___y_3595_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(lean_object* v_00_u03b1_3598_, lean_object* v_x_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_3599_, v___y_3600_, v___y_3601_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___boxed(lean_object* v_00_u03b1_3604_, lean_object* v_x_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(v_00_u03b1_3604_, v_x_3605_, v___y_3606_, v___y_3607_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(lean_object* v_as_3610_, lean_object* v_as_x27_3611_, lean_object* v_b_3612_, lean_object* v_a_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
lean_object* v___x_3617_; 
v___x_3617_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_3611_, v_b_3612_, v___y_3614_, v___y_3615_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___boxed(lean_object* v_as_3618_, lean_object* v_as_x27_3619_, lean_object* v_b_3620_, lean_object* v_a_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(v_as_3618_, v_as_x27_3619_, v_b_3620_, v_a_3621_, v___y_3622_, v___y_3623_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec(v_as_x27_3619_);
lean_dec(v_as_3618_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3626_, lean_object* v_m_3627_, lean_object* v_a_3628_){
_start:
{
lean_object* v___x_3629_; 
v___x_3629_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_3627_, v_a_3628_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3630_, lean_object* v_m_3631_, lean_object* v_a_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(v_00_u03b2_3630_, v_m_3631_, v_a_3632_);
lean_dec(v_a_3632_);
lean_dec_ref(v_m_3631_);
return v_res_3633_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_3634_, lean_object* v_x_3635_, lean_object* v_x_3636_){
_start:
{
uint8_t v___x_3637_; 
v___x_3637_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_3635_, v_x_3636_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3638_, lean_object* v_x_3639_, lean_object* v_x_3640_){
_start:
{
uint8_t v_res_3641_; lean_object* v_r_3642_; 
v_res_3641_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(v_00_u03b2_3638_, v_x_3639_, v_x_3640_);
lean_dec_ref(v_x_3640_);
lean_dec_ref(v_x_3639_);
v_r_3642_ = lean_box(v_res_3641_);
return v_r_3642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_3643_, lean_object* v_a_3644_, lean_object* v_x_3645_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_3644_, v_x_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___boxed(lean_object* v_00_u03b2_3647_, lean_object* v_a_3648_, lean_object* v_x_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(v_00_u03b2_3647_, v_a_3648_, v_x_3649_);
lean_dec(v_x_3649_);
lean_dec(v_a_3648_);
return v_res_3650_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(lean_object* v_00_u03b2_3651_, lean_object* v_x_3652_, size_t v_x_3653_, lean_object* v_x_3654_){
_start:
{
uint8_t v___x_3655_; 
v___x_3655_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_3652_, v_x_3653_, v_x_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3656_, lean_object* v_x_3657_, lean_object* v_x_3658_, lean_object* v_x_3659_){
_start:
{
size_t v_x_19034__boxed_3660_; uint8_t v_res_3661_; lean_object* v_r_3662_; 
v_x_19034__boxed_3660_ = lean_unbox_usize(v_x_3658_);
lean_dec(v_x_3658_);
v_res_3661_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(v_00_u03b2_3656_, v_x_3657_, v_x_19034__boxed_3660_, v_x_3659_);
lean_dec_ref(v_x_3659_);
lean_dec_ref(v_x_3657_);
v_r_3662_ = lean_box(v_res_3661_);
return v_r_3662_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(lean_object* v_00_u03b2_3663_, lean_object* v_keys_3664_, lean_object* v_vals_3665_, lean_object* v_heq_3666_, lean_object* v_i_3667_, lean_object* v_k_3668_){
_start:
{
uint8_t v___x_3669_; 
v___x_3669_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_3664_, v_i_3667_, v_k_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___boxed(lean_object* v_00_u03b2_3670_, lean_object* v_keys_3671_, lean_object* v_vals_3672_, lean_object* v_heq_3673_, lean_object* v_i_3674_, lean_object* v_k_3675_){
_start:
{
uint8_t v_res_3676_; lean_object* v_r_3677_; 
v_res_3676_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(v_00_u03b2_3670_, v_keys_3671_, v_vals_3672_, v_heq_3673_, v_i_3674_, v_k_3675_);
lean_dec_ref(v_k_3675_);
lean_dec_ref(v_vals_3672_);
lean_dec_ref(v_keys_3671_);
v_r_3677_ = lean_box(v_res_3676_);
return v_r_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1(){
_start:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3685_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3686_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
v___x_3687_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3688_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElab___boxed), 4, 0);
v___x_3689_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3685_, v___x_3686_, v___x_3687_, v___x_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___boxed(lean_object* v_a_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3(){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3718_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3719_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6));
v___x_3720_ = l_Lean_addBuiltinDeclarationRanges(v___x_3718_, v___x_3719_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___boxed(lean_object* v_a_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
return v_res_3722_;
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
