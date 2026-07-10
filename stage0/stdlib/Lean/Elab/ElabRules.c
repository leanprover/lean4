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
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_evalOptPrio___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Array_mkArray5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.Term.TermElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__9;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "TermElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__11_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "stx"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__15;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__14_value),LEAN_SCALAR_PTR_LITERAL(89, 124, 230, 186, 154, 11, 21, 78)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__16 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__16_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__17 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__17_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__18 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__18_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__19 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__19_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__20 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__20_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__21 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__21_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__22 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__22_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noErrorIfUnused"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__23 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__23_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "no_error_if_unused%"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__24 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__24_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "throwUnsupportedSyntax"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__25 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__25_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__26;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__25_value),LEAN_SCALAR_PTR_LITERAL(225, 251, 194, 35, 13, 152, 147, 184)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__27 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__27_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__28 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__28_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__29 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "aux_def"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__30 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__28_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(83, 33, 36, 212, 17, 187, 86, 94)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__31 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value;
static const lean_array_object l_Lean_Elab_Command_elabElabRulesAux___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__32 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Elab.Command.CommandElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__33 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__34;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "CommandElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__35 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__35_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Elab.Do.DoElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__36 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__36_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__37;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__38 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__38_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DoElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__39 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__39_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cont"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__40 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__40_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__41;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__40_value),LEAN_SCALAR_PTR_LITERAL(53, 231, 177, 147, 174, 255, 200, 174)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__42 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__42_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.Tactic.Tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__43 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__43_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__44;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__45 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__45_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expectedType\?"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__46 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__46_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__47;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__46_value),LEAN_SCALAR_PTR_LITERAL(47, 72, 75, 114, 68, 52, 233, 214)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__48 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__48_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__49 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__49_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Elab.Term.withExpectedType"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__50 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__50_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__51;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "withExpectedType"};
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
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 70, 226, 250, 127, 121, 118, 247)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__22_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
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
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
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
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__28_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
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
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__3_value;
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
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 177, 45, 203, 60, 20, 245, 118)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedPrio"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__4_value),LEAN_SCALAR_PTR_LITERAL(171, 32, 2, 102, 118, 75, 64, 185)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "priority"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
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
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__12_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabTail"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
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
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__28_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
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
lean_object* v_a_108_; lean_object* v___x_109_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_a_108_);
lean_dec_ref_known(v___x_107_, 1);
v___x_109_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_101_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_136_; 
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v___x_109_, 0);
lean_dec(v_unused_137_);
v___x_111_ = v___x_109_;
v_isShared_112_ = v_isSharedCheck_136_;
goto v_resetjp_110_;
}
else
{
lean_dec(v___x_109_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_136_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v_quotContext_x3f_113_; lean_object* v___x_114_; 
v_quotContext_x3f_113_ = lean_ctor_get(v___y_101_, 5);
v___x_114_ = l_Lean_SourceInfo_fromRef(v_a_108_, v___x_104_);
lean_dec(v_a_108_);
if (lean_obj_tag(v_quotContext_x3f_113_) == 0)
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_102_);
lean_dec_ref(v___x_135_);
goto v___jp_115_;
}
else
{
goto v___jp_115_;
}
v___jp_115_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_116_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4));
v___x_117_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7));
v___x_118_ = l_Lean_mkIdent(v_kind_100_);
v___x_119_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
lean_inc_n(v___x_114_, 2);
v___x_120_ = l_Lean_Syntax_node1(v___x_114_, v___x_119_, v_a_106_);
v___x_121_ = l_Lean_Syntax_node2(v___x_114_, v___x_117_, v___x_118_, v___x_120_);
v___x_122_ = l_Lean_Syntax_node2(v___x_114_, v___x_116_, v_attrKind_98_, v___x_121_);
if (lean_obj_tag(v_attrs_x3f_99_) == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_mk_empty_array_with_capacity(v___x_123_);
v___x_125_ = lean_array_push(v___x_124_, v___x_122_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_125_);
v___x_127_ = v___x_111_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
else
{
lean_object* v_val_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v_val_129_ = lean_ctor_get(v_attrs_x3f_99_, 0);
v___x_130_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_129_);
v___x_131_ = lean_array_push(v___x_130_, v___x_122_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_131_);
v___x_133_ = v___x_111_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
lean_dec(v_a_108_);
lean_dec(v_a_106_);
lean_dec(v_kind_100_);
lean_dec(v_attrKind_98_);
v_a_138_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_109_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_109_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec(v_a_106_);
lean_dec(v_kind_100_);
lean_dec(v_attrKind_98_);
v_a_146_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_107_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_107_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_dec(v_kind_100_);
lean_dec(v_attrKind_98_);
v_a_154_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_105_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_105_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___boxed(lean_object* v_k_162_, lean_object* v_attrKind_163_, lean_object* v_attrs_x3f_164_, lean_object* v_kind_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_162_, v_attrKind_163_, v_attrs_x3f_164_, v_kind_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v_attrs_x3f_164_);
return v_res_169_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(lean_object* v_opts_170_, lean_object* v_opt_171_){
_start:
{
lean_object* v_name_172_; lean_object* v_defValue_173_; lean_object* v_map_174_; lean_object* v___x_175_; 
v_name_172_ = lean_ctor_get(v_opt_171_, 0);
v_defValue_173_ = lean_ctor_get(v_opt_171_, 1);
v_map_174_ = lean_ctor_get(v_opts_170_, 0);
v___x_175_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_174_, v_name_172_);
if (lean_obj_tag(v___x_175_) == 0)
{
uint8_t v___x_176_; 
v___x_176_ = lean_unbox(v_defValue_173_);
return v___x_176_;
}
else
{
lean_object* v_val_177_; 
v_val_177_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_val_177_);
lean_dec_ref_known(v___x_175_, 1);
if (lean_obj_tag(v_val_177_) == 1)
{
uint8_t v_v_178_; 
v_v_178_ = lean_ctor_get_uint8(v_val_177_, 0);
lean_dec_ref_known(v_val_177_, 0);
return v_v_178_;
}
else
{
uint8_t v___x_179_; 
lean_dec(v_val_177_);
v___x_179_ = lean_unbox(v_defValue_173_);
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8___boxed(lean_object* v_opts_180_, lean_object* v_opt_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(v_opts_180_, v_opt_181_);
lean_dec_ref(v_opt_181_);
lean_dec_ref(v_opts_180_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_box(1);
v___x_185_ = l_Lean_MessageData_ofFormat(v___x_184_);
return v___x_185_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2));
v___x_190_ = l_Lean_MessageData_ofFormat(v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
if (lean_obj_tag(v_x_192_) == 0)
{
return v_x_191_;
}
else
{
lean_object* v_head_193_; lean_object* v_tail_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_216_; 
v_head_193_ = lean_ctor_get(v_x_192_, 0);
v_tail_194_ = lean_ctor_get(v_x_192_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_x_192_);
if (v_isSharedCheck_216_ == 0)
{
v___x_196_ = v_x_192_;
v_isShared_197_ = v_isSharedCheck_216_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_tail_194_);
lean_inc(v_head_193_);
lean_dec(v_x_192_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_216_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v_before_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_214_; 
v_before_198_ = lean_ctor_get(v_head_193_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v_head_193_);
if (v_isSharedCheck_214_ == 0)
{
lean_object* v_unused_215_; 
v_unused_215_ = lean_ctor_get(v_head_193_, 1);
lean_dec(v_unused_215_);
v___x_200_ = v_head_193_;
v_isShared_201_ = v_isSharedCheck_214_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_before_198_);
lean_dec(v_head_193_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_214_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_201_ == 0)
{
lean_ctor_set_tag(v___x_200_, 7);
lean_ctor_set(v___x_200_, 1, v___x_202_);
lean_ctor_set(v___x_200_, 0, v_x_191_);
v___x_204_ = v___x_200_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_x_191_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v___x_202_);
v___x_204_ = v_reuseFailAlloc_213_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_205_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3);
if (v_isShared_197_ == 0)
{
lean_ctor_set_tag(v___x_196_, 7);
lean_ctor_set(v___x_196_, 1, v___x_205_);
lean_ctor_set(v___x_196_, 0, v___x_204_);
v___x_207_ = v___x_196_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_204_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_205_);
v___x_207_ = v_reuseFailAlloc_212_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = l_Lean_MessageData_ofSyntax(v_before_198_);
v___x_209_ = l_Lean_indentD(v___x_208_);
v___x_210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_207_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v_x_191_ = v___x_210_;
v_x_192_ = v_tail_194_;
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
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1));
v___x_221_ = l_Lean_MessageData_ofFormat(v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(lean_object* v_msgData_222_, lean_object* v_macroStack_223_, lean_object* v___y_224_){
_start:
{
lean_object* v___x_226_; lean_object* v_scopes_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_opts_230_; lean_object* v___x_231_; uint8_t v___x_232_; uint8_t v___x_233_; 
v___x_226_ = lean_st_ref_get(v___y_224_);
v_scopes_227_ = lean_ctor_get(v___x_226_, 2);
lean_inc(v_scopes_227_);
lean_dec(v___x_226_);
v___x_228_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_229_ = l_List_head_x21___redArg(v___x_228_, v_scopes_227_);
lean_dec(v_scopes_227_);
v_opts_230_ = lean_ctor_get(v___x_229_, 1);
lean_inc_ref(v_opts_230_);
lean_dec(v___x_229_);
v___x_231_ = l_Lean_Elab_pp_macroStack;
v___x_232_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(v_opts_230_, v___x_231_);
lean_dec_ref(v_opts_230_);
v___x_233_ = lean_bool_not(v___x_232_);
if (v___x_233_ == 0)
{
if (lean_obj_tag(v_macroStack_223_) == 0)
{
lean_object* v___x_234_; 
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v_msgData_222_);
return v___x_234_;
}
else
{
lean_object* v_head_235_; lean_object* v_after_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_251_; 
v_head_235_ = lean_ctor_get(v_macroStack_223_, 0);
lean_inc(v_head_235_);
v_after_236_ = lean_ctor_get(v_head_235_, 1);
v_isSharedCheck_251_ = !lean_is_exclusive(v_head_235_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; 
v_unused_252_ = lean_ctor_get(v_head_235_, 0);
lean_dec(v_unused_252_);
v___x_238_ = v_head_235_;
v_isShared_239_ = v_isSharedCheck_251_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_after_236_);
lean_dec(v_head_235_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_251_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_239_ == 0)
{
lean_ctor_set_tag(v___x_238_, 7);
lean_ctor_set(v___x_238_, 1, v___x_240_);
lean_ctor_set(v___x_238_, 0, v_msgData_222_);
v___x_242_ = v___x_238_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_msgData_222_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___x_240_);
v___x_242_ = v_reuseFailAlloc_250_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v_msgData_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_243_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2);
v___x_244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = l_Lean_MessageData_ofSyntax(v_after_236_);
v___x_246_ = l_Lean_indentD(v___x_245_);
v_msgData_247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_247_, 0, v___x_244_);
lean_ctor_set(v_msgData_247_, 1, v___x_246_);
v___x_248_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(v_msgData_247_, v_macroStack_223_);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
}
}
else
{
lean_object* v___x_253_; 
lean_dec(v_macroStack_223_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v_msgData_222_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___boxed(lean_object* v_msgData_254_, lean_object* v_macroStack_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_msgData_254_, v_macroStack_255_, v___y_256_);
lean_dec(v___y_256_);
return v_res_258_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_259_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0);
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1);
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
lean_ctor_set(v___x_264_, 2, v___x_263_);
lean_ctor_set(v___x_264_, 3, v___x_263_);
lean_ctor_set(v___x_264_, 4, v___x_262_);
lean_ctor_set(v___x_264_, 5, v___x_262_);
lean_ctor_set(v___x_264_, 6, v___x_262_);
lean_ctor_set(v___x_264_, 7, v___x_262_);
lean_ctor_set(v___x_264_, 8, v___x_262_);
lean_ctor_set(v___x_264_, 9, v___x_262_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_unsigned_to_nat(32u);
v___x_266_ = lean_mk_empty_array_with_capacity(v___x_265_);
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_268_ = ((size_t)5ULL);
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = lean_unsigned_to_nat(32u);
v___x_271_ = lean_mk_empty_array_with_capacity(v___x_270_);
v___x_272_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3);
v___x_273_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_271_);
lean_ctor_set(v___x_273_, 2, v___x_269_);
lean_ctor_set(v___x_273_, 3, v___x_269_);
lean_ctor_set_usize(v___x_273_, 4, v___x_268_);
return v___x_273_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_274_ = lean_box(1);
v___x_275_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4);
v___x_276_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1);
v___x_277_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v___x_275_);
lean_ctor_set(v___x_277_, 2, v___x_274_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(lean_object* v_msgData_278_, lean_object* v___y_279_){
_start:
{
lean_object* v___x_281_; lean_object* v_env_282_; lean_object* v___x_283_; lean_object* v_scopes_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v_opts_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_281_ = lean_st_ref_get(v___y_279_);
v_env_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc_ref(v_env_282_);
lean_dec(v___x_281_);
v___x_283_ = lean_st_ref_get(v___y_279_);
v_scopes_284_ = lean_ctor_get(v___x_283_, 2);
lean_inc(v_scopes_284_);
lean_dec(v___x_283_);
v___x_285_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_286_ = l_List_head_x21___redArg(v___x_285_, v_scopes_284_);
lean_dec(v_scopes_284_);
v_opts_287_ = lean_ctor_get(v___x_286_, 1);
lean_inc_ref(v_opts_287_);
lean_dec(v___x_286_);
v___x_288_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2);
v___x_289_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5);
v___x_290_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_290_, 0, v_env_282_);
lean_ctor_set(v___x_290_, 1, v___x_288_);
lean_ctor_set(v___x_290_, 2, v___x_289_);
lean_ctor_set(v___x_290_, 3, v_opts_287_);
v___x_291_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v_msgData_278_);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___boxed(lean_object* v_msgData_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msgData_293_, v___y_294_);
lean_dec(v___y_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(lean_object* v_msg_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Elab_Command_getRef___redArg(v___y_298_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v_macroStack_303_; lean_object* v___x_304_; lean_object* v_a_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_316_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_301_, 1);
v_macroStack_303_ = lean_ctor_get(v___y_298_, 4);
v___x_304_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msg_297_, v___y_299_);
v_a_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_a_305_);
lean_dec_ref(v___x_304_);
v___x_306_ = l_Lean_Elab_getBetterRef(v_a_302_, v_macroStack_303_);
lean_dec(v_a_302_);
lean_inc(v_macroStack_303_);
v___x_307_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_a_305_, v_macroStack_303_, v___y_299_);
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_316_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_316_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_316_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_306_);
lean_ctor_set(v___x_312_, 1, v_a_308_);
if (v_isShared_311_ == 0)
{
lean_ctor_set_tag(v___x_310_, 1);
lean_ctor_set(v___x_310_, 0, v___x_312_);
v___x_314_ = v___x_310_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec_ref(v_msg_297_);
v_a_317_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_301_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_301_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg___boxed(lean_object* v_msg_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_325_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(lean_object* v_ref_330_, lean_object* v_msg_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Elab_Command_getRef___redArg(v___y_332_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v_fileName_337_; lean_object* v_fileMap_338_; lean_object* v_currRecDepth_339_; lean_object* v_cmdPos_340_; lean_object* v_macroStack_341_; lean_object* v_quotContext_x3f_342_; lean_object* v_currMacroScope_343_; lean_object* v_snap_x3f_344_; lean_object* v_cancelTk_x3f_345_; uint8_t v_suppressElabErrors_346_; lean_object* v_ref_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_a_336_);
lean_dec_ref_known(v___x_335_, 1);
v_fileName_337_ = lean_ctor_get(v___y_332_, 0);
v_fileMap_338_ = lean_ctor_get(v___y_332_, 1);
v_currRecDepth_339_ = lean_ctor_get(v___y_332_, 2);
v_cmdPos_340_ = lean_ctor_get(v___y_332_, 3);
v_macroStack_341_ = lean_ctor_get(v___y_332_, 4);
v_quotContext_x3f_342_ = lean_ctor_get(v___y_332_, 5);
v_currMacroScope_343_ = lean_ctor_get(v___y_332_, 6);
v_snap_x3f_344_ = lean_ctor_get(v___y_332_, 8);
v_cancelTk_x3f_345_ = lean_ctor_get(v___y_332_, 9);
v_suppressElabErrors_346_ = lean_ctor_get_uint8(v___y_332_, sizeof(void*)*10);
v_ref_347_ = l_Lean_replaceRef(v_ref_330_, v_a_336_);
lean_dec(v_a_336_);
lean_inc(v_cancelTk_x3f_345_);
lean_inc(v_snap_x3f_344_);
lean_inc(v_currMacroScope_343_);
lean_inc(v_quotContext_x3f_342_);
lean_inc(v_macroStack_341_);
lean_inc(v_cmdPos_340_);
lean_inc(v_currRecDepth_339_);
lean_inc_ref(v_fileMap_338_);
lean_inc_ref(v_fileName_337_);
v___x_348_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_348_, 0, v_fileName_337_);
lean_ctor_set(v___x_348_, 1, v_fileMap_338_);
lean_ctor_set(v___x_348_, 2, v_currRecDepth_339_);
lean_ctor_set(v___x_348_, 3, v_cmdPos_340_);
lean_ctor_set(v___x_348_, 4, v_macroStack_341_);
lean_ctor_set(v___x_348_, 5, v_quotContext_x3f_342_);
lean_ctor_set(v___x_348_, 6, v_currMacroScope_343_);
lean_ctor_set(v___x_348_, 7, v_ref_347_);
lean_ctor_set(v___x_348_, 8, v_snap_x3f_344_);
lean_ctor_set(v___x_348_, 9, v_cancelTk_x3f_345_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*10, v_suppressElabErrors_346_);
v___x_349_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_331_, v___x_348_, v___y_333_);
lean_dec_ref_known(v___x_348_, 10);
return v___x_349_;
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec_ref(v_msg_331_);
v_a_350_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_335_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_335_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(lean_object* v_ref_358_, lean_object* v_msg_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_358_, v_msg_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v_ref_358_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(lean_object* v_k_367_, lean_object* v_as_368_, size_t v_sz_369_, size_t v_i_370_, lean_object* v_b_371_){
_start:
{
uint8_t v___x_372_; 
v___x_372_ = lean_usize_dec_lt(v_i_370_, v_sz_369_);
if (v___x_372_ == 0)
{
lean_dec(v_k_367_);
lean_inc_ref(v_b_371_);
return v_b_371_;
}
else
{
lean_object* v___x_373_; lean_object* v_a_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_373_ = lean_box(0);
v_a_374_ = lean_array_uget_borrowed(v_as_368_, v_i_370_);
lean_inc(v_a_374_);
v___x_375_ = l_Lean_Syntax_getKind(v_a_374_);
lean_inc(v_k_367_);
v___x_376_ = l_Lean_Elab_Command_checkRuleKind(v___x_375_, v_k_367_);
lean_dec(v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; size_t v___x_378_; size_t v___x_379_; 
v___x_377_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0));
v___x_378_ = ((size_t)1ULL);
v___x_379_ = lean_usize_add(v_i_370_, v___x_378_);
v_i_370_ = v___x_379_;
v_b_371_ = v___x_377_;
goto _start;
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
lean_dec(v_k_367_);
lean_inc(v_a_374_);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v_a_374_);
v___x_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_373_);
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(lean_object* v_k_384_, lean_object* v_as_385_, lean_object* v_sz_386_, lean_object* v_i_387_, lean_object* v_b_388_){
_start:
{
size_t v_sz_boxed_389_; size_t v_i_boxed_390_; lean_object* v_res_391_; 
v_sz_boxed_389_ = lean_unbox_usize(v_sz_386_);
lean_dec(v_sz_386_);
v_i_boxed_390_ = lean_unbox_usize(v_i_387_);
lean_dec(v_i_387_);
v_res_391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_k_384_, v_as_385_, v_sz_boxed_389_, v_i_boxed_390_, v_b_388_);
lean_dec_ref(v_b_388_);
lean_dec_ref(v_as_385_);
return v_res_391_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0));
v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2));
v___x_397_ = l_Lean_stringToMessageData(v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7(void){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Array_mkArray0(lean_box(0));
return v___x_405_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11));
v___x_412_ = l_Lean_stringToMessageData(v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(lean_object* v_k_413_, size_t v_sz_414_, size_t v_i_415_, lean_object* v_bs_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
uint8_t v___x_420_; 
v___x_420_ = lean_usize_dec_lt(v_i_415_, v_sz_414_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; 
lean_dec(v_k_413_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v_bs_416_);
return v___x_421_;
}
else
{
lean_object* v_v_422_; lean_object* v___x_423_; lean_object* v_bs_x27_424_; lean_object* v_a_426_; lean_object* v___y_432_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_v_422_ = lean_array_uget(v_bs_416_, v_i_415_);
v___x_423_ = lean_unsigned_to_nat(0u);
v_bs_x27_424_ = lean_array_uset(v_bs_416_, v_i_415_, v___x_423_);
v___x_451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5));
lean_inc(v_v_422_);
v___x_452_ = l_Lean_Syntax_isOfKind(v_v_422_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; 
lean_dec(v_v_422_);
v___x_453_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
v___y_432_ = v___x_453_;
goto v___jp_431_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = l_Lean_Syntax_getArg(v_v_422_, v___x_454_);
lean_inc(v___x_455_);
v___x_456_ = l_Lean_Syntax_matchesNull(v___x_455_, v___x_454_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
lean_dec(v___x_455_);
lean_dec(v_v_422_);
v___x_457_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
v___y_432_ = v___x_457_;
goto v___jp_431_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_pat_476_; lean_object* v___y_478_; lean_object* v___y_479_; uint8_t v___x_531_; uint8_t v___x_532_; 
v___x_458_ = l_Lean_Syntax_getArg(v___x_455_, v___x_423_);
lean_dec(v___x_455_);
v___x_459_ = lean_unsigned_to_nat(3u);
v___x_460_ = l_Lean_Syntax_getArg(v_v_422_, v___x_459_);
v___x_474_ = l_Lean_Syntax_getArgs(v___x_458_);
lean_dec(v___x_458_);
v___x_475_ = lean_box(0);
v_pat_476_ = lean_array_get(v___x_475_, v___x_474_, v___x_423_);
v___x_531_ = l_Lean_Syntax_isQuot(v_pat_476_);
v___x_532_ = lean_bool_not(v___x_531_);
if (v___x_532_ == 0)
{
v___y_478_ = v___y_417_;
v___y_479_ = v___y_418_;
goto v___jp_477_;
}
else
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
if (lean_obj_tag(v___x_533_) == 0)
{
lean_dec_ref_known(v___x_533_, 1);
v___y_478_ = v___y_417_;
v___y_479_ = v___y_418_;
goto v___jp_477_;
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec(v_pat_476_);
lean_dec_ref(v___x_474_);
lean_dec(v___x_460_);
lean_dec_ref(v_bs_x27_424_);
lean_dec(v_v_422_);
lean_dec(v_k_413_);
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
v___jp_461_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_464_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc_n(v___y_462_, 4);
v___x_465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_465_, 0, v___y_462_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_467_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
v___x_468_ = l_Array_append___redArg(v___x_467_, v___y_463_);
lean_dec_ref(v___y_463_);
v___x_469_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_469_, 0, v___y_462_);
lean_ctor_set(v___x_469_, 1, v___x_466_);
lean_ctor_set(v___x_469_, 2, v___x_468_);
v___x_470_ = l_Lean_Syntax_node1(v___y_462_, v___x_466_, v___x_469_);
v___x_471_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_472_, 0, v___y_462_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = l_Lean_Syntax_node4(v___y_462_, v___x_451_, v___x_465_, v___x_470_, v___x_472_, v___x_460_);
v_a_426_ = v___x_473_;
goto v___jp_425_;
}
v___jp_477_:
{
lean_object* v_quoted_480_; lean_object* v_k_x27_481_; uint8_t v___x_482_; 
lean_inc(v_pat_476_);
v_quoted_480_ = l_Lean_Syntax_getQuotContent(v_pat_476_);
lean_inc(v_quoted_480_);
v_k_x27_481_ = l_Lean_Syntax_getKind(v_quoted_480_);
lean_inc(v_k_413_);
v___x_482_ = l_Lean_Elab_Command_checkRuleKind(v_k_x27_481_, v_k_413_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10));
v___x_484_ = lean_name_eq(v_k_x27_481_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec(v_quoted_480_);
lean_dec(v_pat_476_);
lean_dec_ref(v___x_474_);
lean_dec(v___x_460_);
v___x_485_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12);
v___x_486_ = l_Lean_MessageData_ofName(v_k_x27_481_);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_v_422_, v___x_489_, v___y_478_, v___y_479_);
lean_dec(v_v_422_);
v___y_432_ = v___x_490_;
goto v___jp_431_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; size_t v_sz_493_; size_t v___x_494_; lean_object* v___x_495_; lean_object* v_fst_496_; 
lean_dec(v_k_x27_481_);
v___x_491_ = l_Lean_Syntax_getArgs(v_quoted_480_);
lean_dec(v_quoted_480_);
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0));
v_sz_493_ = lean_array_size(v___x_491_);
v___x_494_ = ((size_t)0ULL);
lean_inc(v_k_413_);
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_k_413_, v___x_491_, v_sz_493_, v___x_494_, v___x_492_);
lean_dec_ref(v___x_491_);
v_fst_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_fst_496_);
lean_dec_ref(v___x_495_);
if (lean_obj_tag(v_fst_496_) == 0)
{
lean_dec(v_pat_476_);
lean_dec_ref(v___x_474_);
lean_dec(v___x_460_);
v___y_443_ = v___y_479_;
v___y_444_ = v___y_478_;
goto v___jp_442_;
}
else
{
lean_object* v_val_497_; 
v_val_497_ = lean_ctor_get(v_fst_496_, 0);
lean_inc(v_val_497_);
lean_dec_ref_known(v_fst_496_, 1);
if (lean_obj_tag(v_val_497_) == 0)
{
lean_dec(v_pat_476_);
lean_dec_ref(v___x_474_);
lean_dec(v___x_460_);
v___y_443_ = v___y_479_;
v___y_444_ = v___y_478_;
goto v___jp_442_;
}
else
{
lean_object* v_val_498_; lean_object* v___x_499_; 
lean_dec(v_v_422_);
v_val_498_ = lean_ctor_get(v_val_497_, 0);
lean_inc(v_val_498_);
lean_dec_ref_known(v_val_497_, 1);
v___x_499_ = l_Lean_Elab_Command_getRef___redArg(v___y_478_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_501_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_499_, 1);
v___x_501_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_478_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_quotContext_x3f_502_; lean_object* v_pat_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec_ref_known(v___x_501_, 1);
v_quotContext_x3f_502_ = lean_ctor_get(v___y_478_, 5);
v_pat_503_ = l_Lean_Syntax_setArg(v_pat_476_, v___x_454_, v_val_498_);
v___x_504_ = lean_array_set(v___x_474_, v___x_423_, v_pat_503_);
v___x_505_ = l_Lean_SourceInfo_fromRef(v_a_500_, v___x_482_);
lean_dec(v_a_500_);
if (lean_obj_tag(v_quotContext_x3f_502_) == 0)
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_479_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_dec_ref_known(v___x_506_, 1);
v___y_462_ = v___x_505_;
v___y_463_ = v___x_504_;
goto v___jp_461_;
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_dec(v___x_505_);
lean_dec_ref(v___x_504_);
lean_dec(v___x_460_);
lean_dec_ref(v_bs_x27_424_);
lean_dec(v_k_413_);
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
else
{
v___y_462_ = v___x_505_;
v___y_463_ = v___x_504_;
goto v___jp_461_;
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_dec(v_a_500_);
lean_dec(v_val_498_);
lean_dec(v_pat_476_);
lean_dec_ref(v___x_474_);
lean_dec(v___x_460_);
lean_dec_ref(v_bs_x27_424_);
lean_dec(v_k_413_);
v_a_515_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_501_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_501_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec(v_val_498_);
lean_dec(v_pat_476_);
lean_dec_ref(v___x_474_);
lean_dec(v___x_460_);
lean_dec_ref(v_bs_x27_424_);
lean_dec(v_k_413_);
v_a_523_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_499_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_499_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_x27_481_);
lean_dec(v_quoted_480_);
lean_dec(v_pat_476_);
lean_dec_ref(v___x_474_);
lean_dec(v___x_460_);
v_a_426_ = v_v_422_;
goto v___jp_425_;
}
}
}
}
v___jp_425_:
{
size_t v___x_427_; size_t v___x_428_; lean_object* v___x_429_; 
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_add(v_i_415_, v___x_427_);
v___x_429_ = lean_array_uset(v_bs_x27_424_, v_i_415_, v_a_426_);
v_i_415_ = v___x_428_;
v_bs_416_ = v___x_429_;
goto _start;
}
v___jp_431_:
{
if (lean_obj_tag(v___y_432_) == 0)
{
lean_object* v_a_433_; 
v_a_433_ = lean_ctor_get(v___y_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref_known(v___y_432_, 1);
v_a_426_ = v_a_433_;
goto v___jp_425_;
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec_ref(v_bs_x27_424_);
lean_dec(v_k_413_);
v_a_434_ = lean_ctor_get(v___y_432_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___y_432_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___y_432_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___y_432_);
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
v___jp_442_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_445_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1);
lean_inc(v_k_413_);
v___x_446_ = l_Lean_MessageData_ofName(v_k_413_);
v___x_447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v___x_448_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_v_422_, v___x_449_, v___y_444_, v___y_443_);
lean_dec(v_v_422_);
v___y_432_ = v___x_450_;
goto v___jp_431_;
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
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
v___x_571_ = l_String_toRawSubstring_x27(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_584_ = l_String_toRawSubstring_x27(v___x_583_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__34(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
v___x_599_ = l_String_toRawSubstring_x27(v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__37(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__36));
v___x_603_ = l_String_toRawSubstring_x27(v___x_602_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__41(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__40));
v___x_608_ = l_String_toRawSubstring_x27(v___x_607_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__44(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__43));
v___x_613_ = l_String_toRawSubstring_x27(v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__47(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__46));
v___x_617_ = l_String_toRawSubstring_x27(v___x_616_);
return v___x_617_;
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
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_1684_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_1684_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_1684_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v_a_802_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v_a_916_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v_a_1054_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v_a_1167_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v_a_1319_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v_a_1454_; lean_object* v___y_1465_; uint8_t v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v_catName_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; 
if (lean_obj_tag(v_cat_x3f_665_) == 1)
{
lean_object* v_val_1671_; lean_object* v___x_1672_; 
v_val_1671_ = lean_ctor_get(v_cat_x3f_665_, 0);
v___x_1672_ = l_Lean_TSyntax_getId(v_val_1671_);
v_catName_1498_ = v___x_1672_;
v___y_1499_ = v_a_668_;
v___y_1500_ = v_a_669_;
goto v___jp_1497_;
}
else
{
if (lean_obj_tag(v_expty_x3f_666_) == 1)
{
lean_object* v___x_1673_; 
v___x_1673_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v_catName_1498_ = v___x_1673_;
v___y_1499_ = v_a_668_;
v___y_1500_ = v_a_669_;
goto v___jp_1497_;
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_del_object(v___x_676_);
lean_dec(v_a_674_);
lean_dec(v_expty_x3f_666_);
lean_dec(v_k_664_);
lean_dec(v_attrKind_663_);
lean_dec(v_doc_x3f_661_);
v___x_1674_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__76, &l_Lean_Elab_Command_elabElabRulesAux___closed__76_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76);
v___x_1675_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v___x_1674_, v_a_668_, v_a_669_);
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1675_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1675_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
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
v___jp_678_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
lean_inc_ref_n(v___y_686_, 4);
v___x_691_ = l_Array_append___redArg(v___y_686_, v___y_690_);
lean_dec_ref(v___y_690_);
lean_inc_n(v___y_679_, 10);
lean_inc_n(v___y_685_, 35);
v___x_692_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_692_, 0, v___y_685_);
lean_ctor_set(v___x_692_, 1, v___y_679_);
lean_ctor_set(v___x_692_, 2, v___x_691_);
v___x_693_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_694_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_695_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_684_, 11);
v___x_696_ = l_Lean_Name_mkStr4(v___y_684_, v___x_693_, v___x_694_, v___x_695_);
v___x_697_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_698_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_698_, 0, v___y_685_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_700_ = l_Lean_Syntax_SepArray_ofElems(v___x_699_, v___y_688_);
lean_dec_ref(v___y_688_);
v___x_701_ = l_Array_append___redArg(v___y_686_, v___x_700_);
lean_dec_ref(v___x_700_);
v___x_702_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_702_, 0, v___y_685_);
lean_ctor_set(v___x_702_, 1, v___y_679_);
lean_ctor_set(v___x_702_, 2, v___x_701_);
v___x_703_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_704_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_704_, 0, v___y_685_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = l_Lean_Syntax_node3(v___y_685_, v___x_696_, v___x_698_, v___x_702_, v___x_704_);
v___x_706_ = l_Lean_Syntax_node1(v___y_685_, v___y_679_, v___x_705_);
lean_inc_ref(v___y_689_);
v___x_707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_707_, 0, v___y_685_);
lean_ctor_set(v___x_707_, 1, v___y_689_);
v___x_708_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_709_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_683_, 3);
lean_inc_n(v___y_682_, 3);
v___x_710_ = l_Lean_addMacroScope(v___y_682_, v___x_709_, v___y_683_);
v___x_711_ = lean_box(0);
v___x_712_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_712_, 0, v___y_685_);
lean_ctor_set(v___x_712_, 1, v___x_708_);
lean_ctor_set(v___x_712_, 2, v___x_710_);
lean_ctor_set(v___x_712_, 3, v___x_711_);
v___x_713_ = l_Lean_mkIdent(v_k_664_);
v___x_714_ = l_Lean_Syntax_node2(v___y_685_, v___y_679_, v___x_712_, v___x_713_);
v___x_715_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_716_, 0, v___y_685_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_718_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
lean_inc_ref_n(v___y_687_, 2);
v___x_719_ = l_Lean_Name_mkStr4(v___y_684_, v___y_687_, v___x_694_, v___x_718_);
lean_inc(v___x_719_);
v___x_720_ = l_Lean_addMacroScope(v___y_682_, v___x_719_, v___y_683_);
v___x_721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_711_);
v___x_722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v___x_711_);
v___x_723_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_723_, 0, v___y_685_);
lean_ctor_set(v___x_723_, 1, v___x_717_);
lean_ctor_set(v___x_723_, 2, v___x_720_);
lean_ctor_set(v___x_723_, 3, v___x_722_);
v___x_724_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
v___x_725_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_725_, 0, v___y_685_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_727_ = l_Lean_Name_mkStr4(v___y_684_, v___x_693_, v___x_694_, v___x_726_);
v___x_728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_728_, 0, v___y_685_);
lean_ctor_set(v___x_728_, 1, v___x_726_);
v___x_729_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_730_ = l_Lean_Name_mkStr4(v___y_684_, v___x_693_, v___x_694_, v___x_729_);
v___x_731_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
v___x_732_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
v___x_733_ = l_Lean_addMacroScope(v___y_682_, v___x_732_, v___y_683_);
v___x_734_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_734_, 0, v___y_685_);
lean_ctor_set(v___x_734_, 1, v___x_731_);
lean_ctor_set(v___x_734_, 2, v___x_733_);
lean_ctor_set(v___x_734_, 3, v___x_711_);
v___x_735_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_736_ = l_Lean_Name_mkStr4(v___y_684_, v___x_693_, v___x_694_, v___x_735_);
v___x_737_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_738_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_738_, 0, v___y_685_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = l_Lean_Syntax_node1(v___y_685_, v___x_736_, v___x_738_);
lean_inc(v___x_739_);
lean_inc_ref(v___x_734_);
v___x_740_ = l_Lean_Syntax_node2(v___y_685_, v___y_679_, v___x_734_, v___x_739_);
v___x_741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_741_, 0, v___y_685_);
lean_ctor_set(v___x_741_, 1, v___y_679_);
lean_ctor_set(v___x_741_, 2, v___y_686_);
v___x_742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_743_, 0, v___y_685_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_745_ = l_Lean_Name_mkStr4(v___y_684_, v___x_693_, v___x_694_, v___x_744_);
v___x_746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_746_, 0, v___y_685_);
lean_ctor_set(v___x_746_, 1, v___x_744_);
v___x_747_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_748_ = l_Lean_Name_mkStr4(v___y_684_, v___x_693_, v___x_694_, v___x_747_);
lean_inc_ref_n(v___x_741_, 3);
v___x_749_ = l_Lean_Syntax_node2(v___y_685_, v___x_748_, v___x_741_, v___x_734_);
v___x_750_ = l_Lean_Syntax_node1(v___y_685_, v___y_679_, v___x_749_);
v___x_751_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_752_, 0, v___y_685_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_754_ = l_Lean_Name_mkStr4(v___y_684_, v___x_693_, v___x_694_, v___x_753_);
v___x_755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_756_ = l_Lean_Name_mkStr4(v___y_684_, v___x_693_, v___x_694_, v___x_755_);
v___x_757_ = l_Array_append___redArg(v___y_686_, v_a_674_);
lean_dec(v_a_674_);
v___x_758_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_759_, 0, v___y_685_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = l_Lean_Syntax_node1(v___y_685_, v___y_679_, v___x_739_);
v___x_761_ = l_Lean_Syntax_node1(v___y_685_, v___y_679_, v___x_760_);
v___x_762_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_763_ = l_Lean_Name_mkStr4(v___y_684_, v___x_693_, v___x_694_, v___x_762_);
v___x_764_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_765_, 0, v___y_685_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_767_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
v___x_768_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_769_ = l_Lean_addMacroScope(v___y_682_, v___x_768_, v___y_683_);
v___x_770_ = l_Lean_Name_mkStr3(v___y_684_, v___y_687_, v___x_766_);
v___x_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v___x_711_);
v___x_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
lean_ctor_set(v___x_772_, 1, v___x_711_);
v___x_773_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_773_, 0, v___y_685_);
lean_ctor_set(v___x_773_, 1, v___x_767_);
lean_ctor_set(v___x_773_, 2, v___x_769_);
lean_ctor_set(v___x_773_, 3, v___x_772_);
v___x_774_ = l_Lean_Syntax_node2(v___y_685_, v___x_763_, v___x_765_, v___x_773_);
lean_inc_ref(v___x_743_);
v___x_775_ = l_Lean_Syntax_node4(v___y_685_, v___x_756_, v___x_759_, v___x_761_, v___x_743_, v___x_774_);
v___x_776_ = lean_array_push(v___x_757_, v___x_775_);
v___x_777_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_777_, 0, v___y_685_);
lean_ctor_set(v___x_777_, 1, v___y_679_);
lean_ctor_set(v___x_777_, 2, v___x_776_);
v___x_778_ = l_Lean_Syntax_node1(v___y_685_, v___x_754_, v___x_777_);
v___x_779_ = l_Lean_Syntax_node6(v___y_685_, v___x_745_, v___x_746_, v___x_741_, v___x_741_, v___x_750_, v___x_752_, v___x_778_);
v___x_780_ = l_Lean_Syntax_node4(v___y_685_, v___x_730_, v___x_740_, v___x_741_, v___x_743_, v___x_779_);
v___x_781_ = l_Lean_Syntax_node2(v___y_685_, v___x_727_, v___x_728_, v___x_780_);
v___x_782_ = lean_unsigned_to_nat(9u);
v___x_783_ = lean_mk_empty_array_with_capacity(v___x_782_);
v___x_784_ = lean_array_push(v___x_783_, v___x_692_);
v___x_785_ = lean_array_push(v___x_784_, v___x_706_);
v___x_786_ = lean_array_push(v___x_785_, v___y_681_);
v___x_787_ = lean_array_push(v___x_786_, v___x_707_);
v___x_788_ = lean_array_push(v___x_787_, v___x_714_);
v___x_789_ = lean_array_push(v___x_788_, v___x_716_);
v___x_790_ = lean_array_push(v___x_789_, v___x_723_);
v___x_791_ = lean_array_push(v___x_790_, v___x_725_);
v___x_792_ = lean_array_push(v___x_791_, v___x_781_);
lean_inc(v___y_680_);
v___x_793_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_793_, 0, v___y_685_);
lean_ctor_set(v___x_793_, 1, v___y_680_);
lean_ctor_set(v___x_793_, 2, v___x_792_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_793_);
v___x_795_ = v___x_676_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
v___jp_797_:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_803_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_804_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_805_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_806_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_807_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_808_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_661_) == 1)
{
lean_object* v_val_809_; lean_object* v___x_810_; 
v_val_809_ = lean_ctor_get(v_doc_x3f_661_, 0);
lean_inc(v_val_809_);
lean_dec_ref_known(v_doc_x3f_661_, 1);
v___x_810_ = l_Array_mkArray1___redArg(v_val_809_);
v___y_679_ = v___x_807_;
v___y_680_ = v___x_806_;
v___y_681_ = v___y_798_;
v___y_682_ = v_a_802_;
v___y_683_ = v___y_799_;
v___y_684_ = v___x_803_;
v___y_685_ = v___y_800_;
v___y_686_ = v___x_808_;
v___y_687_ = v___x_804_;
v___y_688_ = v___y_801_;
v___y_689_ = v___x_805_;
v___y_690_ = v___x_810_;
goto v___jp_678_;
}
else
{
lean_object* v___x_811_; 
lean_dec(v_doc_x3f_661_);
v___x_811_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_679_ = v___x_807_;
v___y_680_ = v___x_806_;
v___y_681_ = v___y_798_;
v___y_682_ = v_a_802_;
v___y_683_ = v___y_799_;
v___y_684_ = v___x_803_;
v___y_685_ = v___y_800_;
v___y_686_ = v___x_808_;
v___y_687_ = v___x_804_;
v___y_688_ = v___y_801_;
v___y_689_ = v___x_805_;
v___y_690_ = v___x_811_;
goto v___jp_678_;
}
}
v___jp_812_:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_inc_ref_n(v___y_813_, 3);
v___x_826_ = l_Array_append___redArg(v___y_813_, v___y_825_);
lean_dec_ref(v___y_825_);
lean_inc_n(v___y_817_, 7);
lean_inc_n(v___y_824_, 26);
v___x_827_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_827_, 0, v___y_824_);
lean_ctor_set(v___x_827_, 1, v___y_817_);
lean_ctor_set(v___x_827_, 2, v___x_826_);
v___x_828_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_829_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_830_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_818_, 8);
v___x_831_ = l_Lean_Name_mkStr4(v___y_818_, v___x_828_, v___x_829_, v___x_830_);
v___x_832_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_833_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_833_, 0, v___y_824_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_835_ = l_Lean_Syntax_SepArray_ofElems(v___x_834_, v___y_821_);
lean_dec_ref(v___y_821_);
v___x_836_ = l_Array_append___redArg(v___y_813_, v___x_835_);
lean_dec_ref(v___x_835_);
v___x_837_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_837_, 0, v___y_824_);
lean_ctor_set(v___x_837_, 1, v___y_817_);
lean_ctor_set(v___x_837_, 2, v___x_836_);
v___x_838_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_839_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_839_, 0, v___y_824_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = l_Lean_Syntax_node3(v___y_824_, v___x_831_, v___x_833_, v___x_837_, v___x_839_);
v___x_841_ = l_Lean_Syntax_node1(v___y_824_, v___y_817_, v___x_840_);
lean_inc_ref(v___y_822_);
v___x_842_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_842_, 0, v___y_824_);
lean_ctor_set(v___x_842_, 1, v___y_822_);
v___x_843_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_844_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_814_, 2);
lean_inc_n(v___y_823_, 2);
v___x_845_ = l_Lean_addMacroScope(v___y_823_, v___x_844_, v___y_814_);
v___x_846_ = lean_box(0);
v___x_847_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_847_, 0, v___y_824_);
lean_ctor_set(v___x_847_, 1, v___x_843_);
lean_ctor_set(v___x_847_, 2, v___x_845_);
lean_ctor_set(v___x_847_, 3, v___x_846_);
v___x_848_ = l_Lean_mkIdent(v_k_664_);
v___x_849_ = l_Lean_Syntax_node2(v___y_824_, v___y_817_, v___x_847_, v___x_848_);
v___x_850_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_851_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_851_, 0, v___y_824_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__34, &l_Lean_Elab_Command_elabElabRulesAux___closed__34_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__34);
v___x_853_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
lean_inc_ref(v___y_820_);
lean_inc_ref_n(v___y_815_, 2);
v___x_854_ = l_Lean_Name_mkStr4(v___y_818_, v___y_815_, v___y_820_, v___x_853_);
lean_inc(v___x_854_);
v___x_855_ = l_Lean_addMacroScope(v___y_823_, v___x_854_, v___y_814_);
v___x_856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set(v___x_856_, 1, v___x_846_);
v___x_857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
lean_ctor_set(v___x_857_, 1, v___x_846_);
v___x_858_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_858_, 0, v___y_824_);
lean_ctor_set(v___x_858_, 1, v___x_852_);
lean_ctor_set(v___x_858_, 2, v___x_855_);
lean_ctor_set(v___x_858_, 3, v___x_857_);
v___x_859_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
v___x_860_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_860_, 0, v___y_824_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_862_ = l_Lean_Name_mkStr4(v___y_818_, v___x_828_, v___x_829_, v___x_861_);
v___x_863_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_863_, 0, v___y_824_);
lean_ctor_set(v___x_863_, 1, v___x_861_);
v___x_864_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_865_ = l_Lean_Name_mkStr4(v___y_818_, v___x_828_, v___x_829_, v___x_864_);
v___x_866_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_867_ = l_Lean_Name_mkStr4(v___y_818_, v___x_828_, v___x_829_, v___x_866_);
v___x_868_ = l_Array_append___redArg(v___y_813_, v_a_674_);
lean_dec(v_a_674_);
v___x_869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_870_, 0, v___y_824_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_872_ = l_Lean_Name_mkStr4(v___y_818_, v___x_828_, v___x_829_, v___x_871_);
v___x_873_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_874_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_874_, 0, v___y_824_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = l_Lean_Syntax_node1(v___y_824_, v___x_872_, v___x_874_);
v___x_876_ = l_Lean_Syntax_node1(v___y_824_, v___y_817_, v___x_875_);
v___x_877_ = l_Lean_Syntax_node1(v___y_824_, v___y_817_, v___x_876_);
v___x_878_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_879_, 0, v___y_824_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_881_ = l_Lean_Name_mkStr4(v___y_818_, v___x_828_, v___x_829_, v___x_880_);
v___x_882_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_883_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_883_, 0, v___y_824_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_885_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
v___x_886_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_887_ = l_Lean_addMacroScope(v___y_823_, v___x_886_, v___y_814_);
v___x_888_ = l_Lean_Name_mkStr3(v___y_818_, v___y_815_, v___x_884_);
v___x_889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_846_);
v___x_890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v___x_846_);
v___x_891_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_891_, 0, v___y_824_);
lean_ctor_set(v___x_891_, 1, v___x_885_);
lean_ctor_set(v___x_891_, 2, v___x_887_);
lean_ctor_set(v___x_891_, 3, v___x_890_);
v___x_892_ = l_Lean_Syntax_node2(v___y_824_, v___x_881_, v___x_883_, v___x_891_);
v___x_893_ = l_Lean_Syntax_node4(v___y_824_, v___x_867_, v___x_870_, v___x_877_, v___x_879_, v___x_892_);
v___x_894_ = lean_array_push(v___x_868_, v___x_893_);
v___x_895_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_895_, 0, v___y_824_);
lean_ctor_set(v___x_895_, 1, v___y_817_);
lean_ctor_set(v___x_895_, 2, v___x_894_);
v___x_896_ = l_Lean_Syntax_node1(v___y_824_, v___x_865_, v___x_895_);
v___x_897_ = l_Lean_Syntax_node2(v___y_824_, v___x_862_, v___x_863_, v___x_896_);
v___x_898_ = lean_unsigned_to_nat(9u);
v___x_899_ = lean_mk_empty_array_with_capacity(v___x_898_);
v___x_900_ = lean_array_push(v___x_899_, v___x_827_);
v___x_901_ = lean_array_push(v___x_900_, v___x_841_);
v___x_902_ = lean_array_push(v___x_901_, v___y_819_);
v___x_903_ = lean_array_push(v___x_902_, v___x_842_);
v___x_904_ = lean_array_push(v___x_903_, v___x_849_);
v___x_905_ = lean_array_push(v___x_904_, v___x_851_);
v___x_906_ = lean_array_push(v___x_905_, v___x_858_);
v___x_907_ = lean_array_push(v___x_906_, v___x_860_);
v___x_908_ = lean_array_push(v___x_907_, v___x_897_);
lean_inc(v___y_816_);
v___x_909_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_909_, 0, v___y_824_);
lean_ctor_set(v___x_909_, 1, v___y_816_);
lean_ctor_set(v___x_909_, 2, v___x_908_);
v___x_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
return v___x_910_;
}
v___jp_911_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_917_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_918_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_919_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
v___x_920_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_921_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_922_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_923_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_661_) == 1)
{
lean_object* v_val_924_; lean_object* v___x_925_; 
v_val_924_ = lean_ctor_get(v_doc_x3f_661_, 0);
lean_inc(v_val_924_);
lean_dec_ref_known(v_doc_x3f_661_, 1);
v___x_925_ = l_Array_mkArray1___redArg(v_val_924_);
v___y_813_ = v___x_923_;
v___y_814_ = v___y_913_;
v___y_815_ = v___x_918_;
v___y_816_ = v___x_921_;
v___y_817_ = v___x_922_;
v___y_818_ = v___x_917_;
v___y_819_ = v___y_912_;
v___y_820_ = v___x_919_;
v___y_821_ = v___y_914_;
v___y_822_ = v___x_920_;
v___y_823_ = v_a_916_;
v___y_824_ = v___y_915_;
v___y_825_ = v___x_925_;
goto v___jp_812_;
}
else
{
lean_object* v___x_926_; 
lean_dec(v_doc_x3f_661_);
v___x_926_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_813_ = v___x_923_;
v___y_814_ = v___y_913_;
v___y_815_ = v___x_918_;
v___y_816_ = v___x_921_;
v___y_817_ = v___x_922_;
v___y_818_ = v___x_917_;
v___y_819_ = v___y_912_;
v___y_820_ = v___x_919_;
v___y_821_ = v___y_914_;
v___y_822_ = v___x_920_;
v___y_823_ = v_a_916_;
v___y_824_ = v___y_915_;
v___y_825_ = v___x_926_;
goto v___jp_812_;
}
}
v___jp_927_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_inc_ref_n(v___y_930_, 4);
v___x_940_ = l_Array_append___redArg(v___y_930_, v___y_939_);
lean_dec_ref(v___y_939_);
lean_inc_n(v___y_932_, 10);
lean_inc_n(v___y_935_, 36);
v___x_941_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_941_, 0, v___y_935_);
lean_ctor_set(v___x_941_, 1, v___y_932_);
lean_ctor_set(v___x_941_, 2, v___x_940_);
v___x_942_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_943_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_944_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_934_, 11);
v___x_945_ = l_Lean_Name_mkStr4(v___y_934_, v___x_942_, v___x_943_, v___x_944_);
v___x_946_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_947_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_947_, 0, v___y_935_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_949_ = l_Lean_Syntax_SepArray_ofElems(v___x_948_, v___y_937_);
lean_dec_ref(v___y_937_);
v___x_950_ = l_Array_append___redArg(v___y_930_, v___x_949_);
lean_dec_ref(v___x_949_);
v___x_951_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_951_, 0, v___y_935_);
lean_ctor_set(v___x_951_, 1, v___y_932_);
lean_ctor_set(v___x_951_, 2, v___x_950_);
v___x_952_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_953_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_953_, 0, v___y_935_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = l_Lean_Syntax_node3(v___y_935_, v___x_945_, v___x_947_, v___x_951_, v___x_953_);
v___x_955_ = l_Lean_Syntax_node1(v___y_935_, v___y_932_, v___x_954_);
lean_inc_ref(v___y_931_);
v___x_956_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_956_, 0, v___y_935_);
lean_ctor_set(v___x_956_, 1, v___y_931_);
v___x_957_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_958_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_933_, 4);
lean_inc_n(v___y_938_, 4);
v___x_959_ = l_Lean_addMacroScope(v___y_938_, v___x_958_, v___y_933_);
v___x_960_ = lean_box(0);
v___x_961_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_961_, 0, v___y_935_);
lean_ctor_set(v___x_961_, 1, v___x_957_);
lean_ctor_set(v___x_961_, 2, v___x_959_);
lean_ctor_set(v___x_961_, 3, v___x_960_);
v___x_962_ = l_Lean_mkIdent(v_k_664_);
v___x_963_ = l_Lean_Syntax_node2(v___y_935_, v___y_932_, v___x_961_, v___x_962_);
v___x_964_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_965_, 0, v___y_935_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__37, &l_Lean_Elab_Command_elabElabRulesAux___closed__37_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__37);
v___x_967_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__38));
v___x_968_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__39));
lean_inc_ref_n(v___y_936_, 2);
v___x_969_ = l_Lean_Name_mkStr4(v___y_934_, v___y_936_, v___x_967_, v___x_968_);
lean_inc(v___x_969_);
v___x_970_ = l_Lean_addMacroScope(v___y_938_, v___x_969_, v___y_933_);
v___x_971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_960_);
v___x_972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v___x_960_);
v___x_973_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_973_, 0, v___y_935_);
lean_ctor_set(v___x_973_, 1, v___x_966_);
lean_ctor_set(v___x_973_, 2, v___x_970_);
lean_ctor_set(v___x_973_, 3, v___x_972_);
v___x_974_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
v___x_975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_975_, 0, v___y_935_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_977_ = l_Lean_Name_mkStr4(v___y_934_, v___x_942_, v___x_943_, v___x_976_);
v___x_978_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_978_, 0, v___y_935_);
lean_ctor_set(v___x_978_, 1, v___x_976_);
v___x_979_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_980_ = l_Lean_Name_mkStr4(v___y_934_, v___x_942_, v___x_943_, v___x_979_);
v___x_981_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
v___x_982_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
v___x_983_ = l_Lean_addMacroScope(v___y_938_, v___x_982_, v___y_933_);
v___x_984_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_984_, 0, v___y_935_);
lean_ctor_set(v___x_984_, 1, v___x_981_);
lean_ctor_set(v___x_984_, 2, v___x_983_);
lean_ctor_set(v___x_984_, 3, v___x_960_);
v___x_985_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__41, &l_Lean_Elab_Command_elabElabRulesAux___closed__41_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__41);
v___x_986_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__42));
v___x_987_ = l_Lean_addMacroScope(v___y_938_, v___x_986_, v___y_933_);
v___x_988_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_988_, 0, v___y_935_);
lean_ctor_set(v___x_988_, 1, v___x_985_);
lean_ctor_set(v___x_988_, 2, v___x_987_);
lean_ctor_set(v___x_988_, 3, v___x_960_);
lean_inc_ref(v___x_984_);
v___x_989_ = l_Lean_Syntax_node2(v___y_935_, v___y_932_, v___x_984_, v___x_988_);
v___x_990_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_990_, 0, v___y_935_);
lean_ctor_set(v___x_990_, 1, v___y_932_);
lean_ctor_set(v___x_990_, 2, v___y_930_);
v___x_991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_992_, 0, v___y_935_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_994_ = l_Lean_Name_mkStr4(v___y_934_, v___x_942_, v___x_943_, v___x_993_);
v___x_995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_995_, 0, v___y_935_);
lean_ctor_set(v___x_995_, 1, v___x_993_);
v___x_996_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_997_ = l_Lean_Name_mkStr4(v___y_934_, v___x_942_, v___x_943_, v___x_996_);
lean_inc_ref_n(v___x_990_, 3);
v___x_998_ = l_Lean_Syntax_node2(v___y_935_, v___x_997_, v___x_990_, v___x_984_);
v___x_999_ = l_Lean_Syntax_node1(v___y_935_, v___y_932_, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___y_935_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1003_ = l_Lean_Name_mkStr4(v___y_934_, v___x_942_, v___x_943_, v___x_1002_);
v___x_1004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1005_ = l_Lean_Name_mkStr4(v___y_934_, v___x_942_, v___x_943_, v___x_1004_);
v___x_1006_ = l_Array_append___redArg(v___y_930_, v_a_674_);
lean_dec(v_a_674_);
v___x_1007_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1008_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___y_935_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1010_ = l_Lean_Name_mkStr4(v___y_934_, v___x_942_, v___x_943_, v___x_1009_);
v___x_1011_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___y_935_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l_Lean_Syntax_node1(v___y_935_, v___x_1010_, v___x_1012_);
v___x_1014_ = l_Lean_Syntax_node1(v___y_935_, v___y_932_, v___x_1013_);
v___x_1015_ = l_Lean_Syntax_node1(v___y_935_, v___y_932_, v___x_1014_);
v___x_1016_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1017_ = l_Lean_Name_mkStr4(v___y_934_, v___x_942_, v___x_943_, v___x_1016_);
v___x_1018_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1019_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___y_935_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1021_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
v___x_1022_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1023_ = l_Lean_addMacroScope(v___y_938_, v___x_1022_, v___y_933_);
v___x_1024_ = l_Lean_Name_mkStr3(v___y_934_, v___y_936_, v___x_1020_);
v___x_1025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___x_960_);
v___x_1026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set(v___x_1026_, 1, v___x_960_);
v___x_1027_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1027_, 0, v___y_935_);
lean_ctor_set(v___x_1027_, 1, v___x_1021_);
lean_ctor_set(v___x_1027_, 2, v___x_1023_);
lean_ctor_set(v___x_1027_, 3, v___x_1026_);
v___x_1028_ = l_Lean_Syntax_node2(v___y_935_, v___x_1017_, v___x_1019_, v___x_1027_);
lean_inc_ref(v___x_992_);
v___x_1029_ = l_Lean_Syntax_node4(v___y_935_, v___x_1005_, v___x_1008_, v___x_1015_, v___x_992_, v___x_1028_);
v___x_1030_ = lean_array_push(v___x_1006_, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1031_, 0, v___y_935_);
lean_ctor_set(v___x_1031_, 1, v___y_932_);
lean_ctor_set(v___x_1031_, 2, v___x_1030_);
v___x_1032_ = l_Lean_Syntax_node1(v___y_935_, v___x_1003_, v___x_1031_);
v___x_1033_ = l_Lean_Syntax_node6(v___y_935_, v___x_994_, v___x_995_, v___x_990_, v___x_990_, v___x_999_, v___x_1001_, v___x_1032_);
v___x_1034_ = l_Lean_Syntax_node4(v___y_935_, v___x_980_, v___x_989_, v___x_990_, v___x_992_, v___x_1033_);
v___x_1035_ = l_Lean_Syntax_node2(v___y_935_, v___x_977_, v___x_978_, v___x_1034_);
v___x_1036_ = lean_unsigned_to_nat(9u);
v___x_1037_ = lean_mk_empty_array_with_capacity(v___x_1036_);
v___x_1038_ = lean_array_push(v___x_1037_, v___x_941_);
v___x_1039_ = lean_array_push(v___x_1038_, v___x_955_);
v___x_1040_ = lean_array_push(v___x_1039_, v___y_929_);
v___x_1041_ = lean_array_push(v___x_1040_, v___x_956_);
v___x_1042_ = lean_array_push(v___x_1041_, v___x_963_);
v___x_1043_ = lean_array_push(v___x_1042_, v___x_965_);
v___x_1044_ = lean_array_push(v___x_1043_, v___x_973_);
v___x_1045_ = lean_array_push(v___x_1044_, v___x_975_);
v___x_1046_ = lean_array_push(v___x_1045_, v___x_1035_);
lean_inc(v___y_928_);
v___x_1047_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1047_, 0, v___y_935_);
lean_ctor_set(v___x_1047_, 1, v___y_928_);
lean_ctor_set(v___x_1047_, 2, v___x_1046_);
v___x_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
return v___x_1048_;
}
v___jp_1049_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1055_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1056_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1057_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_1058_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1059_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1060_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_661_) == 1)
{
lean_object* v_val_1061_; lean_object* v___x_1062_; 
v_val_1061_ = lean_ctor_get(v_doc_x3f_661_, 0);
lean_inc(v_val_1061_);
lean_dec_ref_known(v_doc_x3f_661_, 1);
v___x_1062_ = l_Array_mkArray1___redArg(v_val_1061_);
v___y_928_ = v___x_1058_;
v___y_929_ = v___y_1050_;
v___y_930_ = v___x_1060_;
v___y_931_ = v___x_1057_;
v___y_932_ = v___x_1059_;
v___y_933_ = v___y_1052_;
v___y_934_ = v___x_1055_;
v___y_935_ = v___y_1051_;
v___y_936_ = v___x_1056_;
v___y_937_ = v___y_1053_;
v___y_938_ = v_a_1054_;
v___y_939_ = v___x_1062_;
goto v___jp_927_;
}
else
{
lean_object* v___x_1063_; 
lean_dec(v_doc_x3f_661_);
v___x_1063_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_928_ = v___x_1058_;
v___y_929_ = v___y_1050_;
v___y_930_ = v___x_1060_;
v___y_931_ = v___x_1057_;
v___y_932_ = v___x_1059_;
v___y_933_ = v___y_1052_;
v___y_934_ = v___x_1055_;
v___y_935_ = v___y_1051_;
v___y_936_ = v___x_1056_;
v___y_937_ = v___y_1053_;
v___y_938_ = v_a_1054_;
v___y_939_ = v___x_1063_;
goto v___jp_927_;
}
}
v___jp_1064_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_inc_ref_n(v___y_1074_, 3);
v___x_1077_ = l_Array_append___redArg(v___y_1074_, v___y_1076_);
lean_dec_ref(v___y_1076_);
lean_inc_n(v___y_1070_, 7);
lean_inc_n(v___y_1073_, 26);
v___x_1078_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1078_, 0, v___y_1073_);
lean_ctor_set(v___x_1078_, 1, v___y_1070_);
lean_ctor_set(v___x_1078_, 2, v___x_1077_);
v___x_1079_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1080_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1081_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1069_, 8);
v___x_1082_ = l_Lean_Name_mkStr4(v___y_1069_, v___x_1079_, v___x_1080_, v___x_1081_);
v___x_1083_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1084_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___y_1073_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1086_ = l_Lean_Syntax_SepArray_ofElems(v___x_1085_, v___y_1068_);
lean_dec_ref(v___y_1068_);
v___x_1087_ = l_Array_append___redArg(v___y_1074_, v___x_1086_);
lean_dec_ref(v___x_1086_);
v___x_1088_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1088_, 0, v___y_1073_);
lean_ctor_set(v___x_1088_, 1, v___y_1070_);
lean_ctor_set(v___x_1088_, 2, v___x_1087_);
v___x_1089_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1090_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___y_1073_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = l_Lean_Syntax_node3(v___y_1073_, v___x_1082_, v___x_1084_, v___x_1088_, v___x_1090_);
v___x_1092_ = l_Lean_Syntax_node1(v___y_1073_, v___y_1070_, v___x_1091_);
lean_inc_ref(v___y_1072_);
v___x_1093_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___y_1073_);
lean_ctor_set(v___x_1093_, 1, v___y_1072_);
v___x_1094_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1095_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1067_, 2);
lean_inc_n(v___y_1071_, 2);
v___x_1096_ = l_Lean_addMacroScope(v___y_1071_, v___x_1095_, v___y_1067_);
v___x_1097_ = lean_box(0);
v___x_1098_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1098_, 0, v___y_1073_);
lean_ctor_set(v___x_1098_, 1, v___x_1094_);
lean_ctor_set(v___x_1098_, 2, v___x_1096_);
lean_ctor_set(v___x_1098_, 3, v___x_1097_);
v___x_1099_ = l_Lean_mkIdent(v_k_664_);
v___x_1100_ = l_Lean_Syntax_node2(v___y_1073_, v___y_1070_, v___x_1098_, v___x_1099_);
v___x_1101_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1102_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___y_1073_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__44, &l_Lean_Elab_Command_elabElabRulesAux___closed__44_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__44);
v___x_1104_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__45));
lean_inc_ref_n(v___y_1066_, 2);
v___x_1105_ = l_Lean_Name_mkStr4(v___y_1069_, v___y_1066_, v___x_1104_, v___x_1104_);
lean_inc(v___x_1105_);
v___x_1106_ = l_Lean_addMacroScope(v___y_1071_, v___x_1105_, v___y_1067_);
v___x_1107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1097_);
v___x_1108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
lean_ctor_set(v___x_1108_, 1, v___x_1097_);
v___x_1109_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1109_, 0, v___y_1073_);
lean_ctor_set(v___x_1109_, 1, v___x_1103_);
lean_ctor_set(v___x_1109_, 2, v___x_1106_);
lean_ctor_set(v___x_1109_, 3, v___x_1108_);
v___x_1110_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
v___x_1111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___y_1073_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1113_ = l_Lean_Name_mkStr4(v___y_1069_, v___x_1079_, v___x_1080_, v___x_1112_);
v___x_1114_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___y_1073_);
lean_ctor_set(v___x_1114_, 1, v___x_1112_);
v___x_1115_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1116_ = l_Lean_Name_mkStr4(v___y_1069_, v___x_1079_, v___x_1080_, v___x_1115_);
v___x_1117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1118_ = l_Lean_Name_mkStr4(v___y_1069_, v___x_1079_, v___x_1080_, v___x_1117_);
v___x_1119_ = l_Array_append___redArg(v___y_1074_, v_a_674_);
lean_dec(v_a_674_);
v___x_1120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___y_1073_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1123_ = l_Lean_Name_mkStr4(v___y_1069_, v___x_1079_, v___x_1080_, v___x_1122_);
v___x_1124_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___y_1073_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Lean_Syntax_node1(v___y_1073_, v___x_1123_, v___x_1125_);
v___x_1127_ = l_Lean_Syntax_node1(v___y_1073_, v___y_1070_, v___x_1126_);
v___x_1128_ = l_Lean_Syntax_node1(v___y_1073_, v___y_1070_, v___x_1127_);
v___x_1129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___y_1073_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1132_ = l_Lean_Name_mkStr4(v___y_1069_, v___x_1079_, v___x_1080_, v___x_1131_);
v___x_1133_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___y_1073_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1136_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
v___x_1137_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1138_ = l_Lean_addMacroScope(v___y_1071_, v___x_1137_, v___y_1067_);
v___x_1139_ = l_Lean_Name_mkStr3(v___y_1069_, v___y_1066_, v___x_1135_);
v___x_1140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v___x_1097_);
v___x_1141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v___x_1097_);
v___x_1142_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1142_, 0, v___y_1073_);
lean_ctor_set(v___x_1142_, 1, v___x_1136_);
lean_ctor_set(v___x_1142_, 2, v___x_1138_);
lean_ctor_set(v___x_1142_, 3, v___x_1141_);
v___x_1143_ = l_Lean_Syntax_node2(v___y_1073_, v___x_1132_, v___x_1134_, v___x_1142_);
v___x_1144_ = l_Lean_Syntax_node4(v___y_1073_, v___x_1118_, v___x_1121_, v___x_1128_, v___x_1130_, v___x_1143_);
v___x_1145_ = lean_array_push(v___x_1119_, v___x_1144_);
v___x_1146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1146_, 0, v___y_1073_);
lean_ctor_set(v___x_1146_, 1, v___y_1070_);
lean_ctor_set(v___x_1146_, 2, v___x_1145_);
v___x_1147_ = l_Lean_Syntax_node1(v___y_1073_, v___x_1116_, v___x_1146_);
v___x_1148_ = l_Lean_Syntax_node2(v___y_1073_, v___x_1113_, v___x_1114_, v___x_1147_);
v___x_1149_ = lean_unsigned_to_nat(9u);
v___x_1150_ = lean_mk_empty_array_with_capacity(v___x_1149_);
v___x_1151_ = lean_array_push(v___x_1150_, v___x_1078_);
v___x_1152_ = lean_array_push(v___x_1151_, v___x_1092_);
v___x_1153_ = lean_array_push(v___x_1152_, v___y_1065_);
v___x_1154_ = lean_array_push(v___x_1153_, v___x_1093_);
v___x_1155_ = lean_array_push(v___x_1154_, v___x_1100_);
v___x_1156_ = lean_array_push(v___x_1155_, v___x_1102_);
v___x_1157_ = lean_array_push(v___x_1156_, v___x_1109_);
v___x_1158_ = lean_array_push(v___x_1157_, v___x_1111_);
v___x_1159_ = lean_array_push(v___x_1158_, v___x_1148_);
lean_inc(v___y_1075_);
v___x_1160_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1160_, 0, v___y_1073_);
lean_ctor_set(v___x_1160_, 1, v___y_1075_);
lean_ctor_set(v___x_1160_, 2, v___x_1159_);
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
v___jp_1162_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1168_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1169_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1170_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_1171_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1172_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1173_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_661_) == 1)
{
lean_object* v_val_1174_; lean_object* v___x_1175_; 
v_val_1174_ = lean_ctor_get(v_doc_x3f_661_, 0);
lean_inc(v_val_1174_);
lean_dec_ref_known(v_doc_x3f_661_, 1);
v___x_1175_ = l_Array_mkArray1___redArg(v_val_1174_);
v___y_1065_ = v___y_1163_;
v___y_1066_ = v___x_1169_;
v___y_1067_ = v___y_1165_;
v___y_1068_ = v___y_1164_;
v___y_1069_ = v___x_1168_;
v___y_1070_ = v___x_1172_;
v___y_1071_ = v_a_1167_;
v___y_1072_ = v___x_1170_;
v___y_1073_ = v___y_1166_;
v___y_1074_ = v___x_1173_;
v___y_1075_ = v___x_1171_;
v___y_1076_ = v___x_1175_;
goto v___jp_1064_;
}
else
{
lean_object* v___x_1176_; 
lean_dec(v_doc_x3f_661_);
v___x_1176_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_1065_ = v___y_1163_;
v___y_1066_ = v___x_1169_;
v___y_1067_ = v___y_1165_;
v___y_1068_ = v___y_1164_;
v___y_1069_ = v___x_1168_;
v___y_1070_ = v___x_1172_;
v___y_1071_ = v_a_1167_;
v___y_1072_ = v___x_1170_;
v___y_1073_ = v___y_1166_;
v___y_1074_ = v___x_1173_;
v___y_1075_ = v___x_1171_;
v___y_1076_ = v___x_1176_;
goto v___jp_1064_;
}
}
v___jp_1177_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_inc_ref_n(v___y_1188_, 4);
v___x_1191_ = l_Array_append___redArg(v___y_1188_, v___y_1190_);
lean_dec_ref(v___y_1190_);
lean_inc_n(v___y_1186_, 12);
lean_inc_n(v___y_1183_, 42);
v___x_1192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1192_, 0, v___y_1183_);
lean_ctor_set(v___x_1192_, 1, v___y_1186_);
lean_ctor_set(v___x_1192_, 2, v___x_1191_);
v___x_1193_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1194_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1195_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1185_, 13);
v___x_1196_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1193_, v___x_1194_, v___x_1195_);
v___x_1197_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1198_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___y_1183_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1200_ = l_Lean_Syntax_SepArray_ofElems(v___x_1199_, v___y_1181_);
lean_dec_ref(v___y_1181_);
v___x_1201_ = l_Array_append___redArg(v___y_1188_, v___x_1200_);
lean_dec_ref(v___x_1200_);
v___x_1202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1202_, 0, v___y_1183_);
lean_ctor_set(v___x_1202_, 1, v___y_1186_);
lean_ctor_set(v___x_1202_, 2, v___x_1201_);
v___x_1203_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___y_1183_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = l_Lean_Syntax_node3(v___y_1183_, v___x_1196_, v___x_1198_, v___x_1202_, v___x_1204_);
v___x_1206_ = l_Lean_Syntax_node1(v___y_1183_, v___y_1186_, v___x_1205_);
lean_inc_ref(v___y_1179_);
v___x_1207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___y_1183_);
lean_ctor_set(v___x_1207_, 1, v___y_1179_);
v___x_1208_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1209_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1180_, 5);
lean_inc_n(v___y_1189_, 5);
v___x_1210_ = l_Lean_addMacroScope(v___y_1189_, v___x_1209_, v___y_1180_);
v___x_1211_ = lean_box(0);
v___x_1212_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1212_, 0, v___y_1183_);
lean_ctor_set(v___x_1212_, 1, v___x_1208_);
lean_ctor_set(v___x_1212_, 2, v___x_1210_);
lean_ctor_set(v___x_1212_, 3, v___x_1211_);
v___x_1213_ = l_Lean_mkIdent(v_k_664_);
v___x_1214_ = l_Lean_Syntax_node2(v___y_1183_, v___y_1186_, v___x_1212_, v___x_1213_);
v___x_1215_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1216_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___y_1183_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v___x_1217_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
v___x_1218_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
lean_inc_ref_n(v___y_1182_, 3);
v___x_1219_ = l_Lean_Name_mkStr4(v___y_1185_, v___y_1182_, v___x_1194_, v___x_1218_);
lean_inc(v___x_1219_);
v___x_1220_ = l_Lean_addMacroScope(v___y_1189_, v___x_1219_, v___y_1180_);
v___x_1221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1211_);
v___x_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v___x_1211_);
v___x_1223_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1223_, 0, v___y_1183_);
lean_ctor_set(v___x_1223_, 1, v___x_1217_);
lean_ctor_set(v___x_1223_, 2, v___x_1220_);
lean_ctor_set(v___x_1223_, 3, v___x_1222_);
v___x_1224_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
v___x_1225_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___y_1183_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1227_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1193_, v___x_1194_, v___x_1226_);
v___x_1228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___y_1183_);
lean_ctor_set(v___x_1228_, 1, v___x_1226_);
v___x_1229_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1230_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1193_, v___x_1194_, v___x_1229_);
v___x_1231_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
v___x_1232_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
v___x_1233_ = l_Lean_addMacroScope(v___y_1189_, v___x_1232_, v___y_1180_);
v___x_1234_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1234_, 0, v___y_1183_);
lean_ctor_set(v___x_1234_, 1, v___x_1231_);
lean_ctor_set(v___x_1234_, 2, v___x_1233_);
lean_ctor_set(v___x_1234_, 3, v___x_1211_);
v___x_1235_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__47, &l_Lean_Elab_Command_elabElabRulesAux___closed__47_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__47);
v___x_1236_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__48));
v___x_1237_ = l_Lean_addMacroScope(v___y_1189_, v___x_1236_, v___y_1180_);
v___x_1238_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1238_, 0, v___y_1183_);
lean_ctor_set(v___x_1238_, 1, v___x_1235_);
lean_ctor_set(v___x_1238_, 2, v___x_1237_);
lean_ctor_set(v___x_1238_, 3, v___x_1211_);
lean_inc_ref(v___x_1238_);
lean_inc_ref(v___x_1234_);
v___x_1239_ = l_Lean_Syntax_node2(v___y_1183_, v___y_1186_, v___x_1234_, v___x_1238_);
v___x_1240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1240_, 0, v___y_1183_);
lean_ctor_set(v___x_1240_, 1, v___y_1186_);
lean_ctor_set(v___x_1240_, 2, v___y_1188_);
v___x_1241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___y_1183_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__49));
v___x_1244_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1193_, v___x_1194_, v___x_1243_);
v___x_1245_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__51, &l_Lean_Elab_Command_elabElabRulesAux___closed__51_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__51);
v___x_1246_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__52));
v___x_1247_ = l_Lean_Name_mkStr4(v___y_1185_, v___y_1182_, v___x_1194_, v___x_1246_);
lean_inc(v___x_1247_);
v___x_1248_ = l_Lean_addMacroScope(v___y_1189_, v___x_1247_, v___y_1180_);
v___x_1249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1211_);
v___x_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v___x_1211_);
v___x_1251_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1251_, 0, v___y_1183_);
lean_ctor_set(v___x_1251_, 1, v___x_1245_);
lean_ctor_set(v___x_1251_, 2, v___x_1248_);
lean_ctor_set(v___x_1251_, 3, v___x_1250_);
v___x_1252_ = l_Lean_Syntax_node1(v___y_1183_, v___y_1186_, v___y_1178_);
v___x_1253_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_1254_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1193_, v___x_1194_, v___x_1253_);
v___x_1255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___y_1183_);
lean_ctor_set(v___x_1255_, 1, v___x_1253_);
v___x_1256_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_1257_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1193_, v___x_1194_, v___x_1256_);
lean_inc_ref_n(v___x_1240_, 4);
v___x_1258_ = l_Lean_Syntax_node2(v___y_1183_, v___x_1257_, v___x_1240_, v___x_1234_);
v___x_1259_ = l_Lean_Syntax_node1(v___y_1183_, v___y_1186_, v___x_1258_);
v___x_1260_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1261_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___y_1183_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1263_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1193_, v___x_1194_, v___x_1262_);
v___x_1264_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1265_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1193_, v___x_1194_, v___x_1264_);
v___x_1266_ = l_Array_append___redArg(v___y_1188_, v_a_674_);
lean_dec(v_a_674_);
v___x_1267_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1268_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___y_1183_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1270_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1193_, v___x_1194_, v___x_1269_);
v___x_1271_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1272_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___y_1183_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = l_Lean_Syntax_node1(v___y_1183_, v___x_1270_, v___x_1272_);
v___x_1274_ = l_Lean_Syntax_node1(v___y_1183_, v___y_1186_, v___x_1273_);
v___x_1275_ = l_Lean_Syntax_node1(v___y_1183_, v___y_1186_, v___x_1274_);
v___x_1276_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1277_ = l_Lean_Name_mkStr4(v___y_1185_, v___x_1193_, v___x_1194_, v___x_1276_);
v___x_1278_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___y_1183_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1281_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
v___x_1282_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1283_ = l_Lean_addMacroScope(v___y_1189_, v___x_1282_, v___y_1180_);
v___x_1284_ = l_Lean_Name_mkStr3(v___y_1185_, v___y_1182_, v___x_1280_);
v___x_1285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
lean_ctor_set(v___x_1285_, 1, v___x_1211_);
v___x_1286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
lean_ctor_set(v___x_1286_, 1, v___x_1211_);
v___x_1287_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1287_, 0, v___y_1183_);
lean_ctor_set(v___x_1287_, 1, v___x_1281_);
lean_ctor_set(v___x_1287_, 2, v___x_1283_);
lean_ctor_set(v___x_1287_, 3, v___x_1286_);
v___x_1288_ = l_Lean_Syntax_node2(v___y_1183_, v___x_1277_, v___x_1279_, v___x_1287_);
lean_inc_ref_n(v___x_1242_, 2);
v___x_1289_ = l_Lean_Syntax_node4(v___y_1183_, v___x_1265_, v___x_1268_, v___x_1275_, v___x_1242_, v___x_1288_);
v___x_1290_ = lean_array_push(v___x_1266_, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1291_, 0, v___y_1183_);
lean_ctor_set(v___x_1291_, 1, v___y_1186_);
lean_ctor_set(v___x_1291_, 2, v___x_1290_);
v___x_1292_ = l_Lean_Syntax_node1(v___y_1183_, v___x_1263_, v___x_1291_);
v___x_1293_ = l_Lean_Syntax_node6(v___y_1183_, v___x_1254_, v___x_1255_, v___x_1240_, v___x_1240_, v___x_1259_, v___x_1261_, v___x_1292_);
lean_inc(v___x_1230_);
v___x_1294_ = l_Lean_Syntax_node4(v___y_1183_, v___x_1230_, v___x_1252_, v___x_1240_, v___x_1242_, v___x_1293_);
lean_inc_ref(v___x_1228_);
lean_inc(v___x_1227_);
v___x_1295_ = l_Lean_Syntax_node2(v___y_1183_, v___x_1227_, v___x_1228_, v___x_1294_);
v___x_1296_ = l_Lean_Syntax_node2(v___y_1183_, v___y_1186_, v___x_1238_, v___x_1295_);
v___x_1297_ = l_Lean_Syntax_node2(v___y_1183_, v___x_1244_, v___x_1251_, v___x_1296_);
v___x_1298_ = l_Lean_Syntax_node4(v___y_1183_, v___x_1230_, v___x_1239_, v___x_1240_, v___x_1242_, v___x_1297_);
v___x_1299_ = l_Lean_Syntax_node2(v___y_1183_, v___x_1227_, v___x_1228_, v___x_1298_);
v___x_1300_ = lean_unsigned_to_nat(9u);
v___x_1301_ = lean_mk_empty_array_with_capacity(v___x_1300_);
v___x_1302_ = lean_array_push(v___x_1301_, v___x_1192_);
v___x_1303_ = lean_array_push(v___x_1302_, v___x_1206_);
v___x_1304_ = lean_array_push(v___x_1303_, v___y_1184_);
v___x_1305_ = lean_array_push(v___x_1304_, v___x_1207_);
v___x_1306_ = lean_array_push(v___x_1305_, v___x_1214_);
v___x_1307_ = lean_array_push(v___x_1306_, v___x_1216_);
v___x_1308_ = lean_array_push(v___x_1307_, v___x_1223_);
v___x_1309_ = lean_array_push(v___x_1308_, v___x_1225_);
v___x_1310_ = lean_array_push(v___x_1309_, v___x_1299_);
lean_inc(v___y_1187_);
v___x_1311_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1311_, 0, v___y_1183_);
lean_ctor_set(v___x_1311_, 1, v___y_1187_);
lean_ctor_set(v___x_1311_, 2, v___x_1310_);
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
return v___x_1312_;
}
v___jp_1313_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1320_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1321_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1322_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_1323_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1324_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1325_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_661_) == 1)
{
lean_object* v_val_1326_; lean_object* v___x_1327_; 
v_val_1326_ = lean_ctor_get(v_doc_x3f_661_, 0);
lean_inc(v_val_1326_);
lean_dec_ref_known(v_doc_x3f_661_, 1);
v___x_1327_ = l_Array_mkArray1___redArg(v_val_1326_);
v___y_1178_ = v___y_1314_;
v___y_1179_ = v___x_1322_;
v___y_1180_ = v___y_1316_;
v___y_1181_ = v___y_1317_;
v___y_1182_ = v___x_1321_;
v___y_1183_ = v___y_1318_;
v___y_1184_ = v___y_1315_;
v___y_1185_ = v___x_1320_;
v___y_1186_ = v___x_1324_;
v___y_1187_ = v___x_1323_;
v___y_1188_ = v___x_1325_;
v___y_1189_ = v_a_1319_;
v___y_1190_ = v___x_1327_;
goto v___jp_1177_;
}
else
{
lean_object* v___x_1328_; 
lean_dec(v_doc_x3f_661_);
v___x_1328_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_1178_ = v___y_1314_;
v___y_1179_ = v___x_1322_;
v___y_1180_ = v___y_1316_;
v___y_1181_ = v___y_1317_;
v___y_1182_ = v___x_1321_;
v___y_1183_ = v___y_1318_;
v___y_1184_ = v___y_1315_;
v___y_1185_ = v___x_1320_;
v___y_1186_ = v___x_1324_;
v___y_1187_ = v___x_1323_;
v___y_1188_ = v___x_1325_;
v___y_1189_ = v_a_1319_;
v___y_1190_ = v___x_1328_;
goto v___jp_1177_;
}
}
v___jp_1329_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
lean_inc_ref_n(v___y_1332_, 4);
v___x_1343_ = l_Array_append___redArg(v___y_1332_, v___y_1342_);
lean_dec_ref(v___y_1342_);
lean_inc_n(v___y_1338_, 10);
lean_inc_n(v___y_1331_, 35);
v___x_1344_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1344_, 0, v___y_1331_);
lean_ctor_set(v___x_1344_, 1, v___y_1338_);
lean_ctor_set(v___x_1344_, 2, v___x_1343_);
v___x_1345_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1346_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1347_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref_n(v___y_1340_, 11);
v___x_1348_ = l_Lean_Name_mkStr4(v___y_1340_, v___x_1345_, v___x_1346_, v___x_1347_);
v___x_1349_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
v___x_1350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___y_1331_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
v___x_1351_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
v___x_1352_ = l_Lean_Syntax_SepArray_ofElems(v___x_1351_, v___y_1335_);
lean_dec_ref(v___y_1335_);
v___x_1353_ = l_Array_append___redArg(v___y_1332_, v___x_1352_);
lean_dec_ref(v___x_1352_);
v___x_1354_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1354_, 0, v___y_1331_);
lean_ctor_set(v___x_1354_, 1, v___y_1338_);
lean_ctor_set(v___x_1354_, 2, v___x_1353_);
v___x_1355_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___y_1331_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = l_Lean_Syntax_node3(v___y_1331_, v___x_1348_, v___x_1350_, v___x_1354_, v___x_1356_);
v___x_1358_ = l_Lean_Syntax_node1(v___y_1331_, v___y_1338_, v___x_1357_);
lean_inc_ref(v___y_1336_);
v___x_1359_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___y_1331_);
lean_ctor_set(v___x_1359_, 1, v___y_1336_);
v___x_1360_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
v___x_1361_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc_n(v___y_1337_, 3);
lean_inc_n(v___y_1339_, 3);
v___x_1362_ = l_Lean_addMacroScope(v___y_1339_, v___x_1361_, v___y_1337_);
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1364_, 0, v___y_1331_);
lean_ctor_set(v___x_1364_, 1, v___x_1360_);
lean_ctor_set(v___x_1364_, 2, v___x_1362_);
lean_ctor_set(v___x_1364_, 3, v___x_1363_);
v___x_1365_ = l_Lean_mkIdent(v_k_664_);
v___x_1366_ = l_Lean_Syntax_node2(v___y_1331_, v___y_1338_, v___x_1364_, v___x_1365_);
v___x_1367_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_1368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___y_1331_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__37, &l_Lean_Elab_Command_elabElabRulesAux___closed__37_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__37);
v___x_1370_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__38));
v___x_1371_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__39));
lean_inc_ref_n(v___y_1341_, 2);
v___x_1372_ = l_Lean_Name_mkStr4(v___y_1340_, v___y_1341_, v___x_1370_, v___x_1371_);
lean_inc(v___x_1372_);
v___x_1373_ = l_Lean_addMacroScope(v___y_1339_, v___x_1372_, v___y_1337_);
v___x_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1372_);
lean_ctor_set(v___x_1374_, 1, v___x_1363_);
v___x_1375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v___x_1363_);
v___x_1376_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1376_, 0, v___y_1331_);
lean_ctor_set(v___x_1376_, 1, v___x_1369_);
lean_ctor_set(v___x_1376_, 2, v___x_1373_);
lean_ctor_set(v___x_1376_, 3, v___x_1375_);
v___x_1377_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
v___x_1378_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___y_1331_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
v___x_1380_ = l_Lean_Name_mkStr4(v___y_1340_, v___x_1345_, v___x_1346_, v___x_1379_);
v___x_1381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___y_1331_);
lean_ctor_set(v___x_1381_, 1, v___x_1379_);
v___x_1382_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
v___x_1383_ = l_Lean_Name_mkStr4(v___y_1340_, v___x_1345_, v___x_1346_, v___x_1382_);
v___x_1384_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
v___x_1385_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
v___x_1386_ = l_Lean_addMacroScope(v___y_1339_, v___x_1385_, v___y_1337_);
v___x_1387_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1387_, 0, v___y_1331_);
lean_ctor_set(v___x_1387_, 1, v___x_1384_);
lean_ctor_set(v___x_1387_, 2, v___x_1386_);
lean_ctor_set(v___x_1387_, 3, v___x_1363_);
lean_inc_ref(v___x_1387_);
v___x_1388_ = l_Lean_Syntax_node2(v___y_1331_, v___y_1338_, v___x_1387_, v___y_1330_);
v___x_1389_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1389_, 0, v___y_1331_);
lean_ctor_set(v___x_1389_, 1, v___y_1338_);
lean_ctor_set(v___x_1389_, 2, v___y_1332_);
v___x_1390_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_1391_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___y_1331_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
v___x_1392_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
v___x_1393_ = l_Lean_Name_mkStr4(v___y_1340_, v___x_1345_, v___x_1346_, v___x_1392_);
v___x_1394_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___y_1331_);
lean_ctor_set(v___x_1394_, 1, v___x_1392_);
v___x_1395_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
v___x_1396_ = l_Lean_Name_mkStr4(v___y_1340_, v___x_1345_, v___x_1346_, v___x_1395_);
lean_inc_ref_n(v___x_1389_, 3);
v___x_1397_ = l_Lean_Syntax_node2(v___y_1331_, v___x_1396_, v___x_1389_, v___x_1387_);
v___x_1398_ = l_Lean_Syntax_node1(v___y_1331_, v___y_1338_, v___x_1397_);
v___x_1399_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
v___x_1400_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___y_1331_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
v___x_1401_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
v___x_1402_ = l_Lean_Name_mkStr4(v___y_1340_, v___x_1345_, v___x_1346_, v___x_1401_);
v___x_1403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_1404_ = l_Lean_Name_mkStr4(v___y_1340_, v___x_1345_, v___x_1346_, v___x_1403_);
v___x_1405_ = l_Array_append___redArg(v___y_1332_, v_a_674_);
lean_dec(v_a_674_);
v___x_1406_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_1407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___y_1331_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
v___x_1408_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
v___x_1409_ = l_Lean_Name_mkStr4(v___y_1340_, v___x_1345_, v___x_1346_, v___x_1408_);
v___x_1410_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
v___x_1411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___y_1331_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = l_Lean_Syntax_node1(v___y_1331_, v___x_1409_, v___x_1411_);
v___x_1413_ = l_Lean_Syntax_node1(v___y_1331_, v___y_1338_, v___x_1412_);
v___x_1414_ = l_Lean_Syntax_node1(v___y_1331_, v___y_1338_, v___x_1413_);
v___x_1415_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
v___x_1416_ = l_Lean_Name_mkStr4(v___y_1340_, v___x_1345_, v___x_1346_, v___x_1415_);
v___x_1417_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
v___x_1418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___y_1331_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
v___x_1420_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
v___x_1421_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
v___x_1422_ = l_Lean_addMacroScope(v___y_1339_, v___x_1421_, v___y_1337_);
v___x_1423_ = l_Lean_Name_mkStr3(v___y_1340_, v___y_1341_, v___x_1419_);
v___x_1424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
lean_ctor_set(v___x_1424_, 1, v___x_1363_);
v___x_1425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
lean_ctor_set(v___x_1425_, 1, v___x_1363_);
v___x_1426_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1426_, 0, v___y_1331_);
lean_ctor_set(v___x_1426_, 1, v___x_1420_);
lean_ctor_set(v___x_1426_, 2, v___x_1422_);
lean_ctor_set(v___x_1426_, 3, v___x_1425_);
v___x_1427_ = l_Lean_Syntax_node2(v___y_1331_, v___x_1416_, v___x_1418_, v___x_1426_);
lean_inc_ref(v___x_1391_);
v___x_1428_ = l_Lean_Syntax_node4(v___y_1331_, v___x_1404_, v___x_1407_, v___x_1414_, v___x_1391_, v___x_1427_);
v___x_1429_ = lean_array_push(v___x_1405_, v___x_1428_);
v___x_1430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1430_, 0, v___y_1331_);
lean_ctor_set(v___x_1430_, 1, v___y_1338_);
lean_ctor_set(v___x_1430_, 2, v___x_1429_);
v___x_1431_ = l_Lean_Syntax_node1(v___y_1331_, v___x_1402_, v___x_1430_);
v___x_1432_ = l_Lean_Syntax_node6(v___y_1331_, v___x_1393_, v___x_1394_, v___x_1389_, v___x_1389_, v___x_1398_, v___x_1400_, v___x_1431_);
v___x_1433_ = l_Lean_Syntax_node4(v___y_1331_, v___x_1383_, v___x_1388_, v___x_1389_, v___x_1391_, v___x_1432_);
v___x_1434_ = l_Lean_Syntax_node2(v___y_1331_, v___x_1380_, v___x_1381_, v___x_1433_);
v___x_1435_ = lean_unsigned_to_nat(9u);
v___x_1436_ = lean_mk_empty_array_with_capacity(v___x_1435_);
v___x_1437_ = lean_array_push(v___x_1436_, v___x_1344_);
v___x_1438_ = lean_array_push(v___x_1437_, v___x_1358_);
v___x_1439_ = lean_array_push(v___x_1438_, v___y_1334_);
v___x_1440_ = lean_array_push(v___x_1439_, v___x_1359_);
v___x_1441_ = lean_array_push(v___x_1440_, v___x_1366_);
v___x_1442_ = lean_array_push(v___x_1441_, v___x_1368_);
v___x_1443_ = lean_array_push(v___x_1442_, v___x_1376_);
v___x_1444_ = lean_array_push(v___x_1443_, v___x_1378_);
v___x_1445_ = lean_array_push(v___x_1444_, v___x_1434_);
lean_inc(v___y_1333_);
v___x_1446_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1446_, 0, v___y_1331_);
lean_ctor_set(v___x_1446_, 1, v___y_1333_);
lean_ctor_set(v___x_1446_, 2, v___x_1445_);
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
return v___x_1447_;
}
v___jp_1448_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1455_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1456_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
v___x_1457_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
v___x_1458_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
v___x_1459_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1460_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_661_) == 1)
{
lean_object* v_val_1461_; lean_object* v___x_1462_; 
v_val_1461_ = lean_ctor_get(v_doc_x3f_661_, 0);
lean_inc(v_val_1461_);
lean_dec_ref_known(v_doc_x3f_661_, 1);
v___x_1462_ = l_Array_mkArray1___redArg(v_val_1461_);
v___y_1330_ = v___y_1449_;
v___y_1331_ = v___y_1452_;
v___y_1332_ = v___x_1460_;
v___y_1333_ = v___x_1458_;
v___y_1334_ = v___y_1450_;
v___y_1335_ = v___y_1451_;
v___y_1336_ = v___x_1457_;
v___y_1337_ = v___y_1453_;
v___y_1338_ = v___x_1459_;
v___y_1339_ = v_a_1454_;
v___y_1340_ = v___x_1455_;
v___y_1341_ = v___x_1456_;
v___y_1342_ = v___x_1462_;
goto v___jp_1329_;
}
else
{
lean_object* v___x_1463_; 
lean_dec(v_doc_x3f_661_);
v___x_1463_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_1330_ = v___y_1449_;
v___y_1331_ = v___y_1452_;
v___y_1332_ = v___x_1460_;
v___y_1333_ = v___x_1458_;
v___y_1334_ = v___y_1450_;
v___y_1335_ = v___y_1451_;
v___y_1336_ = v___x_1457_;
v___y_1337_ = v___y_1453_;
v___y_1338_ = v___x_1459_;
v___y_1339_ = v_a_1454_;
v___y_1340_ = v___x_1455_;
v___y_1341_ = v___x_1456_;
v___y_1342_ = v___x_1463_;
goto v___jp_1329_;
}
}
v___jp_1464_:
{
lean_object* v___x_1470_; 
lean_inc(v___y_1469_);
lean_inc(v_k_664_);
v___x_1470_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_664_, v_attrKind_663_, v_attrs_x3f_662_, v___y_1469_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1472_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
v___x_1472_ = l_Lean_Elab_Command_getRef___redArg(v___y_1467_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v___x_1474_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1467_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v_quotContext_x3f_1476_; lean_object* v___x_1477_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
v_quotContext_x3f_1476_ = lean_ctor_get(v___y_1467_, 5);
v___x_1477_ = l_Lean_SourceInfo_fromRef(v_a_1473_, v___y_1466_);
lean_dec(v_a_1473_);
if (lean_obj_tag(v_quotContext_x3f_1476_) == 0)
{
lean_object* v___x_1478_; lean_object* v_a_1479_; 
v___x_1478_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1468_);
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref(v___x_1478_);
v___y_1163_ = v___y_1465_;
v___y_1164_ = v_a_1471_;
v___y_1165_ = v_a_1475_;
v___y_1166_ = v___x_1477_;
v_a_1167_ = v_a_1479_;
goto v___jp_1162_;
}
else
{
lean_object* v_val_1480_; 
v_val_1480_ = lean_ctor_get(v_quotContext_x3f_1476_, 0);
lean_inc(v_val_1480_);
v___y_1163_ = v___y_1465_;
v___y_1164_ = v_a_1471_;
v___y_1165_ = v_a_1475_;
v___y_1166_ = v___x_1477_;
v_a_1167_ = v_val_1480_;
goto v___jp_1162_;
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec(v_a_1473_);
lean_dec(v_a_1471_);
lean_dec(v___y_1465_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1481_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1474_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1474_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
else
{
lean_dec(v_a_1471_);
lean_dec(v___y_1465_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
return v___x_1472_;
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec(v___y_1465_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1489_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1470_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1470_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
v___jp_1497_:
{
lean_object* v___x_1501_; 
lean_inc(v_attrKind_663_);
v___x_1501_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_663_);
if (lean_obj_tag(v_expty_x3f_666_) == 1)
{
lean_object* v_val_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; 
lean_del_object(v___x_676_);
v_val_1502_ = lean_ctor_get(v_expty_x3f_666_, 0);
lean_inc(v_val_1502_);
lean_dec_ref_known(v_expty_x3f_666_, 1);
v___x_1503_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v___x_1504_ = lean_name_eq(v_catName_1498_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1505_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__56));
v___x_1506_ = lean_name_eq(v_catName_1498_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_dec(v___x_1501_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_attrKind_663_);
lean_dec(v_doc_x3f_661_);
v___x_1507_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__58, &l_Lean_Elab_Command_elabElabRulesAux___closed__58_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__58);
v___x_1508_ = l_Lean_MessageData_ofName(v_catName_1498_);
v___x_1509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1507_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__60, &l_Lean_Elab_Command_elabElabRulesAux___closed__60_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__60);
v___x_1511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1509_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_val_1502_, v___x_1511_, v___y_1499_, v___y_1500_);
lean_dec(v_val_1502_);
return v___x_1512_;
}
else
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec(v_catName_1498_);
v___x_1513_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__62));
lean_inc(v_k_664_);
v___x_1514_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_664_, v_attrKind_663_, v_attrs_x3f_662_, v___x_1513_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1516_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
v___x_1516_ = l_Lean_Elab_Command_getRef___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1518_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v___x_1518_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v_quotContext_x3f_1520_; lean_object* v___x_1521_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v_quotContext_x3f_1520_ = lean_ctor_get(v___y_1499_, 5);
v___x_1521_ = l_Lean_SourceInfo_fromRef(v_a_1517_, v___x_1504_);
lean_dec(v_a_1517_);
if (lean_obj_tag(v_quotContext_x3f_1520_) == 0)
{
lean_object* v___x_1522_; lean_object* v_a_1523_; 
v___x_1522_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1500_);
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref(v___x_1522_);
v___y_1449_ = v_val_1502_;
v___y_1450_ = v___x_1501_;
v___y_1451_ = v_a_1515_;
v___y_1452_ = v___x_1521_;
v___y_1453_ = v_a_1519_;
v_a_1454_ = v_a_1523_;
goto v___jp_1448_;
}
else
{
lean_object* v_val_1524_; 
v_val_1524_ = lean_ctor_get(v_quotContext_x3f_1520_, 0);
lean_inc(v_val_1524_);
v___y_1449_ = v_val_1502_;
v___y_1450_ = v___x_1501_;
v___y_1451_ = v_a_1515_;
v___y_1452_ = v___x_1521_;
v___y_1453_ = v_a_1519_;
v_a_1454_ = v_val_1524_;
goto v___jp_1448_;
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec(v_a_1517_);
lean_dec(v_a_1515_);
lean_dec(v_val_1502_);
lean_dec(v___x_1501_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1525_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1518_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1518_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
else
{
lean_dec(v_a_1515_);
lean_dec(v_val_1502_);
lean_dec(v___x_1501_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
return v___x_1516_;
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec(v_val_1502_);
lean_dec(v___x_1501_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1533_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1514_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1514_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
lean_dec(v_catName_1498_);
v___x_1541_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__64));
lean_inc(v_k_664_);
v___x_1542_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_664_, v_attrKind_663_, v_attrs_x3f_662_, v___x_1541_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1544_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v___x_1544_ = l_Lean_Elab_Command_getRef___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1546_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
v___x_1546_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v_quotContext_x3f_1548_; uint8_t v___x_1549_; lean_object* v___x_1550_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1546_, 1);
v_quotContext_x3f_1548_ = lean_ctor_get(v___y_1499_, 5);
v___x_1549_ = 0;
v___x_1550_ = l_Lean_SourceInfo_fromRef(v_a_1545_, v___x_1549_);
lean_dec(v_a_1545_);
if (lean_obj_tag(v_quotContext_x3f_1548_) == 0)
{
lean_object* v___x_1551_; lean_object* v_a_1552_; 
v___x_1551_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1500_);
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref(v___x_1551_);
v___y_1314_ = v_val_1502_;
v___y_1315_ = v___x_1501_;
v___y_1316_ = v_a_1547_;
v___y_1317_ = v_a_1543_;
v___y_1318_ = v___x_1550_;
v_a_1319_ = v_a_1552_;
goto v___jp_1313_;
}
else
{
lean_object* v_val_1553_; 
v_val_1553_ = lean_ctor_get(v_quotContext_x3f_1548_, 0);
lean_inc(v_val_1553_);
v___y_1314_ = v_val_1502_;
v___y_1315_ = v___x_1501_;
v___y_1316_ = v_a_1547_;
v___y_1317_ = v_a_1543_;
v___y_1318_ = v___x_1550_;
v_a_1319_ = v_val_1553_;
goto v___jp_1313_;
}
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_dec(v_a_1545_);
lean_dec(v_a_1543_);
lean_dec(v_val_1502_);
lean_dec(v___x_1501_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1554_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1546_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1546_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_dec(v_a_1543_);
lean_dec(v_val_1502_);
lean_dec(v___x_1501_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
return v___x_1544_;
}
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec(v_val_1502_);
lean_dec(v___x_1501_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1562_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1542_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1542_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
}
else
{
lean_object* v___x_1570_; uint8_t v___x_1571_; 
lean_dec(v_expty_x3f_666_);
v___x_1570_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
v___x_1571_ = lean_name_eq(v_catName_1498_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; uint8_t v___x_1573_; 
lean_del_object(v___x_676_);
v___x_1572_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__66));
v___x_1573_ = lean_name_eq(v_catName_1498_, v___x_1572_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1574_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__68));
v___x_1575_ = lean_name_eq(v_catName_1498_, v___x_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__70));
v___x_1577_ = lean_name_eq(v_catName_1498_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; uint8_t v___x_1579_; 
v___x_1578_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__56));
v___x_1579_ = lean_name_eq(v_catName_1498_, v___x_1578_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_dec(v___x_1501_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_attrKind_663_);
lean_dec(v_doc_x3f_661_);
v___x_1580_ = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__72, &l_Lean_Elab_Command_elabElabRulesAux___closed__72_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__72);
v___x_1581_ = l_Lean_MessageData_ofName(v_catName_1498_);
v___x_1582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1580_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
v___x_1584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v___x_1584_, v___y_1499_, v___y_1500_);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_dec(v_catName_1498_);
v___x_1586_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__62));
lean_inc(v_k_664_);
v___x_1587_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_664_, v_attrKind_663_, v_attrs_x3f_662_, v___x_1586_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v___x_1589_ = l_Lean_Elab_Command_getRef___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1591_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v___x_1591_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v_quotContext_x3f_1593_; lean_object* v___x_1594_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1591_, 1);
v_quotContext_x3f_1593_ = lean_ctor_get(v___y_1499_, 5);
v___x_1594_ = l_Lean_SourceInfo_fromRef(v_a_1590_, v___x_1577_);
lean_dec(v_a_1590_);
if (lean_obj_tag(v_quotContext_x3f_1593_) == 0)
{
lean_object* v___x_1595_; lean_object* v_a_1596_; 
v___x_1595_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1500_);
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref(v___x_1595_);
v___y_1050_ = v___x_1501_;
v___y_1051_ = v___x_1594_;
v___y_1052_ = v_a_1592_;
v___y_1053_ = v_a_1588_;
v_a_1054_ = v_a_1596_;
goto v___jp_1049_;
}
else
{
lean_object* v_val_1597_; 
v_val_1597_ = lean_ctor_get(v_quotContext_x3f_1593_, 0);
lean_inc(v_val_1597_);
v___y_1050_ = v___x_1501_;
v___y_1051_ = v___x_1594_;
v___y_1052_ = v_a_1592_;
v___y_1053_ = v_a_1588_;
v_a_1054_ = v_val_1597_;
goto v___jp_1049_;
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v_a_1590_);
lean_dec(v_a_1588_);
lean_dec(v___x_1501_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1598_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1591_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1591_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
else
{
lean_dec(v_a_1588_);
lean_dec(v___x_1501_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
return v___x_1589_;
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec(v___x_1501_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1606_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1587_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1587_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
else
{
lean_dec(v_catName_1498_);
v___y_1465_ = v___x_1501_;
v___y_1466_ = v___x_1573_;
v___y_1467_ = v___y_1499_;
v___y_1468_ = v___y_1500_;
v___y_1469_ = v___x_1574_;
goto v___jp_1464_;
}
}
else
{
lean_dec(v_catName_1498_);
v___y_1465_ = v___x_1501_;
v___y_1466_ = v___x_1573_;
v___y_1467_ = v___y_1499_;
v___y_1468_ = v___y_1500_;
v___y_1469_ = v___x_1574_;
goto v___jp_1464_;
}
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
lean_dec(v_catName_1498_);
v___x_1614_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__74));
lean_inc(v_k_664_);
v___x_1615_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_664_, v_attrKind_663_, v_attrs_x3f_662_, v___x_1614_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1617_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___x_1615_, 1);
v___x_1617_ = l_Lean_Elab_Command_getRef___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1619_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1617_, 1);
v___x_1619_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v_quotContext_x3f_1621_; lean_object* v___x_1622_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
v_quotContext_x3f_1621_ = lean_ctor_get(v___y_1499_, 5);
v___x_1622_ = l_Lean_SourceInfo_fromRef(v_a_1618_, v___x_1571_);
lean_dec(v_a_1618_);
if (lean_obj_tag(v_quotContext_x3f_1621_) == 0)
{
lean_object* v___x_1623_; lean_object* v_a_1624_; 
v___x_1623_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1500_);
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref(v___x_1623_);
v___y_912_ = v___x_1501_;
v___y_913_ = v_a_1620_;
v___y_914_ = v_a_1616_;
v___y_915_ = v___x_1622_;
v_a_916_ = v_a_1624_;
goto v___jp_911_;
}
else
{
lean_object* v_val_1625_; 
v_val_1625_ = lean_ctor_get(v_quotContext_x3f_1621_, 0);
lean_inc(v_val_1625_);
v___y_912_ = v___x_1501_;
v___y_913_ = v_a_1620_;
v___y_914_ = v_a_1616_;
v___y_915_ = v___x_1622_;
v_a_916_ = v_val_1625_;
goto v___jp_911_;
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_dec(v_a_1618_);
lean_dec(v_a_1616_);
lean_dec(v___x_1501_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1626_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1619_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1619_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
else
{
lean_dec(v_a_1616_);
lean_dec(v___x_1501_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
return v___x_1617_;
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_dec(v___x_1501_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1634_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1615_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1615_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
}
else
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_dec(v_catName_1498_);
v___x_1642_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__64));
lean_inc(v_k_664_);
v___x_1643_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(v_k_664_, v_attrKind_663_, v_attrs_x3f_662_, v___x_1642_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1645_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref_known(v___x_1643_, 1);
v___x_1645_ = l_Lean_Elab_Command_getRef___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v___x_1647_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1499_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v_quotContext_x3f_1649_; uint8_t v___x_1650_; lean_object* v___x_1651_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v_quotContext_x3f_1649_ = lean_ctor_get(v___y_1499_, 5);
v___x_1650_ = 0;
v___x_1651_ = l_Lean_SourceInfo_fromRef(v_a_1646_, v___x_1650_);
lean_dec(v_a_1646_);
if (lean_obj_tag(v_quotContext_x3f_1649_) == 0)
{
lean_object* v___x_1652_; lean_object* v_a_1653_; 
v___x_1652_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1500_);
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref(v___x_1652_);
v___y_798_ = v___x_1501_;
v___y_799_ = v_a_1648_;
v___y_800_ = v___x_1651_;
v___y_801_ = v_a_1644_;
v_a_802_ = v_a_1653_;
goto v___jp_797_;
}
else
{
lean_object* v_val_1654_; 
v_val_1654_ = lean_ctor_get(v_quotContext_x3f_1649_, 0);
lean_inc(v_val_1654_);
v___y_798_ = v___x_1501_;
v___y_799_ = v_a_1648_;
v___y_800_ = v___x_1651_;
v___y_801_ = v_a_1644_;
v_a_802_ = v_val_1654_;
goto v___jp_797_;
}
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_dec(v_a_1646_);
lean_dec(v_a_1644_);
lean_dec(v___x_1501_);
lean_del_object(v___x_676_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1655_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1647_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1647_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
else
{
lean_dec(v_a_1644_);
lean_dec(v___x_1501_);
lean_del_object(v___x_676_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
return v___x_1645_;
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
lean_dec(v___x_1501_);
lean_del_object(v___x_676_);
lean_dec(v_a_674_);
lean_dec(v_k_664_);
lean_dec(v_doc_x3f_661_);
v_a_1663_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1643_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1643_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
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
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec(v_expty_x3f_666_);
lean_dec(v_k_664_);
lean_dec(v_attrKind_663_);
lean_dec(v_doc_x3f_661_);
v_a_1685_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_673_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_673_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object* v_doc_x3f_1693_, lean_object* v_attrs_x3f_1694_, lean_object* v_attrKind_1695_, lean_object* v_k_1696_, lean_object* v_cat_x3f_1697_, lean_object* v_expty_x3f_1698_, lean_object* v_alts_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_Elab_Command_elabElabRulesAux(v_doc_x3f_1693_, v_attrs_x3f_1694_, v_attrKind_1695_, v_k_1696_, v_cat_x3f_1697_, v_expty_x3f_1698_, v_alts_1699_, v_a_1700_, v_a_1701_);
lean_dec(v_a_1701_);
lean_dec_ref(v_a_1700_);
lean_dec(v_cat_x3f_1697_);
lean_dec(v_attrs_x3f_1694_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(lean_object* v_00_u03b1_1704_, lean_object* v_ref_1705_, lean_object* v_msg_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_ref_1705_, v_msg_1706_, v___y_1707_, v___y_1708_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___boxed(lean_object* v_00_u03b1_1711_, lean_object* v_ref_1712_, lean_object* v_msg_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(v_00_u03b1_1711_, v_ref_1712_, v_msg_1713_, v___y_1714_, v___y_1715_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v_ref_1712_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(lean_object* v_msgData_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msgData_1718_, v___y_1720_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___boxed(lean_object* v_msgData_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(v_msgData_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(lean_object* v_00_u03b1_1728_, lean_object* v_msg_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_1729_, v___y_1730_, v___y_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___boxed(lean_object* v_00_u03b1_1734_, lean_object* v_msg_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(v_00_u03b1_1734_, v_msg_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(lean_object* v_msgData_1740_, lean_object* v_macroStack_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_msgData_1740_, v_macroStack_1741_, v___y_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___boxed(lean_object* v_msgData_1746_, lean_object* v_macroStack_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(v_msgData_1746_, v_macroStack_1747_, v___y_1748_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0(lean_object* v_x_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0___boxed(lean_object* v_x_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_Elab_Command_elabElabRules___lam__0(v_x_1754_);
lean_dec(v_x_1754_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1(lean_object* v___x_1760_, lean_object* v___x_1761_, lean_object* v_attrKind_1762_, lean_object* v_expty_x3f_1763_, lean_object* v___f_1764_, lean_object* v_cat_x3f_1765_, lean_object* v___x_1766_, lean_object* v___x_1767_, lean_object* v_attrs_x3f_1768_, lean_object* v___x_1769_, lean_object* v___x_1770_, lean_object* v___x_1771_, lean_object* v_doc_x3f_1772_, lean_object* v_kind_x3f_1773_, lean_object* v_alts_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Elab_Command_getRef___redArg(v___y_1775_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1780_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref_known(v___x_1778_, 1);
v___x_1780_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1775_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1879_; 
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1879_ == 0)
{
lean_object* v_unused_1880_; 
v_unused_1880_ = lean_ctor_get(v___x_1780_, 0);
lean_dec(v_unused_1880_);
v___x_1782_ = v___x_1780_;
v_isShared_1783_ = v_isSharedCheck_1879_;
goto v_resetjp_1781_;
}
else
{
lean_dec(v___x_1780_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1879_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v_quotContext_x3f_1784_; uint8_t v___x_1785_; lean_object* v___x_1786_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; 
v_quotContext_x3f_1784_ = lean_ctor_get(v___y_1775_, 5);
v___x_1785_ = 0;
v___x_1786_ = l_Lean_SourceInfo_fromRef(v_a_1779_, v___x_1785_);
lean_dec(v_a_1779_);
if (lean_obj_tag(v_quotContext_x3f_1784_) == 0)
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_1776_);
lean_dec_ref(v___x_1878_);
goto v___jp_1872_;
}
else
{
goto v___jp_1872_;
}
v___jp_1787_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
lean_inc_ref_n(v___y_1790_, 2);
v___x_1796_ = l_Array_append___redArg(v___y_1790_, v___y_1795_);
lean_dec_ref(v___y_1795_);
lean_inc_n(v___y_1789_, 2);
lean_inc_n(v___x_1786_, 3);
v___x_1797_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1786_);
lean_ctor_set(v___x_1797_, 1, v___y_1789_);
lean_ctor_set(v___x_1797_, 2, v___x_1796_);
v___x_1798_ = l_Array_append___redArg(v___y_1790_, v_alts_1774_);
v___x_1799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1786_);
lean_ctor_set(v___x_1799_, 1, v___y_1789_);
lean_ctor_set(v___x_1799_, 2, v___x_1798_);
v___x_1800_ = l_Lean_Syntax_node1(v___x_1786_, v___x_1760_, v___x_1799_);
v___x_1801_ = l_Lean_Syntax_node8(v___x_1786_, v___x_1761_, v___y_1794_, v___y_1793_, v_attrKind_1762_, v___y_1788_, v___y_1792_, v___y_1791_, v___x_1797_, v___x_1800_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v___x_1801_);
v___x_1803_ = v___x_1782_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
v___jp_1805_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_inc_ref(v___y_1808_);
v___x_1813_ = l_Array_append___redArg(v___y_1808_, v___y_1812_);
lean_dec_ref(v___y_1812_);
lean_inc(v___y_1807_);
lean_inc(v___x_1786_);
v___x_1814_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1786_);
lean_ctor_set(v___x_1814_, 1, v___y_1807_);
lean_ctor_set(v___x_1814_, 2, v___x_1813_);
if (lean_obj_tag(v_expty_x3f_1763_) == 1)
{
lean_object* v_val_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_dec_ref(v___f_1764_);
v_val_1815_ = lean_ctor_get(v_expty_x3f_1763_, 0);
lean_inc(v_val_1815_);
lean_dec_ref_known(v_expty_x3f_1763_, 1);
v___x_1816_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___x_1786_);
v___x_1817_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1786_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___x_1818_ = l_Array_mkArray2___redArg(v___x_1817_, v_val_1815_);
v___y_1788_ = v___y_1806_;
v___y_1789_ = v___y_1807_;
v___y_1790_ = v___y_1808_;
v___y_1791_ = v___x_1814_;
v___y_1792_ = v___y_1809_;
v___y_1793_ = v___y_1810_;
v___y_1794_ = v___y_1811_;
v___y_1795_ = v___x_1818_;
goto v___jp_1787_;
}
else
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_apply_1(v___f_1764_, v_expty_x3f_1763_);
v___y_1788_ = v___y_1806_;
v___y_1789_ = v___y_1807_;
v___y_1790_ = v___y_1808_;
v___y_1791_ = v___x_1814_;
v___y_1792_ = v___y_1809_;
v___y_1793_ = v___y_1810_;
v___y_1794_ = v___y_1811_;
v___y_1795_ = v___x_1819_;
goto v___jp_1787_;
}
}
v___jp_1820_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_inc_ref(v___y_1823_);
v___x_1827_ = l_Array_append___redArg(v___y_1823_, v___y_1826_);
lean_dec_ref(v___y_1826_);
lean_inc(v___y_1822_);
lean_inc(v___x_1786_);
v___x_1828_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1786_);
lean_ctor_set(v___x_1828_, 1, v___y_1822_);
lean_ctor_set(v___x_1828_, 2, v___x_1827_);
if (lean_obj_tag(v_cat_x3f_1765_) == 1)
{
lean_object* v_val_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v_val_1829_ = lean_ctor_get(v_cat_x3f_1765_, 0);
lean_inc(v_val_1829_);
lean_dec_ref_known(v_cat_x3f_1765_, 1);
v___x_1830_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(v___x_1786_);
v___x_1831_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1786_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = l_Array_mkArray2___redArg(v___x_1831_, v_val_1829_);
v___y_1806_ = v___y_1821_;
v___y_1807_ = v___y_1822_;
v___y_1808_ = v___y_1823_;
v___y_1809_ = v___x_1828_;
v___y_1810_ = v___y_1824_;
v___y_1811_ = v___y_1825_;
v___y_1812_ = v___x_1832_;
goto v___jp_1805_;
}
else
{
lean_object* v___x_1833_; 
lean_inc_ref(v___f_1764_);
v___x_1833_ = lean_apply_1(v___f_1764_, v_cat_x3f_1765_);
v___y_1806_ = v___y_1821_;
v___y_1807_ = v___y_1822_;
v___y_1808_ = v___y_1823_;
v___y_1809_ = v___x_1828_;
v___y_1810_ = v___y_1824_;
v___y_1811_ = v___y_1825_;
v___y_1812_ = v___x_1833_;
goto v___jp_1805_;
}
}
v___jp_1834_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_inc_ref(v___y_1836_);
v___x_1839_ = l_Array_append___redArg(v___y_1836_, v___y_1838_);
lean_dec_ref(v___y_1838_);
lean_inc(v___y_1835_);
lean_inc_n(v___x_1786_, 2);
v___x_1840_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1786_);
lean_ctor_set(v___x_1840_, 1, v___y_1835_);
lean_ctor_set(v___x_1840_, 2, v___x_1839_);
v___x_1841_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1786_);
lean_ctor_set(v___x_1841_, 1, v___x_1766_);
if (lean_obj_tag(v_kind_x3f_1773_) == 0)
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_mk_empty_array_with_capacity(v___x_1767_);
v___y_1821_ = v___x_1841_;
v___y_1822_ = v___y_1835_;
v___y_1823_ = v___y_1836_;
v___y_1824_ = v___x_1840_;
v___y_1825_ = v___y_1837_;
v___y_1826_ = v___x_1842_;
goto v___jp_1820_;
}
else
{
lean_object* v_val_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v_val_1843_ = lean_ctor_get(v_kind_x3f_1773_, 0);
lean_inc(v_val_1843_);
lean_dec_ref_known(v_kind_x3f_1773_, 1);
v___x_1844_ = l_Lean_mkIdent(v_val_1843_);
v___x_1845_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc_n(v___x_1786_, 4);
v___x_1846_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1786_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__2));
v___x_1848_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1786_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
v___x_1850_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1786_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_1852_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1786_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = l_Array_mkArray5___redArg(v___x_1846_, v___x_1848_, v___x_1850_, v___x_1844_, v___x_1852_);
v___y_1821_ = v___x_1841_;
v___y_1822_ = v___y_1835_;
v___y_1823_ = v___y_1836_;
v___y_1824_ = v___x_1840_;
v___y_1825_ = v___y_1837_;
v___y_1826_ = v___x_1853_;
goto v___jp_1820_;
}
}
v___jp_1854_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
lean_inc_ref(v___y_1856_);
v___x_1858_ = l_Array_append___redArg(v___y_1856_, v___y_1857_);
lean_dec_ref(v___y_1857_);
lean_inc(v___y_1855_);
lean_inc(v___x_1786_);
v___x_1859_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1786_);
lean_ctor_set(v___x_1859_, 1, v___y_1855_);
lean_ctor_set(v___x_1859_, 2, v___x_1858_);
if (lean_obj_tag(v_attrs_x3f_1768_) == 1)
{
lean_object* v_val_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_val_1860_ = lean_ctor_get(v_attrs_x3f_1768_, 0);
v___x_1861_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
v___x_1862_ = l_Lean_Name_mkStr4(v___x_1769_, v___x_1770_, v___x_1771_, v___x_1861_);
v___x_1863_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc_n(v___x_1786_, 4);
v___x_1864_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1786_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
lean_inc_ref(v___y_1856_);
v___x_1865_ = l_Array_append___redArg(v___y_1856_, v_val_1860_);
lean_inc(v___y_1855_);
v___x_1866_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1786_);
lean_ctor_set(v___x_1866_, 1, v___y_1855_);
lean_ctor_set(v___x_1866_, 2, v___x_1865_);
v___x_1867_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_1868_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1786_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = l_Lean_Syntax_node3(v___x_1786_, v___x_1862_, v___x_1864_, v___x_1866_, v___x_1868_);
v___x_1870_ = l_Array_mkArray1___redArg(v___x_1869_);
v___y_1835_ = v___y_1855_;
v___y_1836_ = v___y_1856_;
v___y_1837_ = v___x_1859_;
v___y_1838_ = v___x_1870_;
goto v___jp_1834_;
}
else
{
lean_object* v___x_1871_; 
lean_dec_ref(v___x_1771_);
lean_dec_ref(v___x_1770_);
lean_dec_ref(v___x_1769_);
v___x_1871_ = lean_mk_empty_array_with_capacity(v___x_1767_);
v___y_1835_ = v___y_1855_;
v___y_1836_ = v___y_1856_;
v___y_1837_ = v___x_1859_;
v___y_1838_ = v___x_1871_;
goto v___jp_1834_;
}
}
v___jp_1872_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_1874_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v_doc_x3f_1772_) == 1)
{
lean_object* v_val_1875_; lean_object* v___x_1876_; 
v_val_1875_ = lean_ctor_get(v_doc_x3f_1772_, 0);
lean_inc(v_val_1875_);
lean_dec_ref_known(v_doc_x3f_1772_, 1);
v___x_1876_ = l_Array_mkArray1___redArg(v_val_1875_);
v___y_1855_ = v___x_1873_;
v___y_1856_ = v___x_1874_;
v___y_1857_ = v___x_1876_;
goto v___jp_1854_;
}
else
{
lean_object* v___x_1877_; 
lean_dec(v_doc_x3f_1772_);
v___x_1877_ = lean_mk_empty_array_with_capacity(v___x_1767_);
v___y_1855_ = v___x_1873_;
v___y_1856_ = v___x_1874_;
v___y_1857_ = v___x_1877_;
goto v___jp_1854_;
}
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec(v_a_1779_);
lean_dec(v_kind_x3f_1773_);
lean_dec(v_doc_x3f_1772_);
lean_dec_ref(v___x_1771_);
lean_dec_ref(v___x_1770_);
lean_dec_ref(v___x_1769_);
lean_dec_ref(v___x_1766_);
lean_dec(v_cat_x3f_1765_);
lean_dec_ref(v___f_1764_);
lean_dec(v_expty_x3f_1763_);
lean_dec(v_attrKind_1762_);
lean_dec(v___x_1761_);
lean_dec(v___x_1760_);
v_a_1881_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1780_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1780_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_dec(v_kind_x3f_1773_);
lean_dec(v_doc_x3f_1772_);
lean_dec_ref(v___x_1771_);
lean_dec_ref(v___x_1770_);
lean_dec_ref(v___x_1769_);
lean_dec_ref(v___x_1766_);
lean_dec(v_cat_x3f_1765_);
lean_dec_ref(v___f_1764_);
lean_dec(v_expty_x3f_1763_);
lean_dec(v_attrKind_1762_);
lean_dec(v___x_1761_);
lean_dec(v___x_1760_);
v_a_1889_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1778_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1778_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___boxed(lean_object** _args){
lean_object* v___x_1897_ = _args[0];
lean_object* v___x_1898_ = _args[1];
lean_object* v_attrKind_1899_ = _args[2];
lean_object* v_expty_x3f_1900_ = _args[3];
lean_object* v___f_1901_ = _args[4];
lean_object* v_cat_x3f_1902_ = _args[5];
lean_object* v___x_1903_ = _args[6];
lean_object* v___x_1904_ = _args[7];
lean_object* v_attrs_x3f_1905_ = _args[8];
lean_object* v___x_1906_ = _args[9];
lean_object* v___x_1907_ = _args[10];
lean_object* v___x_1908_ = _args[11];
lean_object* v_doc_x3f_1909_ = _args[12];
lean_object* v_kind_x3f_1910_ = _args[13];
lean_object* v_alts_1911_ = _args[14];
lean_object* v___y_1912_ = _args[15];
lean_object* v___y_1913_ = _args[16];
lean_object* v___y_1914_ = _args[17];
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_Elab_Command_elabElabRules___lam__1(v___x_1897_, v___x_1898_, v_attrKind_1899_, v_expty_x3f_1900_, v___f_1901_, v_cat_x3f_1902_, v___x_1903_, v___x_1904_, v_attrs_x3f_1905_, v___x_1906_, v___x_1907_, v___x_1908_, v_doc_x3f_1909_, v_kind_x3f_1910_, v_alts_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec_ref(v_alts_1911_);
lean_dec(v_attrs_x3f_1905_);
lean_dec(v___x_1904_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2(lean_object* v___f_1944_, lean_object* v_stx_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; uint8_t v___x_1953_; 
v___x_1949_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_1950_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_1951_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
v___x_1952_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
lean_inc(v_stx_1945_);
v___x_1953_ = l_Lean_Syntax_isOfKind(v_stx_1945_, v___x_1952_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; 
lean_dec(v_stx_1945_);
lean_dec_ref(v___f_1944_);
v___x_1954_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_1954_;
}
else
{
lean_object* v___x_1955_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v_expty_x3f_1963_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v_cat_x3f_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v_expty_x3f_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v_cat_x3f_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v_attrs_x3f_2061_; lean_object* v_doc_x3f_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_1955_ = lean_unsigned_to_nat(0u);
v___x_2108_ = l_Lean_Syntax_getArg(v_stx_1945_, v___x_1955_);
v___x_2109_ = l_Lean_Syntax_isNone(v___x_2108_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2110_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2108_);
v___x_2111_ = l_Lean_Syntax_matchesNull(v___x_2108_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; 
lean_dec(v___x_2108_);
lean_dec(v_stx_1945_);
lean_dec_ref(v___f_1944_);
v___x_2112_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2112_;
}
else
{
lean_object* v_doc_x3f_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; 
v_doc_x3f_2113_ = l_Lean_Syntax_getArg(v___x_2108_, v___x_1955_);
lean_dec(v___x_2108_);
v___x_2114_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7));
lean_inc(v_doc_x3f_2113_);
v___x_2115_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2113_, v___x_2114_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; 
lean_dec(v_doc_x3f_2113_);
lean_dec(v_stx_1945_);
lean_dec_ref(v___f_1944_);
v___x_2116_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2116_;
}
else
{
lean_object* v___x_2117_; 
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v_doc_x3f_2113_);
v_doc_x3f_2092_ = v___x_2117_;
v___y_2093_ = v___y_1946_;
v___y_2094_ = v___y_1947_;
goto v___jp_2091_;
}
}
}
else
{
lean_object* v___x_2118_; 
lean_dec(v___x_2108_);
v___x_2118_ = lean_box(0);
v_doc_x3f_2092_ = v___x_2118_;
v___y_2093_ = v___y_1946_;
v___y_2094_ = v___y_1947_;
goto v___jp_2091_;
}
v___jp_1956_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1964_ = lean_unsigned_to_nat(7u);
v___x_1965_ = l_Lean_Syntax_getArg(v_stx_1945_, v___x_1964_);
lean_dec(v_stx_1945_);
v___x_1966_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_1967_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__2));
lean_inc(v___x_1965_);
v___x_1968_ = l_Lean_Syntax_isOfKind(v___x_1965_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; 
lean_dec(v___x_1965_);
lean_dec(v_expty_x3f_1963_);
lean_dec(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___f_1944_);
v___x_1969_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_1969_;
}
else
{
lean_object* v___f_1970_; lean_object* v___x_1971_; lean_object* v_alts_1972_; lean_object* v___x_1973_; 
v___f_1970_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___lam__1___boxed), 18, 13);
lean_closure_set(v___f_1970_, 0, v___x_1967_);
lean_closure_set(v___f_1970_, 1, v___x_1952_);
lean_closure_set(v___f_1970_, 2, v___y_1959_);
lean_closure_set(v___f_1970_, 3, v_expty_x3f_1963_);
lean_closure_set(v___f_1970_, 4, v___f_1944_);
lean_closure_set(v___f_1970_, 5, v___y_1958_);
lean_closure_set(v___f_1970_, 6, v___x_1951_);
lean_closure_set(v___f_1970_, 7, v___x_1955_);
lean_closure_set(v___f_1970_, 8, v___y_1961_);
lean_closure_set(v___f_1970_, 9, v___x_1949_);
lean_closure_set(v___f_1970_, 10, v___x_1950_);
lean_closure_set(v___f_1970_, 11, v___x_1966_);
lean_closure_set(v___f_1970_, 12, v___y_1962_);
v___x_1971_ = l_Lean_Syntax_getArg(v___x_1965_, v___x_1955_);
lean_dec(v___x_1965_);
v_alts_1972_ = l_Lean_Syntax_getArgs(v___x_1971_);
lean_dec(v___x_1971_);
v___x_1973_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(v_alts_1972_, v___x_1951_, v___f_1970_, v___y_1960_, v___y_1957_);
lean_dec_ref(v_alts_1972_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
v_a_1982_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1973_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1973_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
}
v___jp_1990_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_1999_ = lean_unsigned_to_nat(6u);
v___x_2000_ = l_Lean_Syntax_getArg(v_stx_1945_, v___x_1999_);
v___x_2001_ = l_Lean_Syntax_isNone(v___x_2000_);
if (v___x_2001_ == 0)
{
uint8_t v___x_2002_; 
lean_inc(v___x_2000_);
v___x_2002_ = l_Lean_Syntax_matchesNull(v___x_2000_, v___y_1995_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; 
lean_dec(v___x_2000_);
lean_dec(v_cat_x3f_1996_);
lean_dec(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec(v_stx_1945_);
lean_dec_ref(v___f_1944_);
v___x_2003_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2003_;
}
else
{
lean_object* v_expty_x3f_2004_; lean_object* v___x_2005_; 
v_expty_x3f_2004_ = l_Lean_Syntax_getArg(v___x_2000_, v___y_1994_);
lean_dec(v___x_2000_);
v___x_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2005_, 0, v_expty_x3f_2004_);
v___y_1957_ = v___y_1998_;
v___y_1958_ = v_cat_x3f_1996_;
v___y_1959_ = v___y_1991_;
v___y_1960_ = v___y_1997_;
v___y_1961_ = v___y_1992_;
v___y_1962_ = v___y_1993_;
v_expty_x3f_1963_ = v___x_2005_;
goto v___jp_1956_;
}
}
else
{
lean_object* v___x_2006_; 
lean_dec(v___x_2000_);
v___x_2006_ = lean_box(0);
v___y_1957_ = v___y_1998_;
v___y_1958_ = v_cat_x3f_1996_;
v___y_1959_ = v___y_1991_;
v___y_1960_ = v___y_1997_;
v___y_1961_ = v___y_1992_;
v___y_1962_ = v___y_1993_;
v_expty_x3f_1963_ = v___x_2006_;
goto v___jp_1956_;
}
}
v___jp_2007_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2017_ = lean_unsigned_to_nat(7u);
v___x_2018_ = l_Lean_Syntax_getArg(v_stx_1945_, v___x_2017_);
lean_dec(v_stx_1945_);
v___x_2019_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(v___y_2010_);
v___x_2020_ = l_Lean_Name_mkStr4(v___x_1949_, v___x_1950_, v___y_2010_, v___x_2019_);
lean_inc(v___x_2018_);
v___x_2021_ = l_Lean_Syntax_isOfKind(v___x_2018_, v___x_2020_);
lean_dec(v___x_2020_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; 
lean_dec(v___x_2018_);
lean_dec(v_expty_x3f_2014_);
lean_dec(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec(v___y_2009_);
lean_dec(v___y_2008_);
v___x_2022_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2022_;
}
else
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = l_Lean_TSyntax_getId(v___y_2013_);
lean_dec(v___y_2013_);
v___x_2024_ = l_Lean_Elab_Command_resolveSyntaxKind(v___x_2023_, v___y_2015_, v___y_2016_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2026_; lean_object* v_alts_2027_; lean_object* v___x_2028_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2024_, 1);
v___x_2026_ = l_Lean_Syntax_getArg(v___x_2018_, v___x_1955_);
lean_dec(v___x_2018_);
v_alts_2027_ = l_Lean_Syntax_getArgs(v___x_2026_);
lean_dec(v___x_2026_);
v___x_2028_ = l_Lean_Elab_Command_elabElabRulesAux(v___y_2011_, v___y_2008_, v___y_2009_, v_a_2025_, v___y_2012_, v_expty_x3f_2014_, v_alts_2027_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2012_);
lean_dec(v___y_2008_);
return v___x_2028_;
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v___x_2018_);
lean_dec(v_expty_x3f_2014_);
lean_dec(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec(v___y_2009_);
lean_dec(v___y_2008_);
v_a_2029_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2024_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2024_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
v___jp_2037_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
v___x_2048_ = lean_unsigned_to_nat(6u);
v___x_2049_ = l_Lean_Syntax_getArg(v_stx_1945_, v___x_2048_);
v___x_2050_ = l_Lean_Syntax_isNone(v___x_2049_);
if (v___x_2050_ == 0)
{
uint8_t v___x_2051_; 
lean_inc(v___x_2049_);
v___x_2051_ = l_Lean_Syntax_matchesNull(v___x_2049_, v___y_2042_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; 
lean_dec(v___x_2049_);
lean_dec(v_cat_x3f_2045_);
lean_dec(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec(v_stx_1945_);
v___x_2052_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2052_;
}
else
{
lean_object* v_expty_x3f_2053_; lean_object* v___x_2054_; 
v_expty_x3f_2053_ = l_Lean_Syntax_getArg(v___x_2049_, v___y_2038_);
lean_dec(v___x_2049_);
v___x_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2054_, 0, v_expty_x3f_2053_);
v___y_2008_ = v___y_2039_;
v___y_2009_ = v___y_2040_;
v___y_2010_ = v___y_2041_;
v___y_2011_ = v___y_2043_;
v___y_2012_ = v_cat_x3f_2045_;
v___y_2013_ = v___y_2044_;
v_expty_x3f_2014_ = v___x_2054_;
v___y_2015_ = v___y_2046_;
v___y_2016_ = v___y_2047_;
goto v___jp_2007_;
}
}
else
{
lean_object* v___x_2055_; 
lean_dec(v___x_2049_);
v___x_2055_ = lean_box(0);
v___y_2008_ = v___y_2039_;
v___y_2009_ = v___y_2040_;
v___y_2010_ = v___y_2041_;
v___y_2011_ = v___y_2043_;
v___y_2012_ = v_cat_x3f_2045_;
v___y_2013_ = v___y_2044_;
v_expty_x3f_2014_ = v___x_2055_;
v___y_2015_ = v___y_2046_;
v___y_2016_ = v___y_2047_;
goto v___jp_2007_;
}
}
v___jp_2056_:
{
lean_object* v___x_2062_; lean_object* v_attrKind_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; 
v___x_2062_ = lean_unsigned_to_nat(2u);
v_attrKind_2063_ = l_Lean_Syntax_getArg(v_stx_1945_, v___x_2062_);
v___x_2064_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_2065_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v_attrKind_2063_);
v___x_2066_ = l_Lean_Syntax_isOfKind(v_attrKind_2063_, v___x_2065_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; 
lean_dec(v_attrKind_2063_);
lean_dec(v_attrs_x3f_2061_);
lean_dec(v___y_2059_);
lean_dec(v_stx_1945_);
lean_dec_ref(v___f_1944_);
v___x_2067_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2067_;
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2068_ = lean_unsigned_to_nat(4u);
v___x_2069_ = l_Lean_Syntax_getArg(v_stx_1945_, v___x_2068_);
lean_inc(v___x_2069_);
v___x_2070_ = l_Lean_Syntax_matchesNull(v___x_2069_, v___x_1955_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; uint8_t v___x_2072_; 
lean_dec_ref(v___f_1944_);
v___x_2071_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2069_);
v___x_2072_ = l_Lean_Syntax_matchesNull(v___x_2069_, v___x_2071_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; 
lean_dec(v___x_2069_);
lean_dec(v_attrKind_2063_);
lean_dec(v_attrs_x3f_2061_);
lean_dec(v___y_2059_);
lean_dec(v_stx_1945_);
v___x_2073_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2073_;
}
else
{
lean_object* v___x_2074_; lean_object* v_kind_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2074_ = lean_unsigned_to_nat(3u);
v_kind_2075_ = l_Lean_Syntax_getArg(v___x_2069_, v___x_2074_);
lean_dec(v___x_2069_);
v___x_2076_ = l_Lean_Syntax_getArg(v_stx_1945_, v___x_2071_);
v___x_2077_ = l_Lean_Syntax_isNone(v___x_2076_);
if (v___x_2077_ == 0)
{
uint8_t v___x_2078_; 
lean_inc(v___x_2076_);
v___x_2078_ = l_Lean_Syntax_matchesNull(v___x_2076_, v___x_2062_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; 
lean_dec(v___x_2076_);
lean_dec(v_kind_2075_);
lean_dec(v_attrKind_2063_);
lean_dec(v_attrs_x3f_2061_);
lean_dec(v___y_2059_);
lean_dec(v_stx_1945_);
v___x_2079_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2079_;
}
else
{
lean_object* v_cat_x3f_2080_; lean_object* v___x_2081_; 
v_cat_x3f_2080_ = l_Lean_Syntax_getArg(v___x_2076_, v___y_2060_);
lean_dec(v___x_2076_);
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v_cat_x3f_2080_);
v___y_2038_ = v___y_2060_;
v___y_2039_ = v_attrs_x3f_2061_;
v___y_2040_ = v_attrKind_2063_;
v___y_2041_ = v___x_2064_;
v___y_2042_ = v___x_2062_;
v___y_2043_ = v___y_2059_;
v___y_2044_ = v_kind_2075_;
v_cat_x3f_2045_ = v___x_2081_;
v___y_2046_ = v___y_2058_;
v___y_2047_ = v___y_2057_;
goto v___jp_2037_;
}
}
else
{
lean_object* v___x_2082_; 
lean_dec(v___x_2076_);
v___x_2082_ = lean_box(0);
v___y_2038_ = v___y_2060_;
v___y_2039_ = v_attrs_x3f_2061_;
v___y_2040_ = v_attrKind_2063_;
v___y_2041_ = v___x_2064_;
v___y_2042_ = v___x_2062_;
v___y_2043_ = v___y_2059_;
v___y_2044_ = v_kind_2075_;
v_cat_x3f_2045_ = v___x_2082_;
v___y_2046_ = v___y_2058_;
v___y_2047_ = v___y_2057_;
goto v___jp_2037_;
}
}
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
lean_dec(v___x_2069_);
v___x_2083_ = lean_unsigned_to_nat(5u);
v___x_2084_ = l_Lean_Syntax_getArg(v_stx_1945_, v___x_2083_);
v___x_2085_ = l_Lean_Syntax_isNone(v___x_2084_);
if (v___x_2085_ == 0)
{
uint8_t v___x_2086_; 
lean_inc(v___x_2084_);
v___x_2086_ = l_Lean_Syntax_matchesNull(v___x_2084_, v___x_2062_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; 
lean_dec(v___x_2084_);
lean_dec(v_attrKind_2063_);
lean_dec(v_attrs_x3f_2061_);
lean_dec(v___y_2059_);
lean_dec(v_stx_1945_);
lean_dec_ref(v___f_1944_);
v___x_2087_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2087_;
}
else
{
lean_object* v_cat_x3f_2088_; lean_object* v___x_2089_; 
v_cat_x3f_2088_ = l_Lean_Syntax_getArg(v___x_2084_, v___y_2060_);
lean_dec(v___x_2084_);
v___x_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2089_, 0, v_cat_x3f_2088_);
v___y_1991_ = v_attrKind_2063_;
v___y_1992_ = v_attrs_x3f_2061_;
v___y_1993_ = v___y_2059_;
v___y_1994_ = v___y_2060_;
v___y_1995_ = v___x_2062_;
v_cat_x3f_1996_ = v___x_2089_;
v___y_1997_ = v___y_2058_;
v___y_1998_ = v___y_2057_;
goto v___jp_1990_;
}
}
else
{
lean_object* v___x_2090_; 
lean_dec(v___x_2084_);
v___x_2090_ = lean_box(0);
v___y_1991_ = v_attrKind_2063_;
v___y_1992_ = v_attrs_x3f_2061_;
v___y_1993_ = v___y_2059_;
v___y_1994_ = v___y_2060_;
v___y_1995_ = v___x_2062_;
v_cat_x3f_1996_ = v___x_2090_;
v___y_1997_ = v___y_2058_;
v___y_1998_ = v___y_2057_;
goto v___jp_1990_;
}
}
}
}
v___jp_2091_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2095_ = lean_unsigned_to_nat(1u);
v___x_2096_ = l_Lean_Syntax_getArg(v_stx_1945_, v___x_2095_);
v___x_2097_ = l_Lean_Syntax_isNone(v___x_2096_);
if (v___x_2097_ == 0)
{
uint8_t v___x_2098_; 
lean_inc(v___x_2096_);
v___x_2098_ = l_Lean_Syntax_matchesNull(v___x_2096_, v___x_2095_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; 
lean_dec(v___x_2096_);
lean_dec(v_doc_x3f_2092_);
lean_dec(v_stx_1945_);
lean_dec_ref(v___f_1944_);
v___x_2099_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2099_;
}
else
{
lean_object* v___x_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2100_ = l_Lean_Syntax_getArg(v___x_2096_, v___x_1955_);
lean_dec(v___x_2096_);
v___x_2101_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5));
lean_inc(v___x_2100_);
v___x_2102_ = l_Lean_Syntax_isOfKind(v___x_2100_, v___x_2101_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; 
lean_dec(v___x_2100_);
lean_dec(v_doc_x3f_2092_);
lean_dec(v_stx_1945_);
lean_dec_ref(v___f_1944_);
v___x_2103_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2103_;
}
else
{
lean_object* v___x_2104_; lean_object* v_attrs_x3f_2105_; lean_object* v___x_2106_; 
v___x_2104_ = l_Lean_Syntax_getArg(v___x_2100_, v___x_2095_);
lean_dec(v___x_2100_);
v_attrs_x3f_2105_ = l_Lean_Syntax_getArgs(v___x_2104_);
lean_dec(v___x_2104_);
v___x_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2106_, 0, v_attrs_x3f_2105_);
v___y_2057_ = v___y_2094_;
v___y_2058_ = v___y_2093_;
v___y_2059_ = v_doc_x3f_2092_;
v___y_2060_ = v___x_2095_;
v_attrs_x3f_2061_ = v___x_2106_;
goto v___jp_2056_;
}
}
}
else
{
lean_object* v___x_2107_; 
lean_dec(v___x_2096_);
v___x_2107_ = lean_box(0);
v___y_2057_ = v___y_2094_;
v___y_2058_ = v___y_2093_;
v___y_2059_ = v_doc_x3f_2092_;
v___y_2060_ = v___x_2095_;
v_attrs_x3f_2061_ = v___x_2107_;
goto v___jp_2056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___boxed(lean_object* v___f_2119_, lean_object* v_stx_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Lean_Elab_Command_elabElabRules___lam__2(v___f_2119_, v_stx_2120_, v___y_2121_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v___f_2132_; lean_object* v___x_2133_; 
v___f_2132_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___closed__1));
v___x_2133_ = l_Lean_Elab_Command_adaptExpander(v___f_2132_, v_a_2128_, v_a_2129_, v_a_2130_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___boxed(lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_Elab_Command_elabElabRules(v_a_2134_, v_a_2135_, v_a_2136_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1(){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2146_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2147_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
v___x_2148_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2149_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___boxed), 4, 0);
v___x_2150_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2146_, v___x_2147_, v___x_2148_, v___x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___boxed(lean_object* v_a_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3(){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2179_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
v___x_2180_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6));
v___x_2181_ = l_Lean_addBuiltinDeclarationRanges(v___x_2179_, v___x_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___boxed(lean_object* v_a_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(size_t v_sz_2184_, size_t v_i_2185_, lean_object* v_bs_2186_){
_start:
{
uint8_t v___x_2187_; 
v___x_2187_ = lean_usize_dec_lt(v_i_2185_, v_sz_2184_);
if (v___x_2187_ == 0)
{
return v_bs_2186_;
}
else
{
lean_object* v_v_2188_; lean_object* v___x_2189_; lean_object* v_bs_x27_2190_; size_t v___x_2191_; size_t v___x_2192_; lean_object* v___x_2193_; 
v_v_2188_ = lean_array_uget(v_bs_2186_, v_i_2185_);
v___x_2189_ = lean_unsigned_to_nat(0u);
v_bs_x27_2190_ = lean_array_uset(v_bs_2186_, v_i_2185_, v___x_2189_);
v___x_2191_ = ((size_t)1ULL);
v___x_2192_ = lean_usize_add(v_i_2185_, v___x_2191_);
v___x_2193_ = lean_array_uset(v_bs_x27_2190_, v_i_2185_, v_v_2188_);
v_i_2185_ = v___x_2192_;
v_bs_2186_ = v___x_2193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2___boxed(lean_object* v_sz_2195_, lean_object* v_i_2196_, lean_object* v_bs_2197_){
_start:
{
size_t v_sz_boxed_2198_; size_t v_i_boxed_2199_; lean_object* v_res_2200_; 
v_sz_boxed_2198_ = lean_unbox_usize(v_sz_2195_);
lean_dec(v_sz_2195_);
v_i_boxed_2199_ = lean_unbox_usize(v_i_2196_);
lean_dec(v_i_2196_);
v_res_2200_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_boxed_2198_, v_i_boxed_2199_, v_bs_2197_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(size_t v_sz_2201_, size_t v_i_2202_, lean_object* v_bs_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
uint8_t v___x_2207_; 
v___x_2207_ = lean_usize_dec_lt(v_i_2202_, v_sz_2201_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; 
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v_bs_2203_);
return v___x_2208_;
}
else
{
lean_object* v_v_2209_; lean_object* v___x_2210_; 
v_v_2209_ = lean_array_uget_borrowed(v_bs_2203_, v_i_2202_);
lean_inc(v_v_2209_);
v___x_2210_ = l_Lean_Elab_Command_expandMacroArg(v_v_2209_, v___y_2204_, v___y_2205_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2212_; lean_object* v_bs_x27_2213_; size_t v___x_2214_; size_t v___x_2215_; lean_object* v___x_2216_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2211_);
lean_dec_ref_known(v___x_2210_, 1);
v___x_2212_ = lean_unsigned_to_nat(0u);
v_bs_x27_2213_ = lean_array_uset(v_bs_2203_, v_i_2202_, v___x_2212_);
v___x_2214_ = ((size_t)1ULL);
v___x_2215_ = lean_usize_add(v_i_2202_, v___x_2214_);
v___x_2216_ = lean_array_uset(v_bs_x27_2213_, v_i_2202_, v_a_2211_);
v_i_2202_ = v___x_2215_;
v_bs_2203_ = v___x_2216_;
goto _start;
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v_bs_2203_);
v_a_2218_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2210_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2210_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1___boxed(lean_object* v_sz_2226_, lean_object* v_i_2227_, lean_object* v_bs_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
size_t v_sz_boxed_2232_; size_t v_i_boxed_2233_; lean_object* v_res_2234_; 
v_sz_boxed_2232_ = lean_unbox_usize(v_sz_2226_);
lean_dec(v_sz_2226_);
v_i_boxed_2233_ = lean_unbox_usize(v_i_2227_);
lean_dec(v_i_2227_);
v_res_2234_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_boxed_2232_, v_i_boxed_2233_, v_bs_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
return v_res_2234_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(lean_object* v_keys_2235_, lean_object* v_i_2236_, lean_object* v_k_2237_){
_start:
{
lean_object* v___x_2238_; uint8_t v___x_2239_; 
v___x_2238_ = lean_array_get_size(v_keys_2235_);
v___x_2239_ = lean_nat_dec_lt(v_i_2236_, v___x_2238_);
if (v___x_2239_ == 0)
{
lean_dec(v_i_2236_);
return v___x_2239_;
}
else
{
lean_object* v_k_x27_2240_; uint8_t v___x_2241_; 
v_k_x27_2240_ = lean_array_fget_borrowed(v_keys_2235_, v_i_2236_);
v___x_2241_ = l_Lean_instBEqExtraModUse_beq(v_k_2237_, v_k_x27_2240_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = lean_unsigned_to_nat(1u);
v___x_2243_ = lean_nat_add(v_i_2236_, v___x_2242_);
lean_dec(v_i_2236_);
v_i_2236_ = v___x_2243_;
goto _start;
}
else
{
lean_dec(v_i_2236_);
return v___x_2241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg___boxed(lean_object* v_keys_2245_, lean_object* v_i_2246_, lean_object* v_k_2247_){
_start:
{
uint8_t v_res_2248_; lean_object* v_r_2249_; 
v_res_2248_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_2245_, v_i_2246_, v_k_2247_);
lean_dec_ref(v_k_2247_);
lean_dec_ref(v_keys_2245_);
v_r_2249_ = lean_box(v_res_2248_);
return v_r_2249_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(lean_object* v_x_2250_, size_t v_x_2251_, lean_object* v_x_2252_){
_start:
{
if (lean_obj_tag(v_x_2250_) == 0)
{
lean_object* v_es_2253_; lean_object* v___x_2254_; size_t v___x_2255_; size_t v___x_2256_; lean_object* v_j_2257_; lean_object* v___x_2258_; 
v_es_2253_ = lean_ctor_get(v_x_2250_, 0);
v___x_2254_ = lean_box(2);
v___x_2255_ = ((size_t)31ULL);
v___x_2256_ = lean_usize_land(v_x_2251_, v___x_2255_);
v_j_2257_ = lean_usize_to_nat(v___x_2256_);
v___x_2258_ = lean_array_get_borrowed(v___x_2254_, v_es_2253_, v_j_2257_);
lean_dec(v_j_2257_);
switch(lean_obj_tag(v___x_2258_))
{
case 0:
{
lean_object* v_key_2259_; uint8_t v___x_2260_; 
v_key_2259_ = lean_ctor_get(v___x_2258_, 0);
v___x_2260_ = l_Lean_instBEqExtraModUse_beq(v_x_2252_, v_key_2259_);
return v___x_2260_;
}
case 1:
{
lean_object* v_node_2261_; size_t v___x_2262_; size_t v___x_2263_; 
v_node_2261_ = lean_ctor_get(v___x_2258_, 0);
v___x_2262_ = ((size_t)5ULL);
v___x_2263_ = lean_usize_shift_right(v_x_2251_, v___x_2262_);
v_x_2250_ = v_node_2261_;
v_x_2251_ = v___x_2263_;
goto _start;
}
default: 
{
uint8_t v___x_2265_; 
v___x_2265_ = 0;
return v___x_2265_;
}
}
}
else
{
lean_object* v_ks_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; 
v_ks_2266_ = lean_ctor_get(v_x_2250_, 0);
v___x_2267_ = lean_unsigned_to_nat(0u);
v___x_2268_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_ks_2266_, v___x_2267_, v_x_2252_);
return v___x_2268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_x_2269_, lean_object* v_x_2270_, lean_object* v_x_2271_){
_start:
{
size_t v_x_19435__boxed_2272_; uint8_t v_res_2273_; lean_object* v_r_2274_; 
v_x_19435__boxed_2272_ = lean_unbox_usize(v_x_2270_);
lean_dec(v_x_2270_);
v_res_2273_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2269_, v_x_19435__boxed_2272_, v_x_2271_);
lean_dec_ref(v_x_2271_);
lean_dec_ref(v_x_2269_);
v_r_2274_ = lean_box(v_res_2273_);
return v_r_2274_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(lean_object* v_x_2275_, lean_object* v_x_2276_){
_start:
{
uint64_t v___x_2277_; size_t v___x_2278_; uint8_t v___x_2279_; 
v___x_2277_ = l_Lean_instHashableExtraModUse_hash(v_x_2276_);
v___x_2278_ = lean_uint64_to_usize(v___x_2277_);
v___x_2279_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_2275_, v___x_2278_, v_x_2276_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_x_2280_, lean_object* v_x_2281_){
_start:
{
uint8_t v_res_2282_; lean_object* v_r_2283_; 
v_res_2282_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_2280_, v_x_2281_);
lean_dec_ref(v_x_2281_);
lean_dec_ref(v_x_2280_);
v_r_2283_ = lean_box(v_res_2282_);
return v_r_2283_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2284_; double v___x_2285_; 
v___x_2284_ = lean_unsigned_to_nat(0u);
v___x_2285_ = lean_float_of_nat(v___x_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(lean_object* v_cls_2289_, lean_object* v_msg_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_Elab_Command_getRef___redArg(v___y_2291_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2296_; lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2343_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msg_2290_, v___y_2292_);
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2299_ = v___x_2296_;
v_isShared_2300_ = v_isSharedCheck_2343_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2296_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2343_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2301_; lean_object* v_traceState_2302_; lean_object* v_env_2303_; lean_object* v_messages_2304_; lean_object* v_scopes_2305_; lean_object* v_usedQuotCtxts_2306_; lean_object* v_nextMacroScope_2307_; lean_object* v_maxRecDepth_2308_; lean_object* v_ngen_2309_; lean_object* v_auxDeclNGen_2310_; lean_object* v_infoState_2311_; lean_object* v_snapshotTasks_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2342_; 
v___x_2301_ = lean_st_ref_take(v___y_2292_);
v_traceState_2302_ = lean_ctor_get(v___x_2301_, 9);
v_env_2303_ = lean_ctor_get(v___x_2301_, 0);
v_messages_2304_ = lean_ctor_get(v___x_2301_, 1);
v_scopes_2305_ = lean_ctor_get(v___x_2301_, 2);
v_usedQuotCtxts_2306_ = lean_ctor_get(v___x_2301_, 3);
v_nextMacroScope_2307_ = lean_ctor_get(v___x_2301_, 4);
v_maxRecDepth_2308_ = lean_ctor_get(v___x_2301_, 5);
v_ngen_2309_ = lean_ctor_get(v___x_2301_, 6);
v_auxDeclNGen_2310_ = lean_ctor_get(v___x_2301_, 7);
v_infoState_2311_ = lean_ctor_get(v___x_2301_, 8);
v_snapshotTasks_2312_ = lean_ctor_get(v___x_2301_, 10);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2314_ = v___x_2301_;
v_isShared_2315_ = v_isSharedCheck_2342_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_snapshotTasks_2312_);
lean_inc(v_traceState_2302_);
lean_inc(v_infoState_2311_);
lean_inc(v_auxDeclNGen_2310_);
lean_inc(v_ngen_2309_);
lean_inc(v_maxRecDepth_2308_);
lean_inc(v_nextMacroScope_2307_);
lean_inc(v_usedQuotCtxts_2306_);
lean_inc(v_scopes_2305_);
lean_inc(v_messages_2304_);
lean_inc(v_env_2303_);
lean_dec(v___x_2301_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2342_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
uint64_t v_tid_2316_; lean_object* v_traces_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2341_; 
v_tid_2316_ = lean_ctor_get_uint64(v_traceState_2302_, sizeof(void*)*1);
v_traces_2317_ = lean_ctor_get(v_traceState_2302_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_traceState_2302_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2319_ = v_traceState_2302_;
v_isShared_2320_ = v_isSharedCheck_2341_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_traces_2317_);
lean_dec(v_traceState_2302_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2341_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2321_; double v___x_2322_; uint8_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2321_ = lean_box(0);
v___x_2322_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0);
v___x_2323_ = 0;
v___x_2324_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1));
v___x_2325_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2325_, 0, v_cls_2289_);
lean_ctor_set(v___x_2325_, 1, v___x_2321_);
lean_ctor_set(v___x_2325_, 2, v___x_2324_);
lean_ctor_set_float(v___x_2325_, sizeof(void*)*3, v___x_2322_);
lean_ctor_set_float(v___x_2325_, sizeof(void*)*3 + 8, v___x_2322_);
lean_ctor_set_uint8(v___x_2325_, sizeof(void*)*3 + 16, v___x_2323_);
v___x_2326_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2));
v___x_2327_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2325_);
lean_ctor_set(v___x_2327_, 1, v_a_2297_);
lean_ctor_set(v___x_2327_, 2, v___x_2326_);
v___x_2328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2328_, 0, v_a_2295_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
v___x_2329_ = l_Lean_PersistentArray_push___redArg(v_traces_2317_, v___x_2328_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v___x_2329_);
v___x_2331_ = v___x_2319_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2329_);
lean_ctor_set_uint64(v_reuseFailAlloc_2340_, sizeof(void*)*1, v_tid_2316_);
v___x_2331_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2333_; 
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 9, v___x_2331_);
v___x_2333_ = v___x_2314_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_env_2303_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_messages_2304_);
lean_ctor_set(v_reuseFailAlloc_2339_, 2, v_scopes_2305_);
lean_ctor_set(v_reuseFailAlloc_2339_, 3, v_usedQuotCtxts_2306_);
lean_ctor_set(v_reuseFailAlloc_2339_, 4, v_nextMacroScope_2307_);
lean_ctor_set(v_reuseFailAlloc_2339_, 5, v_maxRecDepth_2308_);
lean_ctor_set(v_reuseFailAlloc_2339_, 6, v_ngen_2309_);
lean_ctor_set(v_reuseFailAlloc_2339_, 7, v_auxDeclNGen_2310_);
lean_ctor_set(v_reuseFailAlloc_2339_, 8, v_infoState_2311_);
lean_ctor_set(v_reuseFailAlloc_2339_, 9, v___x_2331_);
lean_ctor_set(v_reuseFailAlloc_2339_, 10, v_snapshotTasks_2312_);
v___x_2333_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2334_ = lean_st_ref_set(v___y_2292_, v___x_2333_);
v___x_2335_ = lean_box(0);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v___x_2335_);
v___x_2337_ = v___x_2299_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec_ref(v_msg_2290_);
lean_dec(v_cls_2289_);
v_a_2344_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2294_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2294_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___boxed(lean_object* v_cls_2352_, lean_object* v_msg_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_2352_, v_msg_2353_, v___y_2354_, v___y_2355_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
return v_res_2357_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2360_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1));
v___x_2361_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0));
v___x_2362_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2361_, v___x_2360_);
return v___x_2362_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5));
v___x_2368_ = l_Lean_stringToMessageData(v___x_2367_);
return v___x_2368_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8(void){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7));
v___x_2371_ = l_Lean_stringToMessageData(v___x_2370_);
return v___x_2371_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9(void){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1));
v___x_2373_ = l_Lean_stringToMessageData(v___x_2372_);
return v___x_2373_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v_cls_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v_cls_2377_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4));
v___x_2378_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11));
v___x_2379_ = l_Lean_Name_append(v___x_2378_, v_cls_2377_);
return v___x_2379_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13));
v___x_2382_ = l_Lean_stringToMessageData(v___x_2381_);
return v___x_2382_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15));
v___x_2385_ = l_Lean_stringToMessageData(v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(lean_object* v_mod_2390_, uint8_t v_isMeta_2391_, lean_object* v_hint_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; lean_object* v_env_2397_; uint8_t v_isExporting_2398_; lean_object* v___x_2399_; lean_object* v_env_2400_; lean_object* v___x_2401_; lean_object* v_entry_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___y_2407_; lean_object* v___x_2433_; uint8_t v___x_2434_; uint8_t v___x_2435_; 
v___x_2396_ = lean_st_ref_get(v___y_2394_);
v_env_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc_ref(v_env_2397_);
lean_dec(v___x_2396_);
v_isExporting_2398_ = lean_ctor_get_uint8(v_env_2397_, sizeof(void*)*8);
lean_dec_ref(v_env_2397_);
v___x_2399_ = lean_st_ref_get(v___y_2394_);
v_env_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc_ref(v_env_2400_);
lean_dec(v___x_2399_);
v___x_2401_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2);
lean_inc(v_mod_2390_);
v_entry_2402_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2402_, 0, v_mod_2390_);
lean_ctor_set_uint8(v_entry_2402_, sizeof(void*)*1, v_isExporting_2398_);
lean_ctor_set_uint8(v_entry_2402_, sizeof(void*)*1 + 1, v_isMeta_2391_);
v___x_2403_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2404_ = lean_box(1);
v___x_2405_ = lean_box(0);
v___x_2433_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2401_, v___x_2403_, v_env_2400_, v___x_2404_, v___x_2405_);
v___x_2434_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v___x_2433_, v_entry_2402_);
lean_dec(v___x_2433_);
v___x_2435_ = lean_bool_not(v___x_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
lean_dec_ref_known(v_entry_2402_, 1);
lean_dec(v_hint_2392_);
lean_dec(v_mod_2390_);
v___x_2436_ = lean_box(0);
v___x_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
return v___x_2437_;
}
else
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v_scopes_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v_opts_2444_; uint8_t v_hasTrace_2445_; 
v___x_2438_ = l_Lean_inheritedTraceOptions;
v___x_2439_ = lean_st_ref_get(v___x_2438_);
v___x_2440_ = lean_st_ref_get(v___y_2394_);
v_scopes_2441_ = lean_ctor_get(v___x_2440_, 2);
lean_inc(v_scopes_2441_);
lean_dec(v___x_2440_);
v___x_2442_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2443_ = l_List_head_x21___redArg(v___x_2442_, v_scopes_2441_);
lean_dec(v_scopes_2441_);
v_opts_2444_ = lean_ctor_get(v___x_2443_, 1);
lean_inc_ref(v_opts_2444_);
lean_dec(v___x_2443_);
v_hasTrace_2445_ = lean_ctor_get_uint8(v_opts_2444_, sizeof(void*)*1);
if (v_hasTrace_2445_ == 0)
{
lean_dec_ref(v_opts_2444_);
lean_dec(v___x_2439_);
lean_dec(v_hint_2392_);
lean_dec(v_mod_2390_);
v___y_2407_ = v___y_2394_;
goto v___jp_2406_;
}
else
{
lean_object* v_cls_2446_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v_cls_2446_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4));
v___x_2466_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12);
v___x_2467_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2439_, v_opts_2444_, v___x_2466_);
lean_dec_ref(v_opts_2444_);
lean_dec(v___x_2439_);
if (v___x_2467_ == 0)
{
lean_dec(v_hint_2392_);
lean_dec(v_mod_2390_);
v___y_2407_ = v___y_2394_;
goto v___jp_2406_;
}
else
{
lean_object* v___x_2468_; lean_object* v___y_2470_; 
v___x_2468_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14);
if (v_isExporting_2398_ == 0)
{
lean_object* v___x_2477_; 
v___x_2477_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__19));
v___y_2470_ = v___x_2477_;
goto v___jp_2469_;
}
else
{
lean_object* v___x_2478_; 
v___x_2478_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__20));
v___y_2470_ = v___x_2478_;
goto v___jp_2469_;
}
v___jp_2469_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
lean_inc_ref(v___y_2470_);
v___x_2471_ = l_Lean_stringToMessageData(v___y_2470_);
v___x_2472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2468_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16);
v___x_2474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2472_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
if (v_isMeta_2391_ == 0)
{
lean_object* v___x_2475_; 
v___x_2475_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17));
v___y_2453_ = v___x_2474_;
v___y_2454_ = v___x_2475_;
goto v___jp_2452_;
}
else
{
lean_object* v___x_2476_; 
v___x_2476_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18));
v___y_2453_ = v___x_2474_;
v___y_2454_ = v___x_2476_;
goto v___jp_2452_;
}
}
}
v___jp_2447_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___y_2448_);
lean_ctor_set(v___x_2450_, 1, v___y_2449_);
v___x_2451_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_2446_, v___x_2450_, v___y_2393_, v___y_2394_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_dec_ref_known(v___x_2451_, 1);
v___y_2407_ = v___y_2394_;
goto v___jp_2406_;
}
else
{
lean_dec_ref_known(v_entry_2402_, 1);
return v___x_2451_;
}
}
v___jp_2452_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; 
lean_inc_ref(v___y_2454_);
v___x_2455_ = l_Lean_stringToMessageData(v___y_2454_);
v___x_2456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___y_2453_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6);
v___x_2458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2456_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
v___x_2459_ = l_Lean_MessageData_ofName(v_mod_2390_);
v___x_2460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2458_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = l_Lean_Name_isAnonymous(v_hint_2392_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2462_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8);
v___x_2463_ = l_Lean_MessageData_ofName(v_hint_2392_);
v___x_2464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2462_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___y_2448_ = v___x_2460_;
v___y_2449_ = v___x_2464_;
goto v___jp_2447_;
}
else
{
lean_object* v___x_2465_; 
lean_dec(v_hint_2392_);
v___x_2465_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9);
v___y_2448_ = v___x_2460_;
v___y_2449_ = v___x_2465_;
goto v___jp_2447_;
}
}
}
}
v___jp_2406_:
{
lean_object* v___x_2408_; lean_object* v_toEnvExtension_2409_; lean_object* v_env_2410_; lean_object* v_messages_2411_; lean_object* v_scopes_2412_; lean_object* v_usedQuotCtxts_2413_; lean_object* v_nextMacroScope_2414_; lean_object* v_maxRecDepth_2415_; lean_object* v_ngen_2416_; lean_object* v_auxDeclNGen_2417_; lean_object* v_infoState_2418_; lean_object* v_traceState_2419_; lean_object* v_snapshotTasks_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2432_; 
v___x_2408_ = lean_st_ref_take(v___y_2407_);
v_toEnvExtension_2409_ = lean_ctor_get(v___x_2403_, 0);
v_env_2410_ = lean_ctor_get(v___x_2408_, 0);
v_messages_2411_ = lean_ctor_get(v___x_2408_, 1);
v_scopes_2412_ = lean_ctor_get(v___x_2408_, 2);
v_usedQuotCtxts_2413_ = lean_ctor_get(v___x_2408_, 3);
v_nextMacroScope_2414_ = lean_ctor_get(v___x_2408_, 4);
v_maxRecDepth_2415_ = lean_ctor_get(v___x_2408_, 5);
v_ngen_2416_ = lean_ctor_get(v___x_2408_, 6);
v_auxDeclNGen_2417_ = lean_ctor_get(v___x_2408_, 7);
v_infoState_2418_ = lean_ctor_get(v___x_2408_, 8);
v_traceState_2419_ = lean_ctor_get(v___x_2408_, 9);
v_snapshotTasks_2420_ = lean_ctor_get(v___x_2408_, 10);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2422_ = v___x_2408_;
v_isShared_2423_ = v_isSharedCheck_2432_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_snapshotTasks_2420_);
lean_inc(v_traceState_2419_);
lean_inc(v_infoState_2418_);
lean_inc(v_auxDeclNGen_2417_);
lean_inc(v_ngen_2416_);
lean_inc(v_maxRecDepth_2415_);
lean_inc(v_nextMacroScope_2414_);
lean_inc(v_usedQuotCtxts_2413_);
lean_inc(v_scopes_2412_);
lean_inc(v_messages_2411_);
lean_inc(v_env_2410_);
lean_dec(v___x_2408_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2432_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v_asyncMode_2424_; lean_object* v___x_2425_; lean_object* v___x_2427_; 
v_asyncMode_2424_ = lean_ctor_get(v_toEnvExtension_2409_, 2);
v___x_2425_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2403_, v_env_2410_, v_entry_2402_, v_asyncMode_2424_, v___x_2405_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2425_);
v___x_2427_ = v___x_2422_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2425_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v_messages_2411_);
lean_ctor_set(v_reuseFailAlloc_2431_, 2, v_scopes_2412_);
lean_ctor_set(v_reuseFailAlloc_2431_, 3, v_usedQuotCtxts_2413_);
lean_ctor_set(v_reuseFailAlloc_2431_, 4, v_nextMacroScope_2414_);
lean_ctor_set(v_reuseFailAlloc_2431_, 5, v_maxRecDepth_2415_);
lean_ctor_set(v_reuseFailAlloc_2431_, 6, v_ngen_2416_);
lean_ctor_set(v_reuseFailAlloc_2431_, 7, v_auxDeclNGen_2417_);
lean_ctor_set(v_reuseFailAlloc_2431_, 8, v_infoState_2418_);
lean_ctor_set(v_reuseFailAlloc_2431_, 9, v_traceState_2419_);
lean_ctor_set(v_reuseFailAlloc_2431_, 10, v_snapshotTasks_2420_);
v___x_2427_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2428_ = lean_st_ref_set(v___y_2407_, v___x_2427_);
v___x_2429_ = lean_box(0);
v___x_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
return v___x_2430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___boxed(lean_object* v_mod_2479_, lean_object* v_isMeta_2480_, lean_object* v_hint_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
uint8_t v_isMeta_boxed_2485_; lean_object* v_res_2486_; 
v_isMeta_boxed_2485_ = lean_unbox(v_isMeta_2480_);
v_res_2486_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_mod_2479_, v_isMeta_boxed_2485_, v_hint_2481_, v___y_2482_, v___y_2483_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(lean_object* v___x_2487_, lean_object* v_declName_2488_, lean_object* v_as_2489_, size_t v_sz_2490_, size_t v_i_2491_, lean_object* v_b_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
uint8_t v___x_2496_; 
v___x_2496_ = lean_usize_dec_lt(v_i_2491_, v_sz_2490_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; 
lean_dec(v_declName_2488_);
v___x_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2497_, 0, v_b_2492_);
return v___x_2497_;
}
else
{
lean_object* v___x_2498_; lean_object* v_modules_2499_; lean_object* v___x_2500_; lean_object* v_a_2501_; lean_object* v___x_2502_; lean_object* v_toImport_2503_; lean_object* v_module_2504_; uint8_t v___x_2505_; lean_object* v___x_2506_; 
v___x_2498_ = l_Lean_Environment_header(v___x_2487_);
v_modules_2499_ = lean_ctor_get(v___x_2498_, 3);
lean_inc_ref(v_modules_2499_);
lean_dec_ref(v___x_2498_);
v___x_2500_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2501_ = lean_array_uget_borrowed(v_as_2489_, v_i_2491_);
v___x_2502_ = lean_array_get(v___x_2500_, v_modules_2499_, v_a_2501_);
lean_dec_ref(v_modules_2499_);
v_toImport_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc_ref(v_toImport_2503_);
lean_dec(v___x_2502_);
v_module_2504_ = lean_ctor_get(v_toImport_2503_, 0);
lean_inc(v_module_2504_);
lean_dec_ref(v_toImport_2503_);
v___x_2505_ = 0;
lean_inc(v_declName_2488_);
v___x_2506_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_2504_, v___x_2505_, v_declName_2488_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v___x_2507_; size_t v___x_2508_; size_t v___x_2509_; 
lean_dec_ref_known(v___x_2506_, 1);
v___x_2507_ = lean_box(0);
v___x_2508_ = ((size_t)1ULL);
v___x_2509_ = lean_usize_add(v_i_2491_, v___x_2508_);
v_i_2491_ = v___x_2509_;
v_b_2492_ = v___x_2507_;
goto _start;
}
else
{
lean_dec(v_declName_2488_);
return v___x_2506_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4___boxed(lean_object* v___x_2511_, lean_object* v_declName_2512_, lean_object* v_as_2513_, lean_object* v_sz_2514_, lean_object* v_i_2515_, lean_object* v_b_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
size_t v_sz_boxed_2520_; size_t v_i_boxed_2521_; lean_object* v_res_2522_; 
v_sz_boxed_2520_ = lean_unbox_usize(v_sz_2514_);
lean_dec(v_sz_2514_);
v_i_boxed_2521_ = lean_unbox_usize(v_i_2515_);
lean_dec(v_i_2515_);
v_res_2522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v___x_2511_, v_declName_2512_, v_as_2513_, v_sz_boxed_2520_, v_i_boxed_2521_, v_b_2516_, v___y_2517_, v___y_2518_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec_ref(v_as_2513_);
lean_dec_ref(v___x_2511_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(lean_object* v_a_2523_, lean_object* v_x_2524_){
_start:
{
if (lean_obj_tag(v_x_2524_) == 0)
{
lean_object* v___x_2525_; 
v___x_2525_ = lean_box(0);
return v___x_2525_;
}
else
{
lean_object* v_key_2526_; lean_object* v_value_2527_; lean_object* v_tail_2528_; uint8_t v___x_2529_; 
v_key_2526_ = lean_ctor_get(v_x_2524_, 0);
v_value_2527_ = lean_ctor_get(v_x_2524_, 1);
v_tail_2528_ = lean_ctor_get(v_x_2524_, 2);
v___x_2529_ = lean_name_eq(v_key_2526_, v_a_2523_);
if (v___x_2529_ == 0)
{
v_x_2524_ = v_tail_2528_;
goto _start;
}
else
{
lean_object* v___x_2531_; 
lean_inc(v_value_2527_);
v___x_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2531_, 0, v_value_2527_);
return v___x_2531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v_a_2532_, lean_object* v_x_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_2532_, v_x_2533_);
lean_dec(v_x_2533_);
lean_dec(v_a_2532_);
return v_res_2534_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2535_; uint64_t v___x_2536_; 
v___x_2535_ = lean_unsigned_to_nat(1723u);
v___x_2536_ = lean_uint64_of_nat(v___x_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(lean_object* v_m_2537_, lean_object* v_a_2538_){
_start:
{
lean_object* v_buckets_2539_; lean_object* v___x_2540_; uint64_t v___y_2542_; 
v_buckets_2539_ = lean_ctor_get(v_m_2537_, 1);
v___x_2540_ = lean_array_get_size(v_buckets_2539_);
if (lean_obj_tag(v_a_2538_) == 0)
{
uint64_t v___x_2556_; 
v___x_2556_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___closed__0);
v___y_2542_ = v___x_2556_;
goto v___jp_2541_;
}
else
{
uint64_t v_hash_2557_; 
v_hash_2557_ = lean_ctor_get_uint64(v_a_2538_, sizeof(void*)*2);
v___y_2542_ = v_hash_2557_;
goto v___jp_2541_;
}
v___jp_2541_:
{
uint64_t v___x_2543_; uint64_t v___x_2544_; uint64_t v_fold_2545_; uint64_t v___x_2546_; uint64_t v___x_2547_; uint64_t v___x_2548_; size_t v___x_2549_; size_t v___x_2550_; size_t v___x_2551_; size_t v___x_2552_; size_t v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2543_ = 32ULL;
v___x_2544_ = lean_uint64_shift_right(v___y_2542_, v___x_2543_);
v_fold_2545_ = lean_uint64_xor(v___y_2542_, v___x_2544_);
v___x_2546_ = 16ULL;
v___x_2547_ = lean_uint64_shift_right(v_fold_2545_, v___x_2546_);
v___x_2548_ = lean_uint64_xor(v_fold_2545_, v___x_2547_);
v___x_2549_ = lean_uint64_to_usize(v___x_2548_);
v___x_2550_ = lean_usize_of_nat(v___x_2540_);
v___x_2551_ = ((size_t)1ULL);
v___x_2552_ = lean_usize_sub(v___x_2550_, v___x_2551_);
v___x_2553_ = lean_usize_land(v___x_2549_, v___x_2552_);
v___x_2554_ = lean_array_uget_borrowed(v_buckets_2539_, v___x_2553_);
v___x_2555_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_2538_, v___x_2554_);
return v___x_2555_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_m_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_2558_, v_a_2559_);
lean_dec(v_a_2559_);
lean_dec_ref(v_m_2558_);
return v_res_2560_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1));
v___x_2564_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0));
v___x_2565_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2564_, v___x_2563_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(lean_object* v_declName_2568_, uint8_t v_isMeta_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v___x_2573_; lean_object* v_env_2577_; lean_object* v___y_2579_; lean_object* v___x_2592_; 
v___x_2573_ = lean_st_ref_get(v___y_2571_);
v_env_2577_ = lean_ctor_get(v___x_2573_, 0);
lean_inc_ref(v_env_2577_);
lean_dec(v___x_2573_);
v___x_2592_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2577_, v_declName_2568_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_dec_ref(v_env_2577_);
lean_dec(v_declName_2568_);
goto v___jp_2574_;
}
else
{
lean_object* v_val_2593_; lean_object* v___x_2594_; lean_object* v_modules_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; 
v_val_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_val_2593_);
lean_dec_ref_known(v___x_2592_, 1);
v___x_2594_ = l_Lean_Environment_header(v_env_2577_);
v_modules_2595_ = lean_ctor_get(v___x_2594_, 3);
lean_inc_ref(v_modules_2595_);
lean_dec_ref(v___x_2594_);
v___x_2596_ = lean_array_get_size(v_modules_2595_);
v___x_2597_ = lean_nat_dec_lt(v_val_2593_, v___x_2596_);
if (v___x_2597_ == 0)
{
lean_dec_ref(v_modules_2595_);
lean_dec(v_val_2593_);
lean_dec_ref(v_env_2577_);
lean_dec(v_declName_2568_);
goto v___jp_2574_;
}
else
{
lean_object* v___x_2598_; lean_object* v_env_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; uint8_t v___y_2603_; 
v___x_2598_ = lean_st_ref_get(v___y_2571_);
v_env_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc_ref(v_env_2599_);
lean_dec(v___x_2598_);
v___x_2600_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__2);
v___x_2601_ = lean_array_fget(v_modules_2595_, v_val_2593_);
lean_dec(v_val_2593_);
lean_dec_ref(v_modules_2595_);
if (v_isMeta_2569_ == 0)
{
lean_dec_ref(v_env_2599_);
v___y_2603_ = v_isMeta_2569_;
goto v___jp_2602_;
}
else
{
uint8_t v___x_2614_; uint8_t v___x_2615_; 
lean_inc(v_declName_2568_);
v___x_2614_ = l_Lean_isMarkedMeta(v_env_2599_, v_declName_2568_);
v___x_2615_ = lean_bool_not(v___x_2614_);
v___y_2603_ = v___x_2615_;
goto v___jp_2602_;
}
v___jp_2602_:
{
lean_object* v_toImport_2604_; lean_object* v_module_2605_; lean_object* v___x_2606_; 
v_toImport_2604_ = lean_ctor_get(v___x_2601_, 0);
lean_inc_ref(v_toImport_2604_);
lean_dec(v___x_2601_);
v_module_2605_ = lean_ctor_get(v_toImport_2604_, 0);
lean_inc(v_module_2605_);
lean_dec_ref(v_toImport_2604_);
lean_inc(v_declName_2568_);
v___x_2606_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_2605_, v___y_2603_, v_declName_2568_, v___y_2570_, v___y_2571_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
lean_dec_ref_known(v___x_2606_, 1);
v___x_2607_ = l_Lean_indirectModUseExt;
v___x_2608_ = lean_box(1);
v___x_2609_ = lean_box(0);
lean_inc_ref(v_env_2577_);
v___x_2610_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2600_, v___x_2607_, v_env_2577_, v___x_2608_, v___x_2609_);
v___x_2611_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v___x_2610_, v_declName_2568_);
lean_dec(v___x_2610_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v___x_2612_; 
v___x_2612_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__3));
v___y_2579_ = v___x_2612_;
goto v___jp_2578_;
}
else
{
lean_object* v_val_2613_; 
v_val_2613_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_val_2613_);
lean_dec_ref_known(v___x_2611_, 1);
v___y_2579_ = v_val_2613_;
goto v___jp_2578_;
}
}
else
{
lean_dec_ref(v_env_2577_);
lean_dec(v_declName_2568_);
return v___x_2606_;
}
}
}
}
v___jp_2574_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2575_ = lean_box(0);
v___x_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
return v___x_2576_;
}
v___jp_2578_:
{
lean_object* v___x_2580_; size_t v_sz_2581_; size_t v___x_2582_; lean_object* v___x_2583_; 
v___x_2580_ = lean_box(0);
v_sz_2581_ = lean_array_size(v___y_2579_);
v___x_2582_ = ((size_t)0ULL);
v___x_2583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v_env_2577_, v_declName_2568_, v___y_2579_, v_sz_2581_, v___x_2582_, v___x_2580_, v___y_2570_, v___y_2571_);
lean_dec_ref(v___y_2579_);
lean_dec_ref(v_env_2577_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2590_ == 0)
{
lean_object* v_unused_2591_; 
v_unused_2591_ = lean_ctor_get(v___x_2583_, 0);
lean_dec(v_unused_2591_);
v___x_2585_ = v___x_2583_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_dec(v___x_2583_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2580_);
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2580_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
else
{
return v___x_2583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___boxed(lean_object* v_declName_2616_, lean_object* v_isMeta_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
uint8_t v_isMeta_boxed_2621_; lean_object* v_res_2622_; 
v_isMeta_boxed_2621_ = lean_unbox(v_isMeta_2617_);
v_res_2622_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_declName_2616_, v_isMeta_boxed_2621_, v___y_2618_, v___y_2619_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(lean_object* v_as_x27_2623_, lean_object* v_b_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
if (lean_obj_tag(v_as_x27_2623_) == 0)
{
lean_object* v___x_2628_; 
v___x_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2628_, 0, v_b_2624_);
return v___x_2628_;
}
else
{
lean_object* v_head_2629_; lean_object* v_tail_2630_; uint8_t v___x_2631_; lean_object* v___x_2632_; 
v_head_2629_ = lean_ctor_get(v_as_x27_2623_, 0);
v_tail_2630_ = lean_ctor_get(v_as_x27_2623_, 1);
v___x_2631_ = 1;
lean_inc(v_head_2629_);
v___x_2632_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_head_2629_, v___x_2631_, v___y_2625_, v___y_2626_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v___x_2633_; 
lean_dec_ref_known(v___x_2632_, 1);
v___x_2633_ = lean_box(0);
v_as_x27_2623_ = v_tail_2630_;
v_b_2624_ = v___x_2633_;
goto _start;
}
else
{
return v___x_2632_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_2635_, lean_object* v_b_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_2635_, v_b_2636_, v___y_2637_, v___y_2638_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v_as_x27_2635_);
return v_res_2640_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = l_Lean_maxRecDepthErrorMessage;
v___x_2647_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
return v___x_2647_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3);
v___x_2649_ = l_Lean_MessageData_ofFormat(v___x_2648_);
return v___x_2649_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2650_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4);
v___x_2651_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2));
v___x_2652_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
lean_ctor_set(v___x_2652_, 1, v___x_2650_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(lean_object* v_ref_2653_){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2655_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5);
v___x_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2656_, 0, v_ref_2653_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___boxed(lean_object* v_ref_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_2658_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(lean_object* v_currNamespace_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2664_, 0, v_currNamespace_2661_);
lean_ctor_set(v___x_2664_, 1, v___y_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(v_currNamespace_2665_, v___y_2666_, v___y_2667_);
lean_dec_ref(v___y_2666_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(lean_object* v_env_2669_, lean_object* v_declName_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
uint8_t v___x_2673_; lean_object* v_env_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; uint8_t v___x_2677_; 
v___x_2673_ = 0;
v_env_2674_ = l_Lean_Environment_setExporting(v_env_2669_, v___x_2673_);
lean_inc(v_declName_2670_);
v___x_2675_ = l_Lean_mkPrivateName(v_env_2674_, v_declName_2670_);
v___x_2676_ = 1;
lean_inc_ref(v_env_2674_);
v___x_2677_ = l_Lean_Environment_contains(v_env_2674_, v___x_2675_, v___x_2676_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; uint8_t v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2678_ = l_Lean_privateToUserName(v_declName_2670_);
v___x_2679_ = l_Lean_Environment_contains(v_env_2674_, v___x_2678_, v___x_2676_);
v___x_2680_ = lean_box(v___x_2679_);
v___x_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
lean_ctor_set(v___x_2681_, 1, v___y_2672_);
return v___x_2681_;
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
lean_dec_ref(v_env_2674_);
lean_dec(v_declName_2670_);
v___x_2682_ = lean_box(v___x_2677_);
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
lean_ctor_set(v___x_2683_, 1, v___y_2672_);
return v___x_2683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed(lean_object* v_env_2684_, lean_object* v_declName_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(v_env_2684_, v_declName_2685_, v___y_2686_, v___y_2687_);
lean_dec_ref(v___y_2686_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(lean_object* v_x_2689_, lean_object* v___y_2690_){
_start:
{
if (lean_obj_tag(v_x_2689_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2692_; 
v_a_2691_ = lean_ctor_get(v_x_2689_, 0);
lean_inc(v_a_2691_);
v___x_2692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2692_, 0, v_a_2691_);
lean_ctor_set(v___x_2692_, 1, v___y_2690_);
return v___x_2692_;
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2694_; 
v_a_2693_ = lean_ctor_get(v_x_2689_, 0);
lean_inc(v_a_2693_);
v___x_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2694_, 0, v_a_2693_);
lean_ctor_set(v___x_2694_, 1, v___y_2690_);
return v___x_2694_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg___boxed(lean_object* v_x_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_2695_, v___y_2696_);
lean_dec_ref(v_x_2695_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(lean_object* v_env_2698_, lean_object* v_stx_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2698_, v_stx_2699_, v___y_2700_, v___y_2701_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
if (lean_obj_tag(v_a_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2712_; 
v_a_2704_ = lean_ctor_get(v___x_2702_, 1);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2712_ == 0)
{
lean_object* v_unused_2713_; 
v_unused_2713_ = lean_ctor_get(v___x_2702_, 0);
lean_dec(v_unused_2713_);
v___x_2706_ = v___x_2702_;
v_isShared_2707_ = v_isSharedCheck_2712_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2702_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2712_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2708_; lean_object* v___x_2710_; 
v___x_2708_ = lean_box(0);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v___x_2708_);
v___x_2710_ = v___x_2706_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2708_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v_a_2704_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
else
{
lean_object* v_val_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2742_; 
v_val_2714_ = lean_ctor_get(v_a_2703_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_a_2703_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2716_ = v_a_2703_;
v_isShared_2717_ = v_isSharedCheck_2742_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_val_2714_);
lean_dec(v_a_2703_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2742_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v_snd_2718_; 
v_snd_2718_ = lean_ctor_get(v_val_2714_, 1);
lean_inc(v_snd_2718_);
lean_dec(v_val_2714_);
if (lean_obj_tag(v_snd_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2728_; 
lean_del_object(v___x_2716_);
v_a_2719_ = lean_ctor_get(v___x_2702_, 1);
lean_inc(v_a_2719_);
lean_dec_ref_known(v___x_2702_, 2);
v_a_2720_ = lean_ctor_get(v_snd_2718_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_snd_2718_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2722_ = v_snd_2718_;
v_isShared_2723_ = v_isSharedCheck_2728_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v_snd_2718_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2728_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_2725_, v_a_2719_);
lean_dec_ref(v___x_2725_);
return v___x_2726_;
}
}
}
else
{
lean_object* v_a_2729_; lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2741_; 
v_a_2729_ = lean_ctor_get(v___x_2702_, 1);
lean_inc(v_a_2729_);
lean_dec_ref_known(v___x_2702_, 2);
v_a_2730_ = lean_ctor_get(v_snd_2718_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_snd_2718_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2732_ = v_snd_2718_;
v_isShared_2733_ = v_isSharedCheck_2741_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v_snd_2718_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2741_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 0, v_a_2730_);
v___x_2735_ = v___x_2716_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2737_; 
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v___x_2735_);
v___x_2737_ = v___x_2732_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2738_; 
v___x_2738_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_2737_, v_a_2729_);
lean_dec_ref(v___x_2737_);
return v___x_2738_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
v_a_2743_ = lean_ctor_get(v___x_2702_, 0);
v_a_2744_ = lean_ctor_get(v___x_2702_, 1);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2702_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_inc(v_a_2743_);
lean_dec(v___x_2702_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2743_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed(lean_object* v_env_2752_, lean_object* v_stx_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(v_env_2752_, v_stx_2753_, v___y_2754_, v___y_2755_);
lean_dec_ref(v___y_2754_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(lean_object* v_env_2757_, lean_object* v_currNamespace_2758_, lean_object* v_openDecls_2759_, lean_object* v_n_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = l_Lean_ResolveName_resolveNamespace(v_env_2757_, v_currNamespace_2758_, v_openDecls_2759_, v_n_2760_);
v___x_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2763_);
lean_ctor_set(v___x_2764_, 1, v___y_2762_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed(lean_object* v_env_2765_, lean_object* v_currNamespace_2766_, lean_object* v_openDecls_2767_, lean_object* v_n_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(v_env_2765_, v_currNamespace_2766_, v_openDecls_2767_, v_n_2768_, v___y_2769_, v___y_2770_);
lean_dec_ref(v___y_2769_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(lean_object* v_as_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
if (lean_obj_tag(v_as_2772_) == 0)
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = lean_box(0);
v___x_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
return v___x_2777_;
}
else
{
lean_object* v_head_2778_; lean_object* v_tail_2779_; lean_object* v_fst_2780_; lean_object* v_snd_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v_scopes_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v_opts_2788_; uint8_t v_hasTrace_2789_; 
v_head_2778_ = lean_ctor_get(v_as_2772_, 0);
lean_inc(v_head_2778_);
v_tail_2779_ = lean_ctor_get(v_as_2772_, 1);
lean_inc(v_tail_2779_);
lean_dec_ref_known(v_as_2772_, 2);
v_fst_2780_ = lean_ctor_get(v_head_2778_, 0);
lean_inc(v_fst_2780_);
v_snd_2781_ = lean_ctor_get(v_head_2778_, 1);
lean_inc(v_snd_2781_);
lean_dec(v_head_2778_);
v___x_2782_ = l_Lean_inheritedTraceOptions;
v___x_2783_ = lean_st_ref_get(v___x_2782_);
v___x_2784_ = lean_st_ref_get(v___y_2774_);
v_scopes_2785_ = lean_ctor_get(v___x_2784_, 2);
lean_inc(v_scopes_2785_);
lean_dec(v___x_2784_);
v___x_2786_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2787_ = l_List_head_x21___redArg(v___x_2786_, v_scopes_2785_);
lean_dec(v_scopes_2785_);
v_opts_2788_ = lean_ctor_get(v___x_2787_, 1);
lean_inc_ref(v_opts_2788_);
lean_dec(v___x_2787_);
v_hasTrace_2789_ = lean_ctor_get_uint8(v_opts_2788_, sizeof(void*)*1);
if (v_hasTrace_2789_ == 0)
{
lean_dec_ref(v_opts_2788_);
lean_dec(v___x_2783_);
lean_dec(v_snd_2781_);
lean_dec(v_fst_2780_);
v_as_2772_ = v_tail_2779_;
goto _start;
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; 
v___x_2791_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11));
lean_inc(v_fst_2780_);
v___x_2792_ = l_Lean_Name_append(v___x_2791_, v_fst_2780_);
v___x_2793_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2783_, v_opts_2788_, v___x_2792_);
lean_dec(v___x_2792_);
lean_dec_ref(v_opts_2788_);
lean_dec(v___x_2783_);
if (v___x_2793_ == 0)
{
lean_dec(v_snd_2781_);
lean_dec(v_fst_2780_);
v_as_2772_ = v_tail_2779_;
goto _start;
}
else
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2795_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2795_, 0, v_snd_2781_);
v___x_2796_ = l_Lean_MessageData_ofFormat(v___x_2795_);
v___x_2797_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_fst_2780_, v___x_2796_, v___y_2773_, v___y_2774_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_dec_ref_known(v___x_2797_, 1);
v_as_2772_ = v_tail_2779_;
goto _start;
}
else
{
lean_dec(v_tail_2779_);
return v___x_2797_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___boxed(lean_object* v_as_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v_as_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(lean_object* v_env_2804_, lean_object* v_opts_2805_, lean_object* v_currNamespace_2806_, lean_object* v_openDecls_2807_, lean_object* v_n_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = l_Lean_ResolveName_resolveGlobalName(v_env_2804_, v_opts_2805_, v_currNamespace_2806_, v_openDecls_2807_, v_n_2808_);
v___x_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
lean_ctor_set(v___x_2812_, 1, v___y_2810_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed(lean_object* v_env_2813_, lean_object* v_opts_2814_, lean_object* v_currNamespace_2815_, lean_object* v_openDecls_2816_, lean_object* v_n_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(v_env_2813_, v_opts_2814_, v_currNamespace_2815_, v_openDecls_2816_, v_n_2817_, v___y_2818_, v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec_ref(v_opts_2814_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(lean_object* v_x_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v___x_2826_; lean_object* v_env_2827_; lean_object* v___x_2828_; lean_object* v_scopes_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v_opts_2832_; lean_object* v___x_2833_; 
v___x_2826_ = lean_st_ref_get(v___y_2824_);
v_env_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc_ref(v_env_2827_);
lean_dec(v___x_2826_);
v___x_2828_ = lean_st_ref_get(v___y_2824_);
v_scopes_2829_ = lean_ctor_get(v___x_2828_, 2);
lean_inc(v_scopes_2829_);
lean_dec(v___x_2828_);
v___x_2830_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2831_ = l_List_head_x21___redArg(v___x_2830_, v_scopes_2829_);
lean_dec(v_scopes_2829_);
v_opts_2832_ = lean_ctor_get(v___x_2831_, 1);
lean_inc_ref(v_opts_2832_);
lean_dec(v___x_2831_);
v___x_2833_ = l_Lean_Elab_Command_getScope___redArg(v___y_2824_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v_currNamespace_2835_; lean_object* v___x_2836_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v___x_2833_, 1);
v_currNamespace_2835_ = lean_ctor_get(v_a_2834_, 2);
lean_inc(v_currNamespace_2835_);
lean_dec(v_a_2834_);
v___x_2836_ = l_Lean_Elab_Command_getScope___redArg(v___y_2824_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v_openDecls_2838_; lean_object* v___x_2839_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec_ref_known(v___x_2836_, 1);
v_openDecls_2838_ = lean_ctor_get(v_a_2837_, 3);
lean_inc(v_openDecls_2838_);
lean_dec(v_a_2837_);
v___x_2839_ = l_Lean_Elab_Command_getRef___redArg(v___y_2823_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2841_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2839_, 1);
v___x_2841_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2823_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v_currRecDepth_2843_; lean_object* v_quotContext_x3f_2844_; lean_object* v___f_2845_; lean_object* v___f_2846_; lean_object* v___f_2847_; lean_object* v___f_2848_; lean_object* v___f_2849_; lean_object* v_methods_2850_; lean_object* v_a_2852_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref_known(v___x_2841_, 1);
v_currRecDepth_2843_ = lean_ctor_get(v___y_2823_, 2);
v_quotContext_x3f_2844_ = lean_ctor_get(v___y_2823_, 5);
lean_inc_ref_n(v_env_2827_, 3);
v___f_2845_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2845_, 0, v_env_2827_);
v___f_2846_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2846_, 0, v_env_2827_);
lean_inc_n(v_currNamespace_2835_, 2);
v___f_2847_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2847_, 0, v_currNamespace_2835_);
lean_inc(v_openDecls_2838_);
v___f_2848_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_2848_, 0, v_env_2827_);
lean_closure_set(v___f_2848_, 1, v_currNamespace_2835_);
lean_closure_set(v___f_2848_, 2, v_openDecls_2838_);
v___f_2849_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2849_, 0, v_env_2827_);
lean_closure_set(v___f_2849_, 1, v_opts_2832_);
lean_closure_set(v___f_2849_, 2, v_currNamespace_2835_);
lean_closure_set(v___f_2849_, 3, v_openDecls_2838_);
v_methods_2850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2850_, 0, v___f_2846_);
lean_ctor_set(v_methods_2850_, 1, v___f_2847_);
lean_ctor_set(v_methods_2850_, 2, v___f_2845_);
lean_ctor_set(v_methods_2850_, 3, v___f_2848_);
lean_ctor_set(v_methods_2850_, 4, v___f_2849_);
if (lean_obj_tag(v_quotContext_x3f_2844_) == 0)
{
lean_object* v___x_2924_; lean_object* v_a_2925_; 
v___x_2924_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_2824_);
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref(v___x_2924_);
v_a_2852_ = v_a_2925_;
goto v___jp_2851_;
}
else
{
lean_object* v_val_2926_; 
v_val_2926_ = lean_ctor_get(v_quotContext_x3f_2844_, 0);
lean_inc(v_val_2926_);
v_a_2852_ = v_val_2926_;
goto v___jp_2851_;
}
v___jp_2851_:
{
lean_object* v___x_2853_; lean_object* v_maxRecDepth_2854_; lean_object* v___x_2855_; lean_object* v_nextMacroScope_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2853_ = lean_st_ref_get(v___y_2824_);
v_maxRecDepth_2854_ = lean_ctor_get(v___x_2853_, 5);
lean_inc(v_maxRecDepth_2854_);
lean_dec(v___x_2853_);
v___x_2855_ = lean_st_ref_get(v___y_2824_);
v_nextMacroScope_2856_ = lean_ctor_get(v___x_2855_, 4);
lean_inc(v_nextMacroScope_2856_);
lean_dec(v___x_2855_);
lean_inc(v_currRecDepth_2843_);
v___x_2857_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2857_, 0, v_methods_2850_);
lean_ctor_set(v___x_2857_, 1, v_a_2852_);
lean_ctor_set(v___x_2857_, 2, v_a_2842_);
lean_ctor_set(v___x_2857_, 3, v_currRecDepth_2843_);
lean_ctor_set(v___x_2857_, 4, v_maxRecDepth_2854_);
lean_ctor_set(v___x_2857_, 5, v_a_2840_);
v___x_2858_ = lean_box(0);
v___x_2859_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2859_, 0, v_nextMacroScope_2856_);
lean_ctor_set(v___x_2859_, 1, v___x_2858_);
lean_ctor_set(v___x_2859_, 2, v___x_2858_);
v___x_2860_ = lean_apply_2(v_x_2822_, v___x_2857_, v___x_2859_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v_a_2862_; lean_object* v_macroScope_2863_; lean_object* v_traceMsgs_2864_; lean_object* v_expandedMacroDecls_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 1);
lean_inc(v_a_2861_);
v_a_2862_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2860_, 2);
v_macroScope_2863_ = lean_ctor_get(v_a_2861_, 0);
lean_inc(v_macroScope_2863_);
v_traceMsgs_2864_ = lean_ctor_get(v_a_2861_, 1);
lean_inc(v_traceMsgs_2864_);
v_expandedMacroDecls_2865_ = lean_ctor_get(v_a_2861_, 2);
lean_inc(v_expandedMacroDecls_2865_);
lean_dec(v_a_2861_);
v___x_2866_ = lean_box(0);
v___x_2867_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_expandedMacroDecls_2865_, v___x_2866_, v___y_2823_, v___y_2824_);
lean_dec(v_expandedMacroDecls_2865_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v___x_2868_; lean_object* v_env_2869_; lean_object* v_messages_2870_; lean_object* v_scopes_2871_; lean_object* v_usedQuotCtxts_2872_; lean_object* v_maxRecDepth_2873_; lean_object* v_ngen_2874_; lean_object* v_auxDeclNGen_2875_; lean_object* v_infoState_2876_; lean_object* v_traceState_2877_; lean_object* v_snapshotTasks_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2904_; 
lean_dec_ref_known(v___x_2867_, 1);
v___x_2868_ = lean_st_ref_take(v___y_2824_);
v_env_2869_ = lean_ctor_get(v___x_2868_, 0);
v_messages_2870_ = lean_ctor_get(v___x_2868_, 1);
v_scopes_2871_ = lean_ctor_get(v___x_2868_, 2);
v_usedQuotCtxts_2872_ = lean_ctor_get(v___x_2868_, 3);
v_maxRecDepth_2873_ = lean_ctor_get(v___x_2868_, 5);
v_ngen_2874_ = lean_ctor_get(v___x_2868_, 6);
v_auxDeclNGen_2875_ = lean_ctor_get(v___x_2868_, 7);
v_infoState_2876_ = lean_ctor_get(v___x_2868_, 8);
v_traceState_2877_ = lean_ctor_get(v___x_2868_, 9);
v_snapshotTasks_2878_ = lean_ctor_get(v___x_2868_, 10);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2904_ == 0)
{
lean_object* v_unused_2905_; 
v_unused_2905_ = lean_ctor_get(v___x_2868_, 4);
lean_dec(v_unused_2905_);
v___x_2880_ = v___x_2868_;
v_isShared_2881_ = v_isSharedCheck_2904_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_snapshotTasks_2878_);
lean_inc(v_traceState_2877_);
lean_inc(v_infoState_2876_);
lean_inc(v_auxDeclNGen_2875_);
lean_inc(v_ngen_2874_);
lean_inc(v_maxRecDepth_2873_);
lean_inc(v_usedQuotCtxts_2872_);
lean_inc(v_scopes_2871_);
lean_inc(v_messages_2870_);
lean_inc(v_env_2869_);
lean_dec(v___x_2868_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2904_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 4, v_macroScope_2863_);
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_env_2869_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_messages_2870_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_scopes_2871_);
lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_usedQuotCtxts_2872_);
lean_ctor_set(v_reuseFailAlloc_2903_, 4, v_macroScope_2863_);
lean_ctor_set(v_reuseFailAlloc_2903_, 5, v_maxRecDepth_2873_);
lean_ctor_set(v_reuseFailAlloc_2903_, 6, v_ngen_2874_);
lean_ctor_set(v_reuseFailAlloc_2903_, 7, v_auxDeclNGen_2875_);
lean_ctor_set(v_reuseFailAlloc_2903_, 8, v_infoState_2876_);
lean_ctor_set(v_reuseFailAlloc_2903_, 9, v_traceState_2877_);
lean_ctor_set(v_reuseFailAlloc_2903_, 10, v_snapshotTasks_2878_);
v___x_2883_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2884_ = lean_st_ref_set(v___y_2824_, v___x_2883_);
v___x_2885_ = l_List_reverse___redArg(v_traceMsgs_2864_);
v___x_2886_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v___x_2885_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2893_ == 0)
{
lean_object* v_unused_2894_; 
v_unused_2894_ = lean_ctor_get(v___x_2886_, 0);
lean_dec(v_unused_2894_);
v___x_2888_ = v___x_2886_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_dec(v___x_2886_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 0, v_a_2862_);
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2862_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec(v_a_2862_);
v_a_2895_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2886_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2886_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
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
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_traceMsgs_2864_);
lean_dec(v_macroScope_2863_);
lean_dec(v_a_2862_);
v_a_2906_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2867_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2867_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_object* v_a_2914_; 
v_a_2914_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2914_);
lean_dec_ref_known(v___x_2860_, 2);
if (lean_obj_tag(v_a_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v_a_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; 
v_a_2915_ = lean_ctor_get(v_a_2914_, 0);
lean_inc(v_a_2915_);
v_a_2916_ = lean_ctor_get(v_a_2914_, 1);
lean_inc_ref(v_a_2916_);
lean_dec_ref_known(v_a_2914_, 2);
v___x_2917_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0));
v___x_2918_ = lean_string_dec_eq(v_a_2916_, v___x_2917_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2919_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2919_, 0, v_a_2916_);
v___x_2920_ = l_Lean_MessageData_ofFormat(v___x_2919_);
v___x_2921_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_a_2915_, v___x_2920_, v___y_2823_, v___y_2824_);
lean_dec(v_a_2915_);
return v___x_2921_;
}
else
{
lean_object* v___x_2922_; 
lean_dec_ref(v_a_2916_);
v___x_2922_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_a_2915_);
return v___x_2922_;
}
}
else
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_2923_;
}
}
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec(v_a_2840_);
lean_dec(v_openDecls_2838_);
lean_dec(v_currNamespace_2835_);
lean_dec_ref(v_opts_2832_);
lean_dec_ref(v_env_2827_);
lean_dec_ref(v_x_2822_);
v_a_2927_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2841_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2841_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_dec(v_openDecls_2838_);
lean_dec(v_currNamespace_2835_);
lean_dec_ref(v_opts_2832_);
lean_dec_ref(v_env_2827_);
lean_dec_ref(v_x_2822_);
v_a_2935_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2839_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2839_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec(v_currNamespace_2835_);
lean_dec_ref(v_opts_2832_);
lean_dec_ref(v_env_2827_);
lean_dec_ref(v_x_2822_);
v_a_2943_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2836_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2836_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
lean_dec_ref(v_opts_2832_);
lean_dec_ref(v_env_2827_);
lean_dec_ref(v_x_2822_);
v_a_2951_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2833_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2833_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___boxed(lean_object* v_x_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_2959_, v___y_2960_, v___y_2961_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object* v_x_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_){
_start:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___x_3049_; uint8_t v___x_3050_; 
v___x_3007_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
v___x_3008_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
v___x_3049_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
lean_inc(v_x_3003_);
v___x_3050_ = l_Lean_Syntax_isOfKind(v_x_3003_, v___x_3049_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; 
lean_dec(v_x_3003_);
v___x_3051_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3051_;
}
else
{
lean_object* v___x_3052_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; uint8_t v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; size_t v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; uint8_t v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; size_t v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; uint8_t v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; size_t v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; uint8_t v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; size_t v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; uint8_t v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; size_t v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v_expectedType_x3f_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v_prio_x3f_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v_name_x3f_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v_prec_x3f_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v_attrs_x3f_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v_doc_x3f_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___x_3529_; uint8_t v___x_3530_; 
v___x_3052_ = lean_unsigned_to_nat(0u);
v___x_3529_ = l_Lean_Syntax_getArg(v_x_3003_, v___x_3052_);
v___x_3530_ = l_Lean_Syntax_isNone(v___x_3529_);
if (v___x_3530_ == 0)
{
lean_object* v___x_3531_; uint8_t v___x_3532_; 
v___x_3531_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3529_);
v___x_3532_ = l_Lean_Syntax_matchesNull(v___x_3529_, v___x_3531_);
if (v___x_3532_ == 0)
{
lean_object* v___x_3533_; 
lean_dec(v___x_3529_);
lean_dec(v_x_3003_);
v___x_3533_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3533_;
}
else
{
lean_object* v_doc_x3f_3534_; lean_object* v___x_3535_; uint8_t v___x_3536_; 
v_doc_x3f_3534_ = l_Lean_Syntax_getArg(v___x_3529_, v___x_3052_);
lean_dec(v___x_3529_);
v___x_3535_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7));
lean_inc(v_doc_x3f_3534_);
v___x_3536_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3534_, v___x_3535_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; 
lean_dec(v_doc_x3f_3534_);
lean_dec(v_x_3003_);
v___x_3537_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3537_;
}
else
{
lean_object* v___x_3538_; 
v___x_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3538_, 0, v_doc_x3f_3534_);
v_doc_x3f_3513_ = v___x_3538_;
v___y_3514_ = v_a_3004_;
v___y_3515_ = v_a_3005_;
goto v___jp_3512_;
}
}
}
else
{
lean_object* v___x_3539_; 
lean_dec(v___x_3529_);
v___x_3539_ = lean_box(0);
v_doc_x3f_3513_ = v___x_3539_;
v___y_3514_ = v_a_3004_;
v___y_3515_ = v_a_3005_;
goto v___jp_3512_;
}
v___jp_3053_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
lean_inc_ref_n(v___y_3059_, 2);
v___x_3070_ = l_Array_append___redArg(v___y_3059_, v___y_3069_);
lean_dec_ref(v___y_3069_);
lean_inc_n(v___y_3054_, 3);
lean_inc_n(v___y_3060_, 6);
v___x_3071_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3071_, 0, v___y_3060_);
lean_ctor_set(v___x_3071_, 1, v___y_3054_);
lean_ctor_set(v___x_3071_, 2, v___x_3070_);
v___x_3072_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3072_, 0, v___y_3060_);
lean_ctor_set(v___x_3072_, 1, v___y_3054_);
lean_ctor_set(v___x_3072_, 2, v___y_3059_);
lean_inc_ref(v___x_3072_);
lean_inc(v___y_3067_);
v___x_3073_ = l_Lean_Syntax_node1(v___y_3060_, v___y_3067_, v___x_3072_);
lean_inc_ref(v___y_3061_);
v___x_3074_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___y_3060_);
lean_ctor_set(v___x_3074_, 1, v___y_3061_);
lean_inc_ref(v___y_3068_);
v___x_3075_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___y_3060_);
lean_ctor_set(v___x_3075_, 1, v___y_3068_);
v___x_3076_ = l_Lean_Syntax_node2(v___y_3060_, v___y_3054_, v___x_3075_, v___y_3056_);
if (lean_obj_tag(v___y_3063_) == 1)
{
lean_object* v_val_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v_val_3077_ = lean_ctor_get(v___y_3063_, 0);
lean_inc(v_val_3077_);
lean_dec_ref_known(v___y_3063_, 1);
v___x_3078_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(v___y_3060_);
v___x_3079_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3079_, 0, v___y_3060_);
lean_ctor_set(v___x_3079_, 1, v___x_3078_);
v___x_3080_ = l_Array_mkArray2___redArg(v___x_3079_, v_val_3077_);
v___y_3010_ = v___y_3054_;
v___y_3011_ = v___y_3055_;
v___y_3012_ = v___x_3072_;
v___y_3013_ = v___x_3071_;
v___y_3014_ = v___y_3057_;
v___y_3015_ = v___x_3074_;
v___y_3016_ = v___y_3058_;
v___y_3017_ = v___y_3059_;
v___y_3018_ = v___y_3060_;
v___y_3019_ = v___y_3062_;
v___y_3020_ = v___x_3073_;
v___y_3021_ = v___y_3065_;
v___y_3022_ = v___y_3064_;
v___y_3023_ = v___y_3066_;
v___y_3024_ = v___x_3076_;
v___y_3025_ = v___x_3080_;
goto v___jp_3009_;
}
else
{
lean_object* v___x_3081_; 
lean_dec(v___y_3063_);
v___x_3081_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_3010_ = v___y_3054_;
v___y_3011_ = v___y_3055_;
v___y_3012_ = v___x_3072_;
v___y_3013_ = v___x_3071_;
v___y_3014_ = v___y_3057_;
v___y_3015_ = v___x_3074_;
v___y_3016_ = v___y_3058_;
v___y_3017_ = v___y_3059_;
v___y_3018_ = v___y_3060_;
v___y_3019_ = v___y_3062_;
v___y_3020_ = v___x_3073_;
v___y_3021_ = v___y_3065_;
v___y_3022_ = v___y_3064_;
v___y_3023_ = v___y_3066_;
v___y_3024_ = v___x_3076_;
v___y_3025_ = v___x_3081_;
goto v___jp_3009_;
}
}
v___jp_3082_:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3097_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
v___x_3098_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
if (lean_obj_tag(v___y_3090_) == 1)
{
lean_object* v_val_3099_; lean_object* v___x_3100_; 
v_val_3099_ = lean_ctor_get(v___y_3090_, 0);
lean_inc(v_val_3099_);
lean_dec_ref_known(v___y_3090_, 1);
v___x_3100_ = l_Array_mkArray1___redArg(v_val_3099_);
v___y_3054_ = v___y_3083_;
v___y_3055_ = v___y_3084_;
v___y_3056_ = v___y_3085_;
v___y_3057_ = v___y_3086_;
v___y_3058_ = v___y_3087_;
v___y_3059_ = v___y_3088_;
v___y_3060_ = v___y_3089_;
v___y_3061_ = v___x_3097_;
v___y_3062_ = v___y_3091_;
v___y_3063_ = v___y_3092_;
v___y_3064_ = v___x_3098_;
v___y_3065_ = v___y_3093_;
v___y_3066_ = v___y_3094_;
v___y_3067_ = v___y_3095_;
v___y_3068_ = v___y_3096_;
v___y_3069_ = v___x_3100_;
goto v___jp_3053_;
}
else
{
lean_object* v___x_3101_; 
lean_dec(v___y_3090_);
v___x_3101_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_3054_ = v___y_3083_;
v___y_3055_ = v___y_3084_;
v___y_3056_ = v___y_3085_;
v___y_3057_ = v___y_3086_;
v___y_3058_ = v___y_3087_;
v___y_3059_ = v___y_3088_;
v___y_3060_ = v___y_3089_;
v___y_3061_ = v___x_3097_;
v___y_3062_ = v___y_3091_;
v___y_3063_ = v___y_3092_;
v___y_3064_ = v___x_3098_;
v___y_3065_ = v___y_3093_;
v___y_3066_ = v___y_3094_;
v___y_3067_ = v___y_3095_;
v___y_3068_ = v___y_3096_;
v___y_3069_ = v___x_3101_;
goto v___jp_3053_;
}
}
v___jp_3102_:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; size_t v_sz_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
lean_inc_ref_n(v___y_3110_, 2);
v___x_3126_ = l_Array_append___redArg(v___y_3110_, v___y_3125_);
lean_dec_ref(v___y_3125_);
lean_inc_n(v___y_3103_, 3);
lean_inc_n(v___y_3108_, 9);
v___x_3127_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3127_, 0, v___y_3108_);
lean_ctor_set(v___x_3127_, 1, v___y_3103_);
lean_ctor_set(v___x_3127_, 2, v___x_3126_);
v___x_3128_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
v___x_3129_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
v___x_3130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___y_3108_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
v___x_3131_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__6));
v___x_3132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___y_3108_);
lean_ctor_set(v___x_3132_, 1, v___x_3131_);
v___x_3133_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
v___x_3134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___y_3108_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
v___x_3135_ = l_Nat_reprFast(v___y_3124_);
v___x_3136_ = lean_box(2);
v___x_3137_ = l_Lean_Syntax_mkNumLit(v___x_3135_, v___x_3136_);
v___x_3138_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_3139_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___y_3108_);
lean_ctor_set(v___x_3139_, 1, v___x_3138_);
v___x_3140_ = l_Lean_Syntax_node5(v___y_3108_, v___x_3128_, v___x_3130_, v___x_3132_, v___x_3134_, v___x_3137_, v___x_3139_);
v___x_3141_ = l_Lean_Syntax_node1(v___y_3108_, v___y_3103_, v___x_3140_);
v_sz_3142_ = lean_array_size(v___y_3112_);
v___x_3143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_3142_, v___y_3120_, v___y_3112_);
v___x_3144_ = l_Array_append___redArg(v___y_3110_, v___x_3143_);
lean_dec_ref(v___x_3143_);
v___x_3145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3145_, 0, v___y_3108_);
lean_ctor_set(v___x_3145_, 1, v___y_3103_);
lean_ctor_set(v___x_3145_, 2, v___x_3144_);
v___x_3146_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
v___x_3147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___y_3108_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
v___x_3148_ = lean_unsigned_to_nat(10u);
v___x_3149_ = lean_mk_empty_array_with_capacity(v___x_3148_);
v___x_3150_ = lean_array_push(v___x_3149_, v___y_3117_);
v___x_3151_ = lean_array_push(v___x_3150_, v___y_3109_);
v___x_3152_ = lean_array_push(v___x_3151_, v___y_3122_);
v___x_3153_ = lean_array_push(v___x_3152_, v___y_3105_);
v___x_3154_ = lean_array_push(v___x_3153_, v___y_3113_);
v___x_3155_ = lean_array_push(v___x_3154_, v___x_3127_);
v___x_3156_ = lean_array_push(v___x_3155_, v___x_3141_);
v___x_3157_ = lean_array_push(v___x_3156_, v___x_3145_);
v___x_3158_ = lean_array_push(v___x_3157_, v___x_3147_);
lean_inc(v___y_3106_);
v___x_3159_ = lean_array_push(v___x_3158_, v___y_3106_);
lean_inc(v___y_3118_);
v___x_3160_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3160_, 0, v___y_3108_);
lean_ctor_set(v___x_3160_, 1, v___y_3118_);
lean_ctor_set(v___x_3160_, 2, v___x_3159_);
v___x_3161_ = l_Lean_Elab_Command_elabSyntax(v___x_3160_, v___y_3104_, v___y_3107_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v___x_3163_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_a_3162_);
lean_dec_ref_known(v___x_3161_, 1);
v___x_3163_ = l_Lean_Elab_Command_getRef___redArg(v___y_3104_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v___x_3165_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___x_3163_, 1);
v___x_3165_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3104_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_quotContext_x3f_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
lean_dec_ref_known(v___x_3165_, 1);
v_quotContext_x3f_3166_ = lean_ctor_get(v___y_3104_, 5);
v___x_3167_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3136_);
lean_ctor_set(v___x_3167_, 1, v_a_3162_);
lean_ctor_set(v___x_3167_, 2, v___y_3116_);
v___x_3168_ = l_Lean_SourceInfo_fromRef(v_a_3164_, v___y_3115_);
lean_dec(v_a_3164_);
if (lean_obj_tag(v_quotContext_x3f_3166_) == 0)
{
lean_object* v___x_3169_; 
v___x_3169_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3107_);
lean_dec_ref(v___x_3169_);
v___y_3083_ = v___y_3103_;
v___y_3084_ = v___y_3104_;
v___y_3085_ = v___y_3106_;
v___y_3086_ = v___y_3107_;
v___y_3087_ = v___x_3167_;
v___y_3088_ = v___y_3110_;
v___y_3089_ = v___x_3168_;
v___y_3090_ = v___y_3111_;
v___y_3091_ = v___y_3114_;
v___y_3092_ = v___y_3119_;
v___y_3093_ = v___y_3121_;
v___y_3094_ = v___x_3138_;
v___y_3095_ = v___y_3123_;
v___y_3096_ = v___x_3146_;
goto v___jp_3082_;
}
else
{
v___y_3083_ = v___y_3103_;
v___y_3084_ = v___y_3104_;
v___y_3085_ = v___y_3106_;
v___y_3086_ = v___y_3107_;
v___y_3087_ = v___x_3167_;
v___y_3088_ = v___y_3110_;
v___y_3089_ = v___x_3168_;
v___y_3090_ = v___y_3111_;
v___y_3091_ = v___y_3114_;
v___y_3092_ = v___y_3119_;
v___y_3093_ = v___y_3121_;
v___y_3094_ = v___x_3138_;
v___y_3095_ = v___y_3123_;
v___y_3096_ = v___x_3146_;
goto v___jp_3082_;
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_dec(v_a_3164_);
lean_dec(v_a_3162_);
lean_dec(v___y_3121_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3111_);
lean_dec(v___y_3106_);
v_a_3170_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3165_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3165_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec(v_a_3162_);
lean_dec(v___y_3121_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3111_);
lean_dec(v___y_3106_);
v_a_3178_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3163_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3163_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
lean_dec(v___y_3121_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3111_);
lean_dec(v___y_3106_);
v_a_3186_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_3161_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3161_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
v___jp_3194_:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
lean_inc_ref(v___y_3202_);
v___x_3218_ = l_Array_append___redArg(v___y_3202_, v___y_3217_);
lean_dec_ref(v___y_3217_);
lean_inc(v___y_3195_);
lean_inc(v___y_3200_);
v___x_3219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3219_, 0, v___y_3200_);
lean_ctor_set(v___x_3219_, 1, v___y_3195_);
lean_ctor_set(v___x_3219_, 2, v___x_3218_);
if (lean_obj_tag(v___y_3216_) == 1)
{
lean_object* v_val_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v_val_3220_ = lean_ctor_get(v___y_3216_, 0);
lean_inc(v_val_3220_);
lean_dec_ref_known(v___y_3216_, 1);
v___x_3221_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
v___x_3222_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc_n(v___y_3200_, 5);
v___x_3223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___y_3200_);
lean_ctor_set(v___x_3223_, 1, v___x_3222_);
v___x_3224_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__9));
v___x_3225_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___y_3200_);
lean_ctor_set(v___x_3225_, 1, v___x_3224_);
v___x_3226_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
v___x_3227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3227_, 0, v___y_3200_);
lean_ctor_set(v___x_3227_, 1, v___x_3226_);
v___x_3228_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
v___x_3229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3229_, 0, v___y_3200_);
lean_ctor_set(v___x_3229_, 1, v___x_3228_);
v___x_3230_ = l_Lean_Syntax_node5(v___y_3200_, v___x_3221_, v___x_3223_, v___x_3225_, v___x_3227_, v_val_3220_, v___x_3229_);
v___x_3231_ = l_Array_mkArray1___redArg(v___x_3230_);
v___y_3103_ = v___y_3195_;
v___y_3104_ = v___y_3196_;
v___y_3105_ = v___y_3197_;
v___y_3106_ = v___y_3198_;
v___y_3107_ = v___y_3199_;
v___y_3108_ = v___y_3200_;
v___y_3109_ = v___y_3201_;
v___y_3110_ = v___y_3202_;
v___y_3111_ = v___y_3203_;
v___y_3112_ = v___y_3204_;
v___y_3113_ = v___x_3219_;
v___y_3114_ = v___y_3205_;
v___y_3115_ = v___y_3206_;
v___y_3116_ = v___y_3209_;
v___y_3117_ = v___y_3208_;
v___y_3118_ = v___y_3207_;
v___y_3119_ = v___y_3210_;
v___y_3120_ = v___y_3211_;
v___y_3121_ = v___y_3213_;
v___y_3122_ = v___y_3212_;
v___y_3123_ = v___y_3215_;
v___y_3124_ = v___y_3214_;
v___y_3125_ = v___x_3231_;
goto v___jp_3102_;
}
else
{
lean_object* v___x_3232_; 
lean_dec(v___y_3216_);
v___x_3232_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_3103_ = v___y_3195_;
v___y_3104_ = v___y_3196_;
v___y_3105_ = v___y_3197_;
v___y_3106_ = v___y_3198_;
v___y_3107_ = v___y_3199_;
v___y_3108_ = v___y_3200_;
v___y_3109_ = v___y_3201_;
v___y_3110_ = v___y_3202_;
v___y_3111_ = v___y_3203_;
v___y_3112_ = v___y_3204_;
v___y_3113_ = v___x_3219_;
v___y_3114_ = v___y_3205_;
v___y_3115_ = v___y_3206_;
v___y_3116_ = v___y_3209_;
v___y_3117_ = v___y_3208_;
v___y_3118_ = v___y_3207_;
v___y_3119_ = v___y_3210_;
v___y_3120_ = v___y_3211_;
v___y_3121_ = v___y_3213_;
v___y_3122_ = v___y_3212_;
v___y_3123_ = v___y_3215_;
v___y_3124_ = v___y_3214_;
v___y_3125_ = v___x_3232_;
goto v___jp_3102_;
}
}
v___jp_3233_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
lean_inc_ref(v___y_3241_);
v___x_3258_ = l_Array_append___redArg(v___y_3241_, v___y_3257_);
lean_dec_ref(v___y_3257_);
lean_inc(v___y_3234_);
lean_inc(v___y_3240_);
v___x_3259_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3259_, 0, v___y_3240_);
lean_ctor_set(v___x_3259_, 1, v___y_3234_);
lean_ctor_set(v___x_3259_, 2, v___x_3258_);
v___x_3260_ = l_Lean_SourceInfo_fromRef(v___y_3251_, v___x_3050_);
lean_dec(v___y_3251_);
lean_inc_ref(v___y_3239_);
v___x_3261_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3260_);
lean_ctor_set(v___x_3261_, 1, v___y_3239_);
if (lean_obj_tag(v___y_3236_) == 1)
{
lean_object* v_val_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v_val_3262_ = lean_ctor_get(v___y_3236_, 0);
lean_inc(v_val_3262_);
lean_dec_ref_known(v___y_3236_, 1);
v___x_3263_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
v___x_3264_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc_n(v___y_3240_, 2);
v___x_3265_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___y_3240_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
v___x_3266_ = l_Lean_Syntax_node2(v___y_3240_, v___x_3263_, v___x_3265_, v_val_3262_);
v___x_3267_ = l_Array_mkArray1___redArg(v___x_3266_);
v___y_3195_ = v___y_3234_;
v___y_3196_ = v___y_3235_;
v___y_3197_ = v___x_3261_;
v___y_3198_ = v___y_3237_;
v___y_3199_ = v___y_3238_;
v___y_3200_ = v___y_3240_;
v___y_3201_ = v___x_3259_;
v___y_3202_ = v___y_3241_;
v___y_3203_ = v___y_3242_;
v___y_3204_ = v___y_3243_;
v___y_3205_ = v___y_3244_;
v___y_3206_ = v___y_3245_;
v___y_3207_ = v___y_3248_;
v___y_3208_ = v___y_3247_;
v___y_3209_ = v___y_3246_;
v___y_3210_ = v___y_3249_;
v___y_3211_ = v___y_3250_;
v___y_3212_ = v___y_3253_;
v___y_3213_ = v___y_3252_;
v___y_3214_ = v___y_3255_;
v___y_3215_ = v___y_3254_;
v___y_3216_ = v___y_3256_;
v___y_3217_ = v___x_3267_;
goto v___jp_3194_;
}
else
{
lean_object* v___x_3268_; 
lean_dec(v___y_3236_);
v___x_3268_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_3195_ = v___y_3234_;
v___y_3196_ = v___y_3235_;
v___y_3197_ = v___x_3261_;
v___y_3198_ = v___y_3237_;
v___y_3199_ = v___y_3238_;
v___y_3200_ = v___y_3240_;
v___y_3201_ = v___x_3259_;
v___y_3202_ = v___y_3241_;
v___y_3203_ = v___y_3242_;
v___y_3204_ = v___y_3243_;
v___y_3205_ = v___y_3244_;
v___y_3206_ = v___y_3245_;
v___y_3207_ = v___y_3248_;
v___y_3208_ = v___y_3247_;
v___y_3209_ = v___y_3246_;
v___y_3210_ = v___y_3249_;
v___y_3211_ = v___y_3250_;
v___y_3212_ = v___y_3253_;
v___y_3213_ = v___y_3252_;
v___y_3214_ = v___y_3255_;
v___y_3215_ = v___y_3254_;
v___y_3216_ = v___y_3256_;
v___y_3217_ = v___x_3268_;
goto v___jp_3194_;
}
}
v___jp_3269_:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
lean_inc_ref(v___y_3278_);
v___x_3294_ = l_Array_append___redArg(v___y_3278_, v___y_3293_);
lean_dec_ref(v___y_3293_);
lean_inc(v___y_3270_);
lean_inc(v___y_3277_);
v___x_3295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3295_, 0, v___y_3277_);
lean_ctor_set(v___x_3295_, 1, v___y_3270_);
lean_ctor_set(v___x_3295_, 2, v___x_3294_);
if (lean_obj_tag(v___y_3276_) == 1)
{
lean_object* v_val_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v_val_3296_ = lean_ctor_get(v___y_3276_, 0);
lean_inc(v_val_3296_);
lean_dec_ref_known(v___y_3276_, 1);
v___x_3297_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(v___y_3281_);
v___x_3298_ = l_Lean_Name_mkStr4(v___x_3007_, v___x_3008_, v___y_3281_, v___x_3297_);
v___x_3299_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc_n(v___y_3277_, 4);
v___x_3300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___y_3277_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
lean_inc_ref(v___y_3278_);
v___x_3301_ = l_Array_append___redArg(v___y_3278_, v_val_3296_);
lean_dec(v_val_3296_);
lean_inc(v___y_3270_);
v___x_3302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3302_, 0, v___y_3277_);
lean_ctor_set(v___x_3302_, 1, v___y_3270_);
lean_ctor_set(v___x_3302_, 2, v___x_3301_);
v___x_3303_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
v___x_3304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___y_3277_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = l_Lean_Syntax_node3(v___y_3277_, v___x_3298_, v___x_3300_, v___x_3302_, v___x_3304_);
v___x_3306_ = l_Array_mkArray1___redArg(v___x_3305_);
v___y_3234_ = v___y_3270_;
v___y_3235_ = v___y_3271_;
v___y_3236_ = v___y_3272_;
v___y_3237_ = v___y_3273_;
v___y_3238_ = v___y_3274_;
v___y_3239_ = v___y_3275_;
v___y_3240_ = v___y_3277_;
v___y_3241_ = v___y_3278_;
v___y_3242_ = v___y_3279_;
v___y_3243_ = v___y_3280_;
v___y_3244_ = v___y_3281_;
v___y_3245_ = v___y_3282_;
v___y_3246_ = v___y_3284_;
v___y_3247_ = v___x_3295_;
v___y_3248_ = v___y_3283_;
v___y_3249_ = v___y_3285_;
v___y_3250_ = v___y_3287_;
v___y_3251_ = v___y_3286_;
v___y_3252_ = v___y_3289_;
v___y_3253_ = v___y_3288_;
v___y_3254_ = v___y_3291_;
v___y_3255_ = v___y_3290_;
v___y_3256_ = v___y_3292_;
v___y_3257_ = v___x_3306_;
goto v___jp_3233_;
}
else
{
lean_object* v___x_3307_; 
lean_dec(v___y_3276_);
v___x_3307_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_3234_ = v___y_3270_;
v___y_3235_ = v___y_3271_;
v___y_3236_ = v___y_3272_;
v___y_3237_ = v___y_3273_;
v___y_3238_ = v___y_3274_;
v___y_3239_ = v___y_3275_;
v___y_3240_ = v___y_3277_;
v___y_3241_ = v___y_3278_;
v___y_3242_ = v___y_3279_;
v___y_3243_ = v___y_3280_;
v___y_3244_ = v___y_3281_;
v___y_3245_ = v___y_3282_;
v___y_3246_ = v___y_3284_;
v___y_3247_ = v___x_3295_;
v___y_3248_ = v___y_3283_;
v___y_3249_ = v___y_3285_;
v___y_3250_ = v___y_3287_;
v___y_3251_ = v___y_3286_;
v___y_3252_ = v___y_3289_;
v___y_3253_ = v___y_3288_;
v___y_3254_ = v___y_3291_;
v___y_3255_ = v___y_3290_;
v___y_3256_ = v___y_3292_;
v___y_3257_ = v___x_3307_;
goto v___jp_3233_;
}
}
v___jp_3308_:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3328_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__12));
v___x_3329_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__13));
v___x_3330_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
v___x_3331_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(v___y_3315_) == 1)
{
lean_object* v_val_3332_; lean_object* v___x_3333_; 
v_val_3332_ = lean_ctor_get(v___y_3315_, 0);
lean_inc(v_val_3332_);
v___x_3333_ = l_Array_mkArray1___redArg(v_val_3332_);
v___y_3270_ = v___x_3330_;
v___y_3271_ = v___y_3309_;
v___y_3272_ = v___y_3310_;
v___y_3273_ = v___y_3311_;
v___y_3274_ = v___y_3312_;
v___y_3275_ = v___x_3328_;
v___y_3276_ = v___y_3313_;
v___y_3277_ = v___y_3314_;
v___y_3278_ = v___x_3331_;
v___y_3279_ = v___y_3315_;
v___y_3280_ = v___y_3316_;
v___y_3281_ = v___y_3317_;
v___y_3282_ = v___y_3318_;
v___y_3283_ = v___x_3329_;
v___y_3284_ = v___y_3319_;
v___y_3285_ = v___y_3320_;
v___y_3286_ = v___y_3322_;
v___y_3287_ = v___y_3321_;
v___y_3288_ = v___y_3324_;
v___y_3289_ = v___y_3323_;
v___y_3290_ = v___y_3326_;
v___y_3291_ = v___y_3325_;
v___y_3292_ = v___y_3327_;
v___y_3293_ = v___x_3333_;
goto v___jp_3269_;
}
else
{
lean_object* v___x_3334_; 
v___x_3334_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
v___y_3270_ = v___x_3330_;
v___y_3271_ = v___y_3309_;
v___y_3272_ = v___y_3310_;
v___y_3273_ = v___y_3311_;
v___y_3274_ = v___y_3312_;
v___y_3275_ = v___x_3328_;
v___y_3276_ = v___y_3313_;
v___y_3277_ = v___y_3314_;
v___y_3278_ = v___x_3331_;
v___y_3279_ = v___y_3315_;
v___y_3280_ = v___y_3316_;
v___y_3281_ = v___y_3317_;
v___y_3282_ = v___y_3318_;
v___y_3283_ = v___x_3329_;
v___y_3284_ = v___y_3319_;
v___y_3285_ = v___y_3320_;
v___y_3286_ = v___y_3322_;
v___y_3287_ = v___y_3321_;
v___y_3288_ = v___y_3324_;
v___y_3289_ = v___y_3323_;
v___y_3290_ = v___y_3326_;
v___y_3291_ = v___y_3325_;
v___y_3292_ = v___y_3327_;
v___y_3293_ = v___x_3334_;
goto v___jp_3269_;
}
}
v___jp_3335_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3352_ = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(v___x_3352_, 0, v___y_3342_);
v___x_3353_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v___x_3352_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v_args_3355_; size_t v_sz_3356_; size_t v___x_3357_; lean_object* v___x_3358_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_a_3354_);
lean_dec_ref_known(v___x_3353_, 1);
v_args_3355_ = l_Lean_Syntax_getArgs(v___y_3345_);
lean_dec(v___y_3345_);
v_sz_3356_ = lean_array_size(v_args_3355_);
v___x_3357_ = ((size_t)0ULL);
v___x_3358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_3356_, v___x_3357_, v_args_3355_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v___x_3360_; lean_object* v_fst_3361_; lean_object* v_snd_3362_; lean_object* v___x_3363_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_a_3359_);
lean_dec_ref_known(v___x_3358_, 1);
v___x_3360_ = l_Array_unzip___redArg(v_a_3359_);
lean_dec(v_a_3359_);
v_fst_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_fst_3361_);
v_snd_3362_ = lean_ctor_get(v___x_3360_, 1);
lean_inc(v_snd_3362_);
lean_dec_ref(v___x_3360_);
v___x_3363_ = l_Lean_Elab_Command_getRef___redArg(v___y_3350_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3365_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3364_);
lean_dec_ref_known(v___x_3363_, 1);
v___x_3365_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3350_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v_quotContext_x3f_3366_; lean_object* v___x_3367_; uint8_t v___x_3368_; lean_object* v___x_3369_; 
lean_dec_ref_known(v___x_3365_, 1);
v_quotContext_x3f_3366_ = lean_ctor_get(v___y_3350_, 5);
v___x_3367_ = l_Lean_Syntax_getArg(v___y_3346_, v___y_3338_);
lean_dec(v___y_3346_);
v___x_3368_ = 0;
v___x_3369_ = l_Lean_SourceInfo_fromRef(v_a_3364_, v___x_3368_);
lean_dec(v_a_3364_);
if (lean_obj_tag(v_quotContext_x3f_3366_) == 0)
{
lean_object* v___x_3370_; 
v___x_3370_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3351_);
lean_dec_ref(v___x_3370_);
v___y_3309_ = v___y_3350_;
v___y_3310_ = v___y_3336_;
v___y_3311_ = v___y_3337_;
v___y_3312_ = v___y_3351_;
v___y_3313_ = v___y_3339_;
v___y_3314_ = v___x_3369_;
v___y_3315_ = v___y_3340_;
v___y_3316_ = v_fst_3361_;
v___y_3317_ = v___y_3341_;
v___y_3318_ = v___x_3368_;
v___y_3319_ = v_snd_3362_;
v___y_3320_ = v_expectedType_x3f_3349_;
v___y_3321_ = v___x_3357_;
v___y_3322_ = v___y_3343_;
v___y_3323_ = v___x_3367_;
v___y_3324_ = v___y_3344_;
v___y_3325_ = v___y_3347_;
v___y_3326_ = v_a_3354_;
v___y_3327_ = v___y_3348_;
goto v___jp_3308_;
}
else
{
v___y_3309_ = v___y_3350_;
v___y_3310_ = v___y_3336_;
v___y_3311_ = v___y_3337_;
v___y_3312_ = v___y_3351_;
v___y_3313_ = v___y_3339_;
v___y_3314_ = v___x_3369_;
v___y_3315_ = v___y_3340_;
v___y_3316_ = v_fst_3361_;
v___y_3317_ = v___y_3341_;
v___y_3318_ = v___x_3368_;
v___y_3319_ = v_snd_3362_;
v___y_3320_ = v_expectedType_x3f_3349_;
v___y_3321_ = v___x_3357_;
v___y_3322_ = v___y_3343_;
v___y_3323_ = v___x_3367_;
v___y_3324_ = v___y_3344_;
v___y_3325_ = v___y_3347_;
v___y_3326_ = v_a_3354_;
v___y_3327_ = v___y_3348_;
goto v___jp_3308_;
}
}
else
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
lean_dec(v_a_3364_);
lean_dec(v_snd_3362_);
lean_dec(v_fst_3361_);
lean_dec(v_a_3354_);
lean_dec(v_expectedType_x3f_3349_);
lean_dec(v___y_3348_);
lean_dec(v___y_3346_);
lean_dec(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec(v___y_3337_);
lean_dec(v___y_3336_);
v_a_3371_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3365_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3365_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
lean_dec(v_snd_3362_);
lean_dec(v_fst_3361_);
lean_dec(v_a_3354_);
lean_dec(v_expectedType_x3f_3349_);
lean_dec(v___y_3348_);
lean_dec(v___y_3346_);
lean_dec(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec(v___y_3337_);
lean_dec(v___y_3336_);
v_a_3379_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3363_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3363_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec(v_a_3354_);
lean_dec(v_expectedType_x3f_3349_);
lean_dec(v___y_3348_);
lean_dec(v___y_3346_);
lean_dec(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec(v___y_3337_);
lean_dec(v___y_3336_);
v_a_3387_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3358_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3358_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
else
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
lean_dec(v_expectedType_x3f_3349_);
lean_dec(v___y_3348_);
lean_dec(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec(v___y_3337_);
lean_dec(v___y_3336_);
v_a_3395_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v___x_3353_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3353_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3395_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
v___jp_3403_:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; uint8_t v___x_3421_; 
v___x_3418_ = lean_unsigned_to_nat(8u);
v___x_3419_ = l_Lean_Syntax_getArg(v_x_3003_, v___x_3418_);
v___x_3420_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__15));
lean_inc(v___x_3419_);
v___x_3421_ = l_Lean_Syntax_isOfKind(v___x_3419_, v___x_3420_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; 
lean_dec(v___x_3419_);
lean_dec(v_prio_x3f_3415_);
lean_dec(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec(v___y_3411_);
lean_dec(v___y_3409_);
lean_dec(v___y_3407_);
lean_dec(v___y_3405_);
lean_dec(v_x_3003_);
v___x_3422_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3422_;
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; uint8_t v___x_3427_; 
v___x_3423_ = lean_unsigned_to_nat(7u);
v___x_3424_ = l_Lean_Syntax_getArg(v_x_3003_, v___x_3423_);
lean_dec(v_x_3003_);
v___x_3425_ = l_Lean_Syntax_getArg(v___x_3419_, v___y_3410_);
v___x_3426_ = l_Lean_Syntax_getArg(v___x_3419_, v___y_3406_);
v___x_3427_ = l_Lean_Syntax_isNone(v___x_3426_);
if (v___x_3427_ == 0)
{
uint8_t v___x_3428_; 
lean_inc(v___x_3426_);
v___x_3428_ = l_Lean_Syntax_matchesNull(v___x_3426_, v___y_3406_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3429_; 
lean_dec(v___x_3426_);
lean_dec(v___x_3425_);
lean_dec(v___x_3424_);
lean_dec(v___x_3419_);
lean_dec(v_prio_x3f_3415_);
lean_dec(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec(v___y_3411_);
lean_dec(v___y_3409_);
lean_dec(v___y_3407_);
lean_dec(v___y_3405_);
v___x_3429_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3429_;
}
else
{
lean_object* v_expectedType_x3f_3430_; lean_object* v___x_3431_; 
v_expectedType_x3f_3430_ = l_Lean_Syntax_getArg(v___x_3426_, v___y_3410_);
lean_dec(v___x_3426_);
v___x_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3431_, 0, v_expectedType_x3f_3430_);
v___y_3336_ = v___y_3407_;
v___y_3337_ = v___x_3425_;
v___y_3338_ = v___y_3408_;
v___y_3339_ = v___y_3411_;
v___y_3340_ = v___y_3414_;
v___y_3341_ = v___y_3404_;
v___y_3342_ = v_prio_x3f_3415_;
v___y_3343_ = v___y_3405_;
v___y_3344_ = v___y_3409_;
v___y_3345_ = v___x_3424_;
v___y_3346_ = v___x_3419_;
v___y_3347_ = v___y_3412_;
v___y_3348_ = v___y_3413_;
v_expectedType_x3f_3349_ = v___x_3431_;
v___y_3350_ = v___y_3416_;
v___y_3351_ = v___y_3417_;
goto v___jp_3335_;
}
}
else
{
lean_object* v___x_3432_; 
lean_dec(v___x_3426_);
v___x_3432_ = lean_box(0);
v___y_3336_ = v___y_3407_;
v___y_3337_ = v___x_3425_;
v___y_3338_ = v___y_3408_;
v___y_3339_ = v___y_3411_;
v___y_3340_ = v___y_3414_;
v___y_3341_ = v___y_3404_;
v___y_3342_ = v_prio_x3f_3415_;
v___y_3343_ = v___y_3405_;
v___y_3344_ = v___y_3409_;
v___y_3345_ = v___x_3424_;
v___y_3346_ = v___x_3419_;
v___y_3347_ = v___y_3412_;
v___y_3348_ = v___y_3413_;
v_expectedType_x3f_3349_ = v___x_3432_;
v___y_3350_ = v___y_3416_;
v___y_3351_ = v___y_3417_;
goto v___jp_3335_;
}
}
}
v___jp_3433_:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; uint8_t v___x_3450_; 
v___x_3448_ = lean_unsigned_to_nat(6u);
v___x_3449_ = l_Lean_Syntax_getArg(v_x_3003_, v___x_3448_);
v___x_3450_ = l_Lean_Syntax_isNone(v___x_3449_);
if (v___x_3450_ == 0)
{
uint8_t v___x_3451_; 
lean_inc(v___x_3449_);
v___x_3451_ = l_Lean_Syntax_matchesNull(v___x_3449_, v___y_3440_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3452_; 
lean_dec(v___x_3449_);
lean_dec(v_name_x3f_3445_);
lean_dec(v___y_3444_);
lean_dec(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec(v_x_3003_);
v___x_3452_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3452_;
}
else
{
lean_object* v___x_3453_; lean_object* v___x_3454_; uint8_t v___x_3455_; 
v___x_3453_ = l_Lean_Syntax_getArg(v___x_3449_, v___x_3052_);
lean_dec(v___x_3449_);
v___x_3454_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
lean_inc(v___x_3453_);
v___x_3455_ = l_Lean_Syntax_isOfKind(v___x_3453_, v___x_3454_);
if (v___x_3455_ == 0)
{
lean_object* v___x_3456_; 
lean_dec(v___x_3453_);
lean_dec(v_name_x3f_3445_);
lean_dec(v___y_3444_);
lean_dec(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec(v_x_3003_);
v___x_3456_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3456_;
}
else
{
lean_object* v_prio_x3f_3457_; lean_object* v___x_3458_; 
v_prio_x3f_3457_ = l_Lean_Syntax_getArg(v___x_3453_, v___y_3438_);
lean_dec(v___x_3453_);
v___x_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3458_, 0, v_prio_x3f_3457_);
v___y_3404_ = v___y_3434_;
v___y_3405_ = v___y_3435_;
v___y_3406_ = v___y_3437_;
v___y_3407_ = v___y_3436_;
v___y_3408_ = v___y_3439_;
v___y_3409_ = v___y_3441_;
v___y_3410_ = v___y_3440_;
v___y_3411_ = v___y_3442_;
v___y_3412_ = v___y_3443_;
v___y_3413_ = v_name_x3f_3445_;
v___y_3414_ = v___y_3444_;
v_prio_x3f_3415_ = v___x_3458_;
v___y_3416_ = v___y_3446_;
v___y_3417_ = v___y_3447_;
goto v___jp_3403_;
}
}
}
else
{
lean_object* v___x_3459_; 
lean_dec(v___x_3449_);
v___x_3459_ = lean_box(0);
v___y_3404_ = v___y_3434_;
v___y_3405_ = v___y_3435_;
v___y_3406_ = v___y_3437_;
v___y_3407_ = v___y_3436_;
v___y_3408_ = v___y_3439_;
v___y_3409_ = v___y_3441_;
v___y_3410_ = v___y_3440_;
v___y_3411_ = v___y_3442_;
v___y_3412_ = v___y_3443_;
v___y_3413_ = v_name_x3f_3445_;
v___y_3414_ = v___y_3444_;
v_prio_x3f_3415_ = v___x_3459_;
v___y_3416_ = v___y_3446_;
v___y_3417_ = v___y_3447_;
goto v___jp_3403_;
}
}
v___jp_3460_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; uint8_t v___x_3476_; 
v___x_3474_ = lean_unsigned_to_nat(5u);
v___x_3475_ = l_Lean_Syntax_getArg(v_x_3003_, v___x_3474_);
v___x_3476_ = l_Lean_Syntax_isNone(v___x_3475_);
if (v___x_3476_ == 0)
{
uint8_t v___x_3477_; 
lean_inc(v___x_3475_);
v___x_3477_ = l_Lean_Syntax_matchesNull(v___x_3475_, v___y_3467_);
if (v___x_3477_ == 0)
{
lean_object* v___x_3478_; 
lean_dec(v___x_3475_);
lean_dec(v_prec_x3f_3471_);
lean_dec(v___y_3470_);
lean_dec(v___y_3468_);
lean_dec(v___y_3466_);
lean_dec(v___y_3462_);
lean_dec(v_x_3003_);
v___x_3478_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3478_;
}
else
{
lean_object* v___x_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; 
v___x_3479_ = l_Lean_Syntax_getArg(v___x_3475_, v___x_3052_);
lean_dec(v___x_3475_);
v___x_3480_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
lean_inc(v___x_3479_);
v___x_3481_ = l_Lean_Syntax_isOfKind(v___x_3479_, v___x_3480_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; 
lean_dec(v___x_3479_);
lean_dec(v_prec_x3f_3471_);
lean_dec(v___y_3470_);
lean_dec(v___y_3468_);
lean_dec(v___y_3466_);
lean_dec(v___y_3462_);
lean_dec(v_x_3003_);
v___x_3482_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3482_;
}
else
{
lean_object* v_name_x3f_3483_; lean_object* v___x_3484_; 
v_name_x3f_3483_ = l_Lean_Syntax_getArg(v___x_3479_, v___y_3465_);
lean_dec(v___x_3479_);
v___x_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3484_, 0, v_name_x3f_3483_);
v___y_3434_ = v___y_3461_;
v___y_3435_ = v___y_3462_;
v___y_3436_ = v_prec_x3f_3471_;
v___y_3437_ = v___y_3463_;
v___y_3438_ = v___y_3465_;
v___y_3439_ = v___y_3464_;
v___y_3440_ = v___y_3467_;
v___y_3441_ = v___y_3466_;
v___y_3442_ = v___y_3468_;
v___y_3443_ = v___y_3469_;
v___y_3444_ = v___y_3470_;
v_name_x3f_3445_ = v___x_3484_;
v___y_3446_ = v___y_3472_;
v___y_3447_ = v___y_3473_;
goto v___jp_3433_;
}
}
}
else
{
lean_object* v___x_3485_; 
lean_dec(v___x_3475_);
v___x_3485_ = lean_box(0);
v___y_3434_ = v___y_3461_;
v___y_3435_ = v___y_3462_;
v___y_3436_ = v_prec_x3f_3471_;
v___y_3437_ = v___y_3463_;
v___y_3438_ = v___y_3465_;
v___y_3439_ = v___y_3464_;
v___y_3440_ = v___y_3467_;
v___y_3441_ = v___y_3466_;
v___y_3442_ = v___y_3468_;
v___y_3443_ = v___y_3469_;
v___y_3444_ = v___y_3470_;
v_name_x3f_3445_ = v___x_3485_;
v___y_3446_ = v___y_3472_;
v___y_3447_ = v___y_3473_;
goto v___jp_3433_;
}
}
v___jp_3486_:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; uint8_t v___x_3496_; 
v___x_3492_ = lean_unsigned_to_nat(2u);
v___x_3493_ = l_Lean_Syntax_getArg(v_x_3003_, v___x_3492_);
v___x_3494_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
v___x_3495_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(v___x_3493_);
v___x_3496_ = l_Lean_Syntax_isOfKind(v___x_3493_, v___x_3495_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; 
lean_dec(v___x_3493_);
lean_dec(v_attrs_x3f_3489_);
lean_dec(v___y_3488_);
lean_dec(v_x_3003_);
v___x_3497_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3497_;
}
else
{
lean_object* v___x_3498_; lean_object* v_tk_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; 
v___x_3498_ = lean_unsigned_to_nat(3u);
v_tk_3499_ = l_Lean_Syntax_getArg(v_x_3003_, v___x_3498_);
v___x_3500_ = lean_unsigned_to_nat(4u);
v___x_3501_ = l_Lean_Syntax_getArg(v_x_3003_, v___x_3500_);
v___x_3502_ = l_Lean_Syntax_isNone(v___x_3501_);
if (v___x_3502_ == 0)
{
uint8_t v___x_3503_; 
lean_inc(v___x_3501_);
v___x_3503_ = l_Lean_Syntax_matchesNull(v___x_3501_, v___y_3487_);
if (v___x_3503_ == 0)
{
lean_object* v___x_3504_; 
lean_dec(v___x_3501_);
lean_dec(v_tk_3499_);
lean_dec(v___x_3493_);
lean_dec(v_attrs_x3f_3489_);
lean_dec(v___y_3488_);
lean_dec(v_x_3003_);
v___x_3504_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3504_;
}
else
{
lean_object* v___x_3505_; lean_object* v___x_3506_; uint8_t v___x_3507_; 
v___x_3505_ = l_Lean_Syntax_getArg(v___x_3501_, v___x_3052_);
lean_dec(v___x_3501_);
v___x_3506_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
lean_inc(v___x_3505_);
v___x_3507_ = l_Lean_Syntax_isOfKind(v___x_3505_, v___x_3506_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; 
lean_dec(v___x_3505_);
lean_dec(v_tk_3499_);
lean_dec(v___x_3493_);
lean_dec(v_attrs_x3f_3489_);
lean_dec(v___y_3488_);
lean_dec(v_x_3003_);
v___x_3508_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3508_;
}
else
{
lean_object* v_prec_x3f_3509_; lean_object* v___x_3510_; 
v_prec_x3f_3509_ = l_Lean_Syntax_getArg(v___x_3505_, v___y_3487_);
lean_dec(v___x_3505_);
v___x_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3510_, 0, v_prec_x3f_3509_);
v___y_3461_ = v___x_3494_;
v___y_3462_ = v_tk_3499_;
v___y_3463_ = v___x_3492_;
v___y_3464_ = v___x_3500_;
v___y_3465_ = v___x_3498_;
v___y_3466_ = v___x_3493_;
v___y_3467_ = v___y_3487_;
v___y_3468_ = v_attrs_x3f_3489_;
v___y_3469_ = v___x_3495_;
v___y_3470_ = v___y_3488_;
v_prec_x3f_3471_ = v___x_3510_;
v___y_3472_ = v___y_3490_;
v___y_3473_ = v___y_3491_;
goto v___jp_3460_;
}
}
}
else
{
lean_object* v___x_3511_; 
lean_dec(v___x_3501_);
v___x_3511_ = lean_box(0);
v___y_3461_ = v___x_3494_;
v___y_3462_ = v_tk_3499_;
v___y_3463_ = v___x_3492_;
v___y_3464_ = v___x_3500_;
v___y_3465_ = v___x_3498_;
v___y_3466_ = v___x_3493_;
v___y_3467_ = v___y_3487_;
v___y_3468_ = v_attrs_x3f_3489_;
v___y_3469_ = v___x_3495_;
v___y_3470_ = v___y_3488_;
v_prec_x3f_3471_ = v___x_3511_;
v___y_3472_ = v___y_3490_;
v___y_3473_ = v___y_3491_;
goto v___jp_3460_;
}
}
}
v___jp_3512_:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; uint8_t v___x_3518_; 
v___x_3516_ = lean_unsigned_to_nat(1u);
v___x_3517_ = l_Lean_Syntax_getArg(v_x_3003_, v___x_3516_);
v___x_3518_ = l_Lean_Syntax_isNone(v___x_3517_);
if (v___x_3518_ == 0)
{
uint8_t v___x_3519_; 
lean_inc(v___x_3517_);
v___x_3519_ = l_Lean_Syntax_matchesNull(v___x_3517_, v___x_3516_);
if (v___x_3519_ == 0)
{
lean_object* v___x_3520_; 
lean_dec(v___x_3517_);
lean_dec(v_doc_x3f_3513_);
lean_dec(v_x_3003_);
v___x_3520_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3520_;
}
else
{
lean_object* v___x_3521_; lean_object* v___x_3522_; uint8_t v___x_3523_; 
v___x_3521_ = l_Lean_Syntax_getArg(v___x_3517_, v___x_3052_);
lean_dec(v___x_3517_);
v___x_3522_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5));
lean_inc(v___x_3521_);
v___x_3523_ = l_Lean_Syntax_isOfKind(v___x_3521_, v___x_3522_);
if (v___x_3523_ == 0)
{
lean_object* v___x_3524_; 
lean_dec(v___x_3521_);
lean_dec(v_doc_x3f_3513_);
lean_dec(v_x_3003_);
v___x_3524_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return v___x_3524_;
}
else
{
lean_object* v___x_3525_; lean_object* v_attrs_x3f_3526_; lean_object* v___x_3527_; 
v___x_3525_ = l_Lean_Syntax_getArg(v___x_3521_, v___x_3516_);
lean_dec(v___x_3521_);
v_attrs_x3f_3526_ = l_Lean_Syntax_getArgs(v___x_3525_);
lean_dec(v___x_3525_);
v___x_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3527_, 0, v_attrs_x3f_3526_);
v___y_3487_ = v___x_3516_;
v___y_3488_ = v_doc_x3f_3513_;
v_attrs_x3f_3489_ = v___x_3527_;
v___y_3490_ = v___y_3514_;
v___y_3491_ = v___y_3515_;
goto v___jp_3486_;
}
}
}
else
{
lean_object* v___x_3528_; 
lean_dec(v___x_3517_);
v___x_3528_ = lean_box(0);
v___y_3487_ = v___x_3516_;
v___y_3488_ = v_doc_x3f_3513_;
v_attrs_x3f_3489_ = v___x_3528_;
v___y_3490_ = v___y_3514_;
v___y_3491_ = v___y_3515_;
goto v___jp_3486_;
}
}
}
v___jp_3009_:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
lean_inc_ref(v___y_3017_);
v___x_3026_ = l_Array_append___redArg(v___y_3017_, v___y_3025_);
lean_dec_ref(v___y_3025_);
lean_inc_n(v___y_3010_, 4);
lean_inc_n(v___y_3018_, 11);
v___x_3027_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3027_, 0, v___y_3018_);
lean_ctor_set(v___x_3027_, 1, v___y_3010_);
lean_ctor_set(v___x_3027_, 2, v___x_3026_);
v___x_3028_ = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref_n(v___y_3019_, 3);
v___x_3029_ = l_Lean_Name_mkStr4(v___x_3007_, v___x_3008_, v___y_3019_, v___x_3028_);
v___x_3030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
v___x_3031_ = l_Lean_Name_mkStr4(v___x_3007_, v___x_3008_, v___y_3019_, v___x_3030_);
v___x_3032_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
v___x_3033_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___y_3018_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
v___x_3034_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__0));
v___x_3035_ = l_Lean_Name_mkStr4(v___x_3007_, v___x_3008_, v___y_3019_, v___x_3034_);
v___x_3036_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__1));
v___x_3037_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___y_3018_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
lean_inc_ref(v___y_3023_);
v___x_3038_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___y_3018_);
lean_ctor_set(v___x_3038_, 1, v___y_3023_);
v___x_3039_ = l_Lean_Syntax_node3(v___y_3018_, v___x_3035_, v___x_3037_, v___y_3016_, v___x_3038_);
v___x_3040_ = l_Lean_Syntax_node1(v___y_3018_, v___y_3010_, v___x_3039_);
v___x_3041_ = l_Lean_Syntax_node1(v___y_3018_, v___y_3010_, v___x_3040_);
v___x_3042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
v___x_3043_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3043_, 0, v___y_3018_);
lean_ctor_set(v___x_3043_, 1, v___x_3042_);
v___x_3044_ = l_Lean_Syntax_node4(v___y_3018_, v___x_3031_, v___x_3033_, v___x_3041_, v___x_3043_, v___y_3021_);
v___x_3045_ = l_Lean_Syntax_node1(v___y_3018_, v___y_3010_, v___x_3044_);
v___x_3046_ = l_Lean_Syntax_node1(v___y_3018_, v___x_3029_, v___x_3045_);
lean_inc(v___y_3012_);
lean_inc(v___y_3022_);
v___x_3047_ = l_Lean_Syntax_node8(v___y_3018_, v___y_3022_, v___y_3013_, v___y_3012_, v___y_3020_, v___y_3015_, v___y_3012_, v___y_3024_, v___x_3027_, v___x_3046_);
v___x_3048_ = l_Lean_Elab_Command_elabCommand(v___x_3047_, v___y_3011_, v___y_3014_);
return v___x_3048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___boxed(lean_object* v_x_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_Elab_Command_elabElab(v_x_3540_, v_a_3541_, v_a_3542_);
lean_dec(v_a_3542_);
lean_dec_ref(v_a_3541_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(lean_object* v_00_u03b1_3545_, lean_object* v_x_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v___x_3549_; 
v___x_3549_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_3546_, v___y_3548_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3550_, lean_object* v_x_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(v_00_u03b1_3550_, v_x_3551_, v___y_3552_, v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec_ref(v_x_3551_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(lean_object* v_00_u03b1_3555_, lean_object* v_ref_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v___x_3560_; 
v___x_3560_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_3556_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___boxed(lean_object* v_00_u03b1_3561_, lean_object* v_ref_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(v_00_u03b1_3561_, v_ref_3562_, v___y_3563_, v___y_3564_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(lean_object* v_00_u03b1_3567_, lean_object* v_x_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
lean_object* v___x_3572_; 
v___x_3572_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(v_x_3568_, v___y_3569_, v___y_3570_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___boxed(lean_object* v_00_u03b1_3573_, lean_object* v_x_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(v_00_u03b1_3573_, v_x_3574_, v___y_3575_, v___y_3576_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(lean_object* v_as_3579_, lean_object* v_as_x27_3580_, lean_object* v_b_3581_, lean_object* v_a_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_3580_, v_b_3581_, v___y_3583_, v___y_3584_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___boxed(lean_object* v_as_3587_, lean_object* v_as_x27_3588_, lean_object* v_b_3589_, lean_object* v_a_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(v_as_3587_, v_as_x27_3588_, v_b_3589_, v_a_3590_, v___y_3591_, v___y_3592_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v_as_x27_3588_);
lean_dec(v_as_3587_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3595_, lean_object* v_m_3596_, lean_object* v_a_3597_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_3596_, v_a_3597_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3599_, lean_object* v_m_3600_, lean_object* v_a_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(v_00_u03b2_3599_, v_m_3600_, v_a_3601_);
lean_dec(v_a_3601_);
lean_dec_ref(v_m_3600_);
return v_res_3602_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_3603_, lean_object* v_x_3604_, lean_object* v_x_3605_){
_start:
{
uint8_t v___x_3606_; 
v___x_3606_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_3604_, v_x_3605_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3607_, lean_object* v_x_3608_, lean_object* v_x_3609_){
_start:
{
uint8_t v_res_3610_; lean_object* v_r_3611_; 
v_res_3610_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(v_00_u03b2_3607_, v_x_3608_, v_x_3609_);
lean_dec_ref(v_x_3609_);
lean_dec_ref(v_x_3608_);
v_r_3611_ = lean_box(v_res_3610_);
return v_r_3611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_3612_, lean_object* v_a_3613_, lean_object* v_x_3614_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_3613_, v_x_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___boxed(lean_object* v_00_u03b2_3616_, lean_object* v_a_3617_, lean_object* v_x_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(v_00_u03b2_3616_, v_a_3617_, v_x_3618_);
lean_dec(v_x_3618_);
lean_dec(v_a_3617_);
return v_res_3619_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(lean_object* v_00_u03b2_3620_, lean_object* v_x_3621_, size_t v_x_3622_, lean_object* v_x_3623_){
_start:
{
uint8_t v___x_3624_; 
v___x_3624_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_3621_, v_x_3622_, v_x_3623_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3625_, lean_object* v_x_3626_, lean_object* v_x_3627_, lean_object* v_x_3628_){
_start:
{
size_t v_x_21872__boxed_3629_; uint8_t v_res_3630_; lean_object* v_r_3631_; 
v_x_21872__boxed_3629_ = lean_unbox_usize(v_x_3627_);
lean_dec(v_x_3627_);
v_res_3630_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(v_00_u03b2_3625_, v_x_3626_, v_x_21872__boxed_3629_, v_x_3628_);
lean_dec_ref(v_x_3628_);
lean_dec_ref(v_x_3626_);
v_r_3631_ = lean_box(v_res_3630_);
return v_r_3631_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(lean_object* v_00_u03b2_3632_, lean_object* v_keys_3633_, lean_object* v_vals_3634_, lean_object* v_heq_3635_, lean_object* v_i_3636_, lean_object* v_k_3637_){
_start:
{
uint8_t v___x_3638_; 
v___x_3638_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_3633_, v_i_3636_, v_k_3637_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___boxed(lean_object* v_00_u03b2_3639_, lean_object* v_keys_3640_, lean_object* v_vals_3641_, lean_object* v_heq_3642_, lean_object* v_i_3643_, lean_object* v_k_3644_){
_start:
{
uint8_t v_res_3645_; lean_object* v_r_3646_; 
v_res_3645_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(v_00_u03b2_3639_, v_keys_3640_, v_vals_3641_, v_heq_3642_, v_i_3643_, v_k_3644_);
lean_dec_ref(v_k_3644_);
lean_dec_ref(v_vals_3641_);
lean_dec_ref(v_keys_3640_);
v_r_3646_ = lean_box(v_res_3645_);
return v_r_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1(){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3654_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3655_ = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
v___x_3656_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3657_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElab___boxed), 4, 0);
v___x_3658_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3654_, v___x_3655_, v___x_3656_, v___x_3657_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___boxed(lean_object* v_a_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3(){
_start:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3687_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
v___x_3688_ = ((lean_object*)(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6));
v___x_3689_ = l_Lean_addBuiltinDeclarationRanges(v___x_3687_, v___x_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___boxed(lean_object* v_a_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
return v_res_3691_;
}
}
lean_object* runtime_initialize_Lean_Elab_MacroArgUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_AuxDef(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ElabRules(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
