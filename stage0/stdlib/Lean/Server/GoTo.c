// Lean compiler output
// Module: Lean.Server.GoTo
// Imports: public import Lean.Server.Utils public import Lean.Data.Lsp.Internal public import Lean.Util.CollectFVars public import Lean.Util.ForEachExpr meta import Lean.Parser.Module
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
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Info_toElabInfo_x3f(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* l_Lean_Server_documentUriFromModule_x3f(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
extern lean_object* l_Lean_builtinDeclRanges;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
extern lean_object* l_Lean_declRangeExt;
extern lean_object* l_Lean_instInhabitedDeclarationRanges_default;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_isAuxRecursor(lean_object*, lean_object*);
uint8_t l_Lean_isNoConfusion(lean_object*, lean_object*);
lean_object* l_Lean_DeclarationRange_toLspRange(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Elab_Info_range_x3f(lean_object*);
lean_object* l_Lean_Syntax_Range_toLspRange(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_errorExplanationExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_findInfo_x3f(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_isInstance___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_Elab_Info_lctx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_declaration_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_declaration_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_declaration_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_declaration_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_definition_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_definition_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_definition_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_definition_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_type_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_type_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_type_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_type_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_instBEqGoToKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_instBEqGoToKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_instBEqGoToKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_instBEqGoToKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instBEqGoToKind___closed__0 = (const lean_object*)&l_Lean_Server_instBEqGoToKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instBEqGoToKind = (const lean_object*)&l_Lean_Server_instBEqGoToKind___closed__0_value;
static const lean_string_object l_Lean_Server_instToJsonGoToKind_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean_Server_instToJsonGoToKind_toJson___closed__0 = (const lean_object*)&l_Lean_Server_instToJsonGoToKind_toJson___closed__0_value;
static const lean_ctor_object l_Lean_Server_instToJsonGoToKind_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Server_instToJsonGoToKind_toJson___closed__0_value)}};
static const lean_object* l_Lean_Server_instToJsonGoToKind_toJson___closed__1 = (const lean_object*)&l_Lean_Server_instToJsonGoToKind_toJson___closed__1_value;
static const lean_string_object l_Lean_Server_instToJsonGoToKind_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Server_instToJsonGoToKind_toJson___closed__2 = (const lean_object*)&l_Lean_Server_instToJsonGoToKind_toJson___closed__2_value;
static const lean_ctor_object l_Lean_Server_instToJsonGoToKind_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Server_instToJsonGoToKind_toJson___closed__2_value)}};
static const lean_object* l_Lean_Server_instToJsonGoToKind_toJson___closed__3 = (const lean_object*)&l_Lean_Server_instToJsonGoToKind_toJson___closed__3_value;
static const lean_string_object l_Lean_Server_instToJsonGoToKind_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l_Lean_Server_instToJsonGoToKind_toJson___closed__4 = (const lean_object*)&l_Lean_Server_instToJsonGoToKind_toJson___closed__4_value;
static const lean_ctor_object l_Lean_Server_instToJsonGoToKind_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Server_instToJsonGoToKind_toJson___closed__4_value)}};
static const lean_object* l_Lean_Server_instToJsonGoToKind_toJson___closed__5 = (const lean_object*)&l_Lean_Server_instToJsonGoToKind_toJson___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Server_instToJsonGoToKind_toJson(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_instToJsonGoToKind_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Server_instToJsonGoToKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_instToJsonGoToKind_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instToJsonGoToKind___closed__0 = (const lean_object*)&l_Lean_Server_instToJsonGoToKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instToJsonGoToKind = (const lean_object*)&l_Lean_Server_instToJsonGoToKind___closed__0_value;
static const lean_string_object l_Lean_Server_instFromJsonGoToKind_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no inductive tag found"};
static const lean_object* l_Lean_Server_instFromJsonGoToKind_fromJson___closed__0 = (const lean_object*)&l_Lean_Server_instFromJsonGoToKind_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Server_instFromJsonGoToKind_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_instFromJsonGoToKind_fromJson___closed__0_value)}};
static const lean_object* l_Lean_Server_instFromJsonGoToKind_fromJson___closed__1 = (const lean_object*)&l_Lean_Server_instFromJsonGoToKind_fromJson___closed__1_value;
static const lean_string_object l_Lean_Server_instFromJsonGoToKind_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "no inductive constructor matched"};
static const lean_object* l_Lean_Server_instFromJsonGoToKind_fromJson___closed__2 = (const lean_object*)&l_Lean_Server_instFromJsonGoToKind_fromJson___closed__2_value;
static const lean_ctor_object l_Lean_Server_instFromJsonGoToKind_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_instFromJsonGoToKind_fromJson___closed__2_value)}};
static const lean_object* l_Lean_Server_instFromJsonGoToKind_fromJson___closed__3 = (const lean_object*)&l_Lean_Server_instFromJsonGoToKind_fromJson___closed__3_value;
static const lean_ctor_object l_Lean_Server_instFromJsonGoToKind_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Server_instFromJsonGoToKind_fromJson___closed__4 = (const lean_object*)&l_Lean_Server_instFromJsonGoToKind_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Server_instFromJsonGoToKind_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_instFromJsonGoToKind_fromJson___closed__5 = (const lean_object*)&l_Lean_Server_instFromJsonGoToKind_fromJson___closed__5_value;
static const lean_ctor_object l_Lean_Server_instFromJsonGoToKind_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Server_instFromJsonGoToKind_fromJson___closed__6 = (const lean_object*)&l_Lean_Server_instFromJsonGoToKind_fromJson___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Server_instFromJsonGoToKind_fromJson(lean_object*);
static const lean_closure_object l_Lean_Server_instFromJsonGoToKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_instFromJsonGoToKind_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instFromJsonGoToKind___closed__0 = (const lean_object*)&l_Lean_Server_instFromJsonGoToKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instFromJsonGoToKind = (const lean_object*)&l_Lean_Server_instFromJsonGoToKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_determineTargetExprs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_determineTargetExprs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Server_GoToKind_determineTargetExprs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_GoToKind_determineTargetExprs___closed__0;
static lean_once_cell_t l_Lean_Server_GoToKind_determineTargetExprs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_GoToKind_determineTargetExprs___closed__1;
static const lean_closure_object l_Lean_Server_GoToKind_determineTargetExprs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_GoToKind_determineTargetExprs___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_GoToKind_determineTargetExprs___closed__2 = (const lean_object*)&l_Lean_Server_GoToKind_determineTargetExprs___closed__2_value;
static const lean_array_object l_Lean_Server_GoToKind_determineTargetExprs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_GoToKind_determineTargetExprs___closed__3 = (const lean_object*)&l_Lean_Server_GoToKind_determineTargetExprs___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_determineTargetExprs(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_determineTargetExprs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Server_getInstanceProjectionArg_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Server_getInstanceProjectionArg_x3f___closed__0;
static lean_once_cell_t l_Lean_Server_getInstanceProjectionArg_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_getInstanceProjectionArg_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_getInstanceProjectionArg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_getInstanceProjectionArg_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_isInstanceProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_isInstanceProjection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_isInstanceProjectionInfoFor(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_isInstanceProjectionInfoFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_locationLinksFromDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_locationLinksFromDecl___closed__0 = (const lean_object*)&l_Lean_Server_locationLinksFromDecl___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromBinder___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromBinder___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromBinder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_locationLinksFromImport___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Server_locationLinksFromImport___redArg___closed__0 = (const lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__0_value;
static const lean_string_object l_Lean_Server_locationLinksFromImport___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Server_locationLinksFromImport___redArg___closed__1 = (const lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__1_value;
static const lean_string_object l_Lean_Server_locationLinksFromImport___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Module"};
static const lean_object* l_Lean_Server_locationLinksFromImport___redArg___closed__2 = (const lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__2_value;
static const lean_string_object l_Lean_Server_locationLinksFromImport___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l_Lean_Server_locationLinksFromImport___redArg___closed__3 = (const lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Server_locationLinksFromImport___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_locationLinksFromImport___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_locationLinksFromImport___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Server_locationLinksFromImport___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__4_value_aux_2),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(177, 219, 158, 40, 50, 143, 61, 44)}};
static const lean_object* l_Lean_Server_locationLinksFromImport___redArg___closed__4 = (const lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Server_locationLinksFromImport___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_locationLinksFromImport___redArg___closed__5 = (const lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Server_locationLinksFromImport___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__5_value),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__5_value)}};
static const lean_object* l_Lean_Server_locationLinksFromImport___redArg___closed__6 = (const lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__6_value;
static const lean_string_object l_Lean_Server_locationLinksFromImport___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l_Lean_Server_locationLinksFromImport___redArg___closed__7 = (const lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Server_locationLinksFromImport___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_locationLinksFromImport___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__8_value_aux_0),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_locationLinksFromImport___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__8_value_aux_1),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Server_locationLinksFromImport___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__8_value_aux_2),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(107, 73, 92, 3, 207, 252, 164, 131)}};
static const lean_object* l_Lean_Server_locationLinksFromImport___redArg___closed__8 = (const lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__8_value;
static const lean_string_object l_Lean_Server_locationLinksFromImport___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_Server_locationLinksFromImport___redArg___closed__9 = (const lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Server_locationLinksFromImport___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_locationLinksFromImport___redArg___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__10_value_aux_0),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_locationLinksFromImport___redArg___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__10_value_aux_1),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Server_locationLinksFromImport___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__10_value_aux_2),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(89, 228, 64, 55, 26, 167, 248, 235)}};
static const lean_object* l_Lean_Server_locationLinksFromImport___redArg___closed__10 = (const lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__10_value;
static const lean_string_object l_Lean_Server_locationLinksFromImport___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l_Lean_Server_locationLinksFromImport___redArg___closed__11 = (const lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Server_locationLinksFromImport___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_locationLinksFromImport___redArg___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__12_value_aux_0),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_locationLinksFromImport___redArg___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__12_value_aux_1),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Server_locationLinksFromImport___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__12_value_aux_2),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(198, 166, 14, 39, 152, 190, 236, 172)}};
static const lean_object* l_Lean_Server_locationLinksFromImport___redArg___closed__12 = (const lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromImport___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromImport___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromImport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromImport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Delab"};
static const lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 78, 224, 2, 255, 4, 162, 217)}};
static const lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__3 = (const lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__4 = (const lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "elabApp"};
static const lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__5 = (const lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(18, 176, 207, 17, 163, 78, 118, 84)}};
static const lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6 = (const lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabIdent"};
static const lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__7 = (const lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_locationLinksFromImport___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(51, 171, 47, 134, 165, 146, 127, 3)}};
static const lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8 = (const lean_object*)&l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromErrorNameInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromErrorNameInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromInstanceProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromInstanceProjection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromTermInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromTermInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDelabTermInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDelabTermInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromFieldInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromFieldInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromOptionInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromOptionInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromCommandInfo___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromCommandInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromCommandInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromCommandInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Server_GoToKind_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Server_GoToKind_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_Server_GoToKind_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Server_GoToKind_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_Server_GoToKind_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_declaration_elim___redArg(lean_object* v_declaration_28_){
_start:
{
lean_inc(v_declaration_28_);
return v_declaration_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_declaration_elim___redArg___boxed(lean_object* v_declaration_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Server_GoToKind_declaration_elim___redArg(v_declaration_29_);
lean_dec(v_declaration_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_declaration_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_declaration_34_){
_start:
{
lean_inc(v_declaration_34_);
return v_declaration_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_declaration_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_declaration_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Server_GoToKind_declaration_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_declaration_38_);
lean_dec(v_declaration_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_definition_elim___redArg(lean_object* v_definition_41_){
_start:
{
lean_inc(v_definition_41_);
return v_definition_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_definition_elim___redArg___boxed(lean_object* v_definition_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Server_GoToKind_definition_elim___redArg(v_definition_42_);
lean_dec(v_definition_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_definition_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_definition_47_){
_start:
{
lean_inc(v_definition_47_);
return v_definition_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_definition_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_definition_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_Server_GoToKind_definition_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_definition_51_);
lean_dec(v_definition_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_type_elim___redArg(lean_object* v_type_54_){
_start:
{
lean_inc(v_type_54_);
return v_type_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_type_elim___redArg___boxed(lean_object* v_type_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Server_GoToKind_type_elim___redArg(v_type_55_);
lean_dec(v_type_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_type_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_type_60_){
_start:
{
lean_inc(v_type_60_);
return v_type_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_type_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_type_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Server_GoToKind_type_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_type_64_);
lean_dec(v_type_64_);
return v_res_66_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_instBEqGoToKind_beq(uint8_t v_x_67_, uint8_t v_y_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_69_ = l_Lean_Server_GoToKind_ctorIdx(v_x_67_);
v___x_70_ = l_Lean_Server_GoToKind_ctorIdx(v_y_68_);
v___x_71_ = lean_nat_dec_eq(v___x_69_, v___x_70_);
lean_dec(v___x_70_);
lean_dec(v___x_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instBEqGoToKind_beq___boxed(lean_object* v_x_72_, lean_object* v_y_73_){
_start:
{
uint8_t v_x_17__boxed_74_; uint8_t v_y_18__boxed_75_; uint8_t v_res_76_; lean_object* v_r_77_; 
v_x_17__boxed_74_ = lean_unbox(v_x_72_);
v_y_18__boxed_75_ = lean_unbox(v_y_73_);
v_res_76_ = l_Lean_Server_instBEqGoToKind_beq(v_x_17__boxed_74_, v_y_18__boxed_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instToJsonGoToKind_toJson(uint8_t v_x_89_){
_start:
{
switch(v_x_89_)
{
case 0:
{
lean_object* v___x_90_; 
v___x_90_ = ((lean_object*)(l_Lean_Server_instToJsonGoToKind_toJson___closed__1));
return v___x_90_;
}
case 1:
{
lean_object* v___x_91_; 
v___x_91_ = ((lean_object*)(l_Lean_Server_instToJsonGoToKind_toJson___closed__3));
return v___x_91_;
}
default: 
{
lean_object* v___x_92_; 
v___x_92_ = ((lean_object*)(l_Lean_Server_instToJsonGoToKind_toJson___closed__5));
return v___x_92_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instToJsonGoToKind_toJson___boxed(lean_object* v_x_93_){
_start:
{
uint8_t v_x_67__boxed_94_; lean_object* v_res_95_; 
v_x_67__boxed_94_ = lean_unbox(v_x_93_);
v_res_95_ = l_Lean_Server_instToJsonGoToKind_toJson(v_x_67__boxed_94_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instFromJsonGoToKind_fromJson(lean_object* v_json_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Json_getTag_x3f(v_json_113_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v___x_115_; 
v___x_115_ = ((lean_object*)(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__1));
return v___x_115_;
}
else
{
lean_object* v_val_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v_val_116_ = lean_ctor_get(v___x_114_, 0);
lean_inc(v_val_116_);
lean_dec_ref_known(v___x_114_, 1);
v___x_117_ = ((lean_object*)(l_Lean_Server_instToJsonGoToKind_toJson___closed__4));
v___x_118_ = lean_string_dec_eq(v_val_116_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = ((lean_object*)(l_Lean_Server_instToJsonGoToKind_toJson___closed__0));
v___x_120_ = lean_string_dec_eq(v_val_116_, v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = ((lean_object*)(l_Lean_Server_instToJsonGoToKind_toJson___closed__2));
v___x_122_ = lean_string_dec_eq(v_val_116_, v___x_121_);
lean_dec(v_val_116_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
v___x_123_ = ((lean_object*)(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__3));
return v___x_123_;
}
else
{
lean_object* v___x_124_; 
v___x_124_ = ((lean_object*)(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__4));
return v___x_124_;
}
}
else
{
lean_object* v___x_125_; 
lean_dec(v_val_116_);
v___x_125_ = ((lean_object*)(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__5));
return v___x_125_;
}
}
else
{
lean_object* v___x_126_; 
lean_dec(v_val_116_);
v___x_126_ = ((lean_object*)(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__6));
return v___x_126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(lean_object* v_e_129_, lean_object* v___y_130_){
_start:
{
uint8_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = l_Lean_Expr_hasMVar(v_e_129_);
v___x_133_ = lean_bool_not(v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v_mctx_135_; lean_object* v___x_136_; lean_object* v_fst_137_; lean_object* v_snd_138_; lean_object* v___x_139_; lean_object* v_cache_140_; lean_object* v_zetaDeltaFVarIds_141_; lean_object* v_postponed_142_; lean_object* v_diag_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_152_; 
v___x_134_ = lean_st_ref_get(v___y_130_);
v_mctx_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc_ref(v_mctx_135_);
lean_dec(v___x_134_);
v___x_136_ = l_Lean_instantiateMVarsCore(v_mctx_135_, v_e_129_);
v_fst_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_fst_137_);
v_snd_138_ = lean_ctor_get(v___x_136_, 1);
lean_inc(v_snd_138_);
lean_dec_ref(v___x_136_);
v___x_139_ = lean_st_ref_take(v___y_130_);
v_cache_140_ = lean_ctor_get(v___x_139_, 1);
v_zetaDeltaFVarIds_141_ = lean_ctor_get(v___x_139_, 2);
v_postponed_142_ = lean_ctor_get(v___x_139_, 3);
v_diag_143_ = lean_ctor_get(v___x_139_, 4);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_152_ == 0)
{
lean_object* v_unused_153_; 
v_unused_153_ = lean_ctor_get(v___x_139_, 0);
lean_dec(v_unused_153_);
v___x_145_ = v___x_139_;
v_isShared_146_ = v_isSharedCheck_152_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_diag_143_);
lean_inc(v_postponed_142_);
lean_inc(v_zetaDeltaFVarIds_141_);
lean_inc(v_cache_140_);
lean_dec(v___x_139_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_152_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v_snd_138_);
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_snd_138_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_cache_140_);
lean_ctor_set(v_reuseFailAlloc_151_, 2, v_zetaDeltaFVarIds_141_);
lean_ctor_set(v_reuseFailAlloc_151_, 3, v_postponed_142_);
lean_ctor_set(v_reuseFailAlloc_151_, 4, v_diag_143_);
v___x_148_ = v_reuseFailAlloc_151_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_st_ref_set(v___y_130_, v___x_148_);
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v_fst_137_);
return v___x_150_;
}
}
}
else
{
lean_object* v___x_154_; 
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v_e_129_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg___boxed(lean_object* v_e_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_e_155_, v___y_156_);
lean_dec(v___y_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0(lean_object* v_e_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_e_159_, v___y_161_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___boxed(lean_object* v_e_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0(v_e_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_determineTargetExprs___lam__0(lean_object* v_e_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_snd_181_; 
switch(lean_obj_tag(v_e_173_))
{
case 1:
{
lean_object* v___x_186_; 
v___x_186_ = lean_array_push(v___y_174_, v_e_173_);
v_snd_181_ = v___x_186_;
goto v___jp_180_;
}
case 4:
{
lean_object* v___x_187_; 
v___x_187_ = lean_array_push(v___y_174_, v_e_173_);
v_snd_181_ = v___x_187_;
goto v___jp_180_;
}
default: 
{
lean_dec_ref(v_e_173_);
v_snd_181_ = v___y_174_;
goto v___jp_180_;
}
}
v___jp_180_:
{
uint8_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_182_ = 1;
v___x_183_ = lean_box(v___x_182_);
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v_snd_181_);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_determineTargetExprs___lam__0___boxed(lean_object* v_e_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Server_GoToKind_determineTargetExprs___lam__0(v_e_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(lean_object* v_a_196_, lean_object* v_b_197_, lean_object* v_x_198_){
_start:
{
if (lean_obj_tag(v_x_198_) == 0)
{
lean_dec(v_b_197_);
lean_dec_ref(v_a_196_);
return v_x_198_;
}
else
{
lean_object* v_key_199_; lean_object* v_value_200_; lean_object* v_tail_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_213_; 
v_key_199_ = lean_ctor_get(v_x_198_, 0);
v_value_200_ = lean_ctor_get(v_x_198_, 1);
v_tail_201_ = lean_ctor_get(v_x_198_, 2);
v_isSharedCheck_213_ = !lean_is_exclusive(v_x_198_);
if (v_isSharedCheck_213_ == 0)
{
v___x_203_ = v_x_198_;
v_isShared_204_ = v_isSharedCheck_213_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_tail_201_);
lean_inc(v_value_200_);
lean_inc(v_key_199_);
lean_dec(v_x_198_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_213_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
uint8_t v___x_205_; 
v___x_205_ = lean_expr_eqv(v_key_199_, v_a_196_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_206_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(v_a_196_, v_b_197_, v_tail_201_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 2, v___x_206_);
v___x_208_ = v___x_203_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_key_199_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_value_200_);
lean_ctor_set(v_reuseFailAlloc_209_, 2, v___x_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
else
{
lean_object* v___x_211_; 
lean_dec(v_value_200_);
lean_dec(v_key_199_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v_b_197_);
lean_ctor_set(v___x_203_, 0, v_a_196_);
v___x_211_ = v___x_203_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_196_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_b_197_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_tail_201_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(lean_object* v_a_214_, lean_object* v_x_215_){
_start:
{
if (lean_obj_tag(v_x_215_) == 0)
{
uint8_t v___x_216_; 
v___x_216_ = 0;
return v___x_216_;
}
else
{
lean_object* v_key_217_; lean_object* v_tail_218_; uint8_t v___x_219_; 
v_key_217_ = lean_ctor_get(v_x_215_, 0);
v_tail_218_ = lean_ctor_get(v_x_215_, 2);
v___x_219_ = lean_expr_eqv(v_key_217_, v_a_214_);
if (v___x_219_ == 0)
{
v_x_215_ = v_tail_218_;
goto _start;
}
else
{
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_221_, lean_object* v_x_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(v_a_221_, v_x_222_);
lean_dec(v_x_222_);
lean_dec_ref(v_a_221_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
return v_x_225_;
}
else
{
lean_object* v_key_227_; lean_object* v_value_228_; lean_object* v_tail_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_252_; 
v_key_227_ = lean_ctor_get(v_x_226_, 0);
v_value_228_ = lean_ctor_get(v_x_226_, 1);
v_tail_229_ = lean_ctor_get(v_x_226_, 2);
v_isSharedCheck_252_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_252_ == 0)
{
v___x_231_ = v_x_226_;
v_isShared_232_ = v_isSharedCheck_252_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_tail_229_);
lean_inc(v_value_228_);
lean_inc(v_key_227_);
lean_dec(v_x_226_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_252_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; uint64_t v_fold_237_; uint64_t v___x_238_; uint64_t v___x_239_; uint64_t v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_233_ = lean_array_get_size(v_x_225_);
v___x_234_ = l_Lean_Expr_hash(v_key_227_);
v___x_235_ = 32ULL;
v___x_236_ = lean_uint64_shift_right(v___x_234_, v___x_235_);
v_fold_237_ = lean_uint64_xor(v___x_234_, v___x_236_);
v___x_238_ = 16ULL;
v___x_239_ = lean_uint64_shift_right(v_fold_237_, v___x_238_);
v___x_240_ = lean_uint64_xor(v_fold_237_, v___x_239_);
v___x_241_ = lean_uint64_to_usize(v___x_240_);
v___x_242_ = lean_usize_of_nat(v___x_233_);
v___x_243_ = ((size_t)1ULL);
v___x_244_ = lean_usize_sub(v___x_242_, v___x_243_);
v___x_245_ = lean_usize_land(v___x_241_, v___x_244_);
v___x_246_ = lean_array_uget_borrowed(v_x_225_, v___x_245_);
lean_inc(v___x_246_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 2, v___x_246_);
v___x_248_ = v___x_231_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_key_227_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_value_228_);
lean_ctor_set(v_reuseFailAlloc_251_, 2, v___x_246_);
v___x_248_ = v_reuseFailAlloc_251_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; 
v___x_249_ = lean_array_uset(v_x_225_, v___x_245_, v___x_248_);
v_x_225_ = v___x_249_;
v_x_226_ = v_tail_229_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6___redArg(lean_object* v_i_253_, lean_object* v_source_254_, lean_object* v_target_255_){
_start:
{
lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_256_ = lean_array_get_size(v_source_254_);
v___x_257_ = lean_nat_dec_lt(v_i_253_, v___x_256_);
if (v___x_257_ == 0)
{
lean_dec_ref(v_source_254_);
lean_dec(v_i_253_);
return v_target_255_;
}
else
{
lean_object* v_es_258_; lean_object* v___x_259_; lean_object* v_source_260_; lean_object* v_target_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_es_258_ = lean_array_fget(v_source_254_, v_i_253_);
v___x_259_ = lean_box(0);
v_source_260_ = lean_array_fset(v_source_254_, v_i_253_, v___x_259_);
v_target_261_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(v_target_255_, v_es_258_);
v___x_262_ = lean_unsigned_to_nat(1u);
v___x_263_ = lean_nat_add(v_i_253_, v___x_262_);
lean_dec(v_i_253_);
v_i_253_ = v___x_263_;
v_source_254_ = v_source_260_;
v_target_255_ = v_target_261_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5___redArg(lean_object* v_data_265_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v_nbuckets_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_266_ = lean_array_get_size(v_data_265_);
v___x_267_ = lean_unsigned_to_nat(2u);
v_nbuckets_268_ = lean_nat_mul(v___x_266_, v___x_267_);
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = lean_box(0);
v___x_271_ = lean_mk_array(v_nbuckets_268_, v___x_270_);
v___x_272_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6___redArg(v___x_269_, v_data_265_, v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2___redArg(lean_object* v_m_273_, lean_object* v_a_274_, lean_object* v_b_275_){
_start:
{
lean_object* v_size_276_; lean_object* v_buckets_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_320_; 
v_size_276_ = lean_ctor_get(v_m_273_, 0);
v_buckets_277_ = lean_ctor_get(v_m_273_, 1);
v_isSharedCheck_320_ = !lean_is_exclusive(v_m_273_);
if (v_isSharedCheck_320_ == 0)
{
v___x_279_ = v_m_273_;
v_isShared_280_ = v_isSharedCheck_320_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_buckets_277_);
lean_inc(v_size_276_);
lean_dec(v_m_273_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_320_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; uint64_t v___x_282_; uint64_t v___x_283_; uint64_t v___x_284_; uint64_t v_fold_285_; uint64_t v___x_286_; uint64_t v___x_287_; uint64_t v___x_288_; size_t v___x_289_; size_t v___x_290_; size_t v___x_291_; size_t v___x_292_; size_t v___x_293_; lean_object* v_bkt_294_; uint8_t v___x_295_; 
v___x_281_ = lean_array_get_size(v_buckets_277_);
v___x_282_ = l_Lean_Expr_hash(v_a_274_);
v___x_283_ = 32ULL;
v___x_284_ = lean_uint64_shift_right(v___x_282_, v___x_283_);
v_fold_285_ = lean_uint64_xor(v___x_282_, v___x_284_);
v___x_286_ = 16ULL;
v___x_287_ = lean_uint64_shift_right(v_fold_285_, v___x_286_);
v___x_288_ = lean_uint64_xor(v_fold_285_, v___x_287_);
v___x_289_ = lean_uint64_to_usize(v___x_288_);
v___x_290_ = lean_usize_of_nat(v___x_281_);
v___x_291_ = ((size_t)1ULL);
v___x_292_ = lean_usize_sub(v___x_290_, v___x_291_);
v___x_293_ = lean_usize_land(v___x_289_, v___x_292_);
v_bkt_294_ = lean_array_uget_borrowed(v_buckets_277_, v___x_293_);
v___x_295_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(v_a_274_, v_bkt_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v_size_x27_297_; lean_object* v___x_298_; lean_object* v_buckets_x27_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_296_ = lean_unsigned_to_nat(1u);
v_size_x27_297_ = lean_nat_add(v_size_276_, v___x_296_);
lean_dec(v_size_276_);
lean_inc(v_bkt_294_);
v___x_298_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_298_, 0, v_a_274_);
lean_ctor_set(v___x_298_, 1, v_b_275_);
lean_ctor_set(v___x_298_, 2, v_bkt_294_);
v_buckets_x27_299_ = lean_array_uset(v_buckets_277_, v___x_293_, v___x_298_);
v___x_300_ = lean_unsigned_to_nat(4u);
v___x_301_ = lean_nat_mul(v_size_x27_297_, v___x_300_);
v___x_302_ = lean_unsigned_to_nat(3u);
v___x_303_ = lean_nat_div(v___x_301_, v___x_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_array_get_size(v_buckets_x27_299_);
v___x_305_ = lean_nat_dec_le(v___x_303_, v___x_304_);
lean_dec(v___x_303_);
if (v___x_305_ == 0)
{
lean_object* v_val_306_; lean_object* v___x_308_; 
v_val_306_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5___redArg(v_buckets_x27_299_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 1, v_val_306_);
lean_ctor_set(v___x_279_, 0, v_size_x27_297_);
v___x_308_ = v___x_279_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_size_x27_297_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_val_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
else
{
lean_object* v___x_311_; 
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 1, v_buckets_x27_299_);
lean_ctor_set(v___x_279_, 0, v_size_x27_297_);
v___x_311_ = v___x_279_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_size_x27_297_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_buckets_x27_299_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
else
{
lean_object* v___x_313_; lean_object* v_buckets_x27_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
lean_inc(v_bkt_294_);
v___x_313_ = lean_box(0);
v_buckets_x27_314_ = lean_array_uset(v_buckets_277_, v___x_293_, v___x_313_);
v___x_315_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(v_a_274_, v_b_275_, v_bkt_294_);
v___x_316_ = lean_array_uset(v_buckets_x27_314_, v___x_293_, v___x_315_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 1, v___x_316_);
v___x_318_ = v___x_279_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_size_276_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(lean_object* v_a_321_, lean_object* v_x_322_){
_start:
{
if (lean_obj_tag(v_x_322_) == 0)
{
lean_object* v___x_323_; 
v___x_323_ = lean_box(0);
return v___x_323_;
}
else
{
lean_object* v_key_324_; lean_object* v_value_325_; lean_object* v_tail_326_; uint8_t v___x_327_; 
v_key_324_ = lean_ctor_get(v_x_322_, 0);
v_value_325_ = lean_ctor_get(v_x_322_, 1);
v_tail_326_ = lean_ctor_get(v_x_322_, 2);
v___x_327_ = lean_expr_eqv(v_key_324_, v_a_321_);
if (v___x_327_ == 0)
{
v_x_322_ = v_tail_326_;
goto _start;
}
else
{
lean_object* v___x_329_; 
lean_inc(v_value_325_);
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v_value_325_);
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_a_330_, lean_object* v_x_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(v_a_330_, v_x_331_);
lean_dec(v_x_331_);
lean_dec_ref(v_a_330_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(lean_object* v_m_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_buckets_335_; lean_object* v___x_336_; uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; uint64_t v_fold_340_; uint64_t v___x_341_; uint64_t v___x_342_; uint64_t v___x_343_; size_t v___x_344_; size_t v___x_345_; size_t v___x_346_; size_t v___x_347_; size_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_buckets_335_ = lean_ctor_get(v_m_333_, 1);
v___x_336_ = lean_array_get_size(v_buckets_335_);
v___x_337_ = l_Lean_Expr_hash(v_a_334_);
v___x_338_ = 32ULL;
v___x_339_ = lean_uint64_shift_right(v___x_337_, v___x_338_);
v_fold_340_ = lean_uint64_xor(v___x_337_, v___x_339_);
v___x_341_ = 16ULL;
v___x_342_ = lean_uint64_shift_right(v_fold_340_, v___x_341_);
v___x_343_ = lean_uint64_xor(v_fold_340_, v___x_342_);
v___x_344_ = lean_uint64_to_usize(v___x_343_);
v___x_345_ = lean_usize_of_nat(v___x_336_);
v___x_346_ = ((size_t)1ULL);
v___x_347_ = lean_usize_sub(v___x_345_, v___x_346_);
v___x_348_ = lean_usize_land(v___x_344_, v___x_347_);
v___x_349_ = lean_array_uget_borrowed(v_buckets_335_, v___x_348_);
v___x_350_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(v_a_334_, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg___boxed(lean_object* v_m_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(v_m_351_, v_a_352_);
lean_dec_ref(v_a_352_);
lean_dec_ref(v_m_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(lean_object* v_g_354_, lean_object* v_e_355_, lean_object* v_a_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_a_364_; lean_object* v_fst_365_; lean_object* v___y_371_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_st_ref_get(v_a_356_);
v___x_375_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(v___x_374_, v_e_355_);
lean_dec(v___x_374_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v___x_376_; 
lean_inc_ref(v_g_354_);
lean_inc(v___y_361_);
lean_inc_ref(v___y_360_);
lean_inc(v___y_359_);
lean_inc_ref(v___y_358_);
lean_inc_ref(v_e_355_);
v___x_376_ = lean_apply_7(v_g_354_, v_e_355_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, lean_box(0));
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v_fst_378_; lean_object* v_snd_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_424_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v___x_376_, 1);
v_fst_378_ = lean_ctor_get(v_a_377_, 0);
v_snd_379_ = lean_ctor_get(v_a_377_, 1);
v_isSharedCheck_424_ = !lean_is_exclusive(v_a_377_);
if (v_isSharedCheck_424_ == 0)
{
v___x_381_ = v_a_377_;
v_isShared_382_ = v_isSharedCheck_424_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_snd_379_);
lean_inc(v_fst_378_);
lean_dec(v_a_377_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_424_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v_d_384_; lean_object* v_b_385_; lean_object* v___y_386_; uint8_t v___x_391_; 
v___x_391_ = lean_unbox(v_fst_378_);
lean_dec(v_fst_378_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_394_; 
lean_dec_ref(v_g_354_);
v___x_392_ = lean_box(0);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_392_);
v___x_394_ = v___x_381_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_snd_379_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
v_a_364_ = v___x_394_;
v_fst_365_ = v___x_392_;
goto v___jp_363_;
}
}
else
{
switch(lean_obj_tag(v_e_355_))
{
case 7:
{
lean_object* v_binderType_396_; lean_object* v_body_397_; 
lean_del_object(v___x_381_);
v_binderType_396_ = lean_ctor_get(v_e_355_, 1);
v_body_397_ = lean_ctor_get(v_e_355_, 2);
lean_inc_ref(v_body_397_);
lean_inc_ref(v_binderType_396_);
v_d_384_ = v_binderType_396_;
v_b_385_ = v_body_397_;
v___y_386_ = v_a_356_;
goto v___jp_383_;
}
case 6:
{
lean_object* v_binderType_398_; lean_object* v_body_399_; 
lean_del_object(v___x_381_);
v_binderType_398_ = lean_ctor_get(v_e_355_, 1);
v_body_399_ = lean_ctor_get(v_e_355_, 2);
lean_inc_ref(v_body_399_);
lean_inc_ref(v_binderType_398_);
v_d_384_ = v_binderType_398_;
v_b_385_ = v_body_399_;
v___y_386_ = v_a_356_;
goto v___jp_383_;
}
case 8:
{
lean_object* v_type_400_; lean_object* v_value_401_; lean_object* v_body_402_; lean_object* v___x_403_; 
lean_del_object(v___x_381_);
v_type_400_ = lean_ctor_get(v_e_355_, 1);
v_value_401_ = lean_ctor_get(v_e_355_, 2);
v_body_402_ = lean_ctor_get(v_e_355_, 3);
lean_inc_ref(v_type_400_);
lean_inc_ref(v_g_354_);
v___x_403_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_354_, v_type_400_, v_a_356_, v_snd_379_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v_snd_405_; lean_object* v___x_406_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
lean_dec_ref_known(v___x_403_, 1);
v_snd_405_ = lean_ctor_get(v_a_404_, 1);
lean_inc(v_snd_405_);
lean_dec(v_a_404_);
lean_inc_ref(v_value_401_);
lean_inc_ref(v_g_354_);
v___x_406_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_354_, v_value_401_, v_a_356_, v_snd_405_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v_snd_408_; lean_object* v___x_409_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
v_snd_408_ = lean_ctor_get(v_a_407_, 1);
lean_inc(v_snd_408_);
lean_dec(v_a_407_);
lean_inc_ref(v_body_402_);
v___x_409_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_354_, v_body_402_, v_a_356_, v_snd_408_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
v___y_371_ = v___x_409_;
goto v___jp_370_;
}
else
{
lean_dec_ref(v_g_354_);
v___y_371_ = v___x_406_;
goto v___jp_370_;
}
}
else
{
lean_dec_ref(v_g_354_);
v___y_371_ = v___x_403_;
goto v___jp_370_;
}
}
case 5:
{
lean_object* v_fn_410_; lean_object* v_arg_411_; lean_object* v___x_412_; 
lean_del_object(v___x_381_);
v_fn_410_ = lean_ctor_get(v_e_355_, 0);
v_arg_411_ = lean_ctor_get(v_e_355_, 1);
lean_inc_ref(v_fn_410_);
lean_inc_ref(v_g_354_);
v___x_412_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_354_, v_fn_410_, v_a_356_, v_snd_379_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v_snd_414_; lean_object* v___x_415_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v_snd_414_ = lean_ctor_get(v_a_413_, 1);
lean_inc(v_snd_414_);
lean_dec(v_a_413_);
lean_inc_ref(v_arg_411_);
v___x_415_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_354_, v_arg_411_, v_a_356_, v_snd_414_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
v___y_371_ = v___x_415_;
goto v___jp_370_;
}
else
{
lean_dec_ref(v_g_354_);
v___y_371_ = v___x_412_;
goto v___jp_370_;
}
}
case 10:
{
lean_object* v_expr_416_; lean_object* v___x_417_; 
lean_del_object(v___x_381_);
v_expr_416_ = lean_ctor_get(v_e_355_, 1);
lean_inc_ref(v_expr_416_);
v___x_417_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_354_, v_expr_416_, v_a_356_, v_snd_379_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
v___y_371_ = v___x_417_;
goto v___jp_370_;
}
case 11:
{
lean_object* v_struct_418_; lean_object* v___x_419_; 
lean_del_object(v___x_381_);
v_struct_418_ = lean_ctor_get(v_e_355_, 2);
lean_inc_ref(v_struct_418_);
v___x_419_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_354_, v_struct_418_, v_a_356_, v_snd_379_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
v___y_371_ = v___x_419_;
goto v___jp_370_;
}
default: 
{
lean_object* v___x_420_; lean_object* v___x_422_; 
lean_dec_ref(v_g_354_);
v___x_420_ = lean_box(0);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_420_);
v___x_422_ = v___x_381_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_snd_379_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
v_a_364_ = v___x_422_;
v_fst_365_ = v___x_420_;
goto v___jp_363_;
}
}
}
}
v___jp_383_:
{
lean_object* v___x_387_; 
lean_inc_ref(v_g_354_);
v___x_387_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_354_, v_d_384_, v___y_386_, v_snd_379_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v_snd_389_; lean_object* v___x_390_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref_known(v___x_387_, 1);
v_snd_389_ = lean_ctor_get(v_a_388_, 1);
lean_inc(v_snd_389_);
lean_dec(v_a_388_);
v___x_390_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_354_, v_b_385_, v___y_386_, v_snd_389_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
v___y_371_ = v___x_390_;
goto v___jp_370_;
}
else
{
lean_dec_ref(v_b_385_);
lean_dec_ref(v_g_354_);
v___y_371_ = v___x_387_;
goto v___jp_370_;
}
}
}
}
else
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec_ref(v_e_355_);
lean_dec_ref(v_g_354_);
v_a_425_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_376_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_376_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
else
{
lean_object* v_val_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_441_; 
lean_dec_ref(v_e_355_);
lean_dec_ref(v_g_354_);
v_val_433_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_441_ == 0)
{
v___x_435_ = v___x_375_;
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_val_433_);
lean_dec(v___x_375_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_437_, 0, v_val_433_);
lean_ctor_set(v___x_437_, 1, v___y_357_);
if (v_isShared_436_ == 0)
{
lean_ctor_set_tag(v___x_435_, 0);
lean_ctor_set(v___x_435_, 0, v___x_437_);
v___x_439_ = v___x_435_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
v___jp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_366_ = lean_st_ref_take(v_a_356_);
v___x_367_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2___redArg(v___x_366_, v_e_355_, v_fst_365_);
v___x_368_ = lean_st_ref_set(v_a_356_, v___x_367_);
v___x_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_369_, 0, v_a_364_);
return v___x_369_;
}
v___jp_370_:
{
if (lean_obj_tag(v___y_371_) == 0)
{
lean_object* v_a_372_; lean_object* v_fst_373_; 
v_a_372_ = lean_ctor_get(v___y_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___y_371_, 1);
v_fst_373_ = lean_ctor_get(v_a_372_, 0);
lean_inc(v_fst_373_);
v_a_364_ = v_a_372_;
v_fst_365_ = v_fst_373_;
goto v___jp_363_;
}
else
{
lean_dec_ref(v_e_355_);
return v___y_371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1___boxed(lean_object* v_g_442_, lean_object* v_e_443_, lean_object* v_a_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_442_, v_e_443_, v_a_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v_a_444_);
return v_res_451_;
}
}
static lean_object* _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__0(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_box(0);
v___x_453_ = lean_unsigned_to_nat(16u);
v___x_454_ = lean_mk_array(v___x_453_, v___x_452_);
return v___x_454_;
}
}
static lean_object* _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__1(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_455_ = lean_obj_once(&l_Lean_Server_GoToKind_determineTargetExprs___closed__0, &l_Lean_Server_GoToKind_determineTargetExprs___closed__0_once, _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__0);
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_455_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_determineTargetExprs(uint8_t v_kind_461_, lean_object* v_ti_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
if (v_kind_461_ == 2)
{
lean_object* v_expr_468_; lean_object* v___x_469_; 
v_expr_468_ = lean_ctor_get(v_ti_462_, 3);
lean_inc_ref(v_expr_468_);
lean_dec_ref(v_ti_462_);
lean_inc(v_a_466_);
lean_inc_ref(v_a_465_);
lean_inc(v_a_464_);
lean_inc_ref(v_a_463_);
v___x_469_ = lean_infer_type(v_expr_468_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; lean_object* v_a_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___f_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_469_, 1);
v___x_471_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_a_470_, v_a_464_);
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref(v___x_471_);
v___x_473_ = lean_obj_once(&l_Lean_Server_GoToKind_determineTargetExprs___closed__1, &l_Lean_Server_GoToKind_determineTargetExprs___closed__1_once, _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__1);
v___x_474_ = lean_st_mk_ref(v___x_473_);
v___f_475_ = ((lean_object*)(l_Lean_Server_GoToKind_determineTargetExprs___closed__2));
v___x_476_ = ((lean_object*)(l_Lean_Server_GoToKind_determineTargetExprs___closed__3));
v___x_477_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v___f_475_, v_a_472_, v___x_474_, v___x_476_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_487_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_487_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_487_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_487_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v_snd_482_; lean_object* v___x_483_; lean_object* v___x_485_; 
v_snd_482_ = lean_ctor_get(v_a_478_, 1);
lean_inc(v_snd_482_);
lean_dec(v_a_478_);
v___x_483_ = lean_st_ref_get(v___x_474_);
lean_dec(v___x_474_);
lean_dec(v___x_483_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v_snd_482_);
v___x_485_ = v___x_480_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_snd_482_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec(v___x_474_);
v_a_488_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_477_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_477_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
v_a_496_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_469_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_469_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
else
{
lean_object* v_expr_504_; lean_object* v___x_505_; lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_516_; 
v_expr_504_ = lean_ctor_get(v_ti_462_, 3);
lean_inc_ref(v_expr_504_);
lean_dec_ref(v_ti_462_);
v___x_505_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_expr_504_, v_a_464_);
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_516_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = lean_mk_empty_array_with_capacity(v___x_510_);
v___x_512_ = lean_array_push(v___x_511_, v_a_506_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_512_);
v___x_514_ = v___x_508_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_determineTargetExprs___boxed(lean_object* v_kind_517_, lean_object* v_ti_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
uint8_t v_kind_boxed_524_; lean_object* v_res_525_; 
v_kind_boxed_524_ = lean_unbox(v_kind_517_);
v_res_525_ = l_Lean_Server_GoToKind_determineTargetExprs(v_kind_boxed_524_, v_ti_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1(lean_object* v_00_u03b2_526_, lean_object* v_m_527_, lean_object* v_a_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(v_m_527_, v_a_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___boxed(lean_object* v_00_u03b2_530_, lean_object* v_m_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1(v_00_u03b2_530_, v_m_531_, v_a_532_);
lean_dec_ref(v_a_532_);
lean_dec_ref(v_m_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2(lean_object* v_00_u03b2_534_, lean_object* v_m_535_, lean_object* v_a_536_, lean_object* v_b_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2___redArg(v_m_535_, v_a_536_, v_b_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_539_, lean_object* v_a_540_, lean_object* v_x_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(v_a_540_, v_x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_543_, lean_object* v_a_544_, lean_object* v_x_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2(v_00_u03b2_543_, v_a_544_, v_x_545_);
lean_dec(v_x_545_);
lean_dec_ref(v_a_544_);
return v_res_546_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_547_, lean_object* v_a_548_, lean_object* v_x_549_){
_start:
{
uint8_t v___x_550_; 
v___x_550_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(v_a_548_, v_x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_551_, lean_object* v_a_552_, lean_object* v_x_553_){
_start:
{
uint8_t v_res_554_; lean_object* v_r_555_; 
v_res_554_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4(v_00_u03b2_551_, v_a_552_, v_x_553_);
lean_dec(v_x_553_);
lean_dec_ref(v_a_552_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_556_, lean_object* v_data_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5___redArg(v_data_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_559_, lean_object* v_a_560_, lean_object* v_b_561_, lean_object* v_x_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(v_a_560_, v_b_561_, v_x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_564_, lean_object* v_i_565_, lean_object* v_source_566_, lean_object* v_target_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6___redArg(v_i_565_, v_source_566_, v_target_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_569_, lean_object* v_x_570_, lean_object* v_x_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(v_x_570_, v_x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(lean_object* v_e_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_st_ref_get(v_a_577_);
v___x_580_ = l_Lean_Expr_getAppFn_x27(v_e_573_);
if (lean_obj_tag(v___x_580_) == 4)
{
lean_object* v_declName_581_; lean_object* v_env_582_; lean_object* v___x_583_; 
v_declName_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_declName_581_);
lean_dec_ref_known(v___x_580_, 2);
v_env_582_ = lean_ctor_get(v___x_579_, 0);
lean_inc_ref(v_env_582_);
lean_dec(v___x_579_);
v___x_583_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_582_, v_declName_581_);
if (lean_obj_tag(v___x_583_) == 1)
{
lean_object* v_val_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_593_; 
v_val_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_593_ == 0)
{
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_593_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_val_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_593_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v_e_573_);
lean_ctor_set(v___x_588_, 1, v_val_584_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_588_);
v___x_590_ = v___x_586_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_592_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; 
v___x_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
return v___x_591_;
}
}
}
else
{
uint8_t v___x_594_; lean_object* v___x_595_; 
lean_dec(v___x_583_);
v___x_594_ = 0;
v___x_595_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_573_, v___x_594_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_606_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_606_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_606_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_606_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
if (lean_obj_tag(v_a_596_) == 1)
{
lean_object* v_val_600_; 
lean_del_object(v___x_598_);
v_val_600_ = lean_ctor_get(v_a_596_, 0);
lean_inc(v_val_600_);
lean_dec_ref_known(v_a_596_, 1);
v_e_573_ = v_val_600_;
goto _start;
}
else
{
lean_object* v___x_602_; lean_object* v___x_604_; 
lean_dec(v_a_596_);
v___x_602_ = lean_box(0);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_602_);
v___x_604_ = v___x_598_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
v_a_607_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_595_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_595_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; 
lean_dec_ref(v___x_580_);
lean_dec(v___x_579_);
lean_dec_ref(v_e_573_);
v___x_615_ = lean_box(0);
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
return v___x_616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f___boxed(lean_object* v_e_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(v_e_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
return v_res_623_;
}
}
static uint64_t _init_l_Lean_Server_getInstanceProjectionArg_x3f___closed__0(void){
_start:
{
uint8_t v___x_624_; uint64_t v___x_625_; 
v___x_624_ = 2;
v___x_625_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_624_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_Server_getInstanceProjectionArg_x3f___closed__1(void){
_start:
{
lean_object* v___x_626_; lean_object* v_dummy_627_; 
v___x_626_ = lean_box(0);
v_dummy_627_ = l_Lean_Expr_sort___override(v___x_626_);
return v_dummy_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_getInstanceProjectionArg_x3f(lean_object* v_e_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v___x_634_; uint8_t v_foApprox_635_; uint8_t v_ctxApprox_636_; uint8_t v_quasiPatternApprox_637_; uint8_t v_constApprox_638_; uint8_t v_isDefEqStuckEx_639_; uint8_t v_unificationHints_640_; uint8_t v_proofIrrelevance_641_; uint8_t v_assignSyntheticOpaque_642_; uint8_t v_offsetCnstrs_643_; uint8_t v_etaStruct_644_; uint8_t v_univApprox_645_; uint8_t v_iota_646_; uint8_t v_beta_647_; uint8_t v_proj_648_; uint8_t v_zeta_649_; uint8_t v_zetaDelta_650_; uint8_t v_zetaUnused_651_; uint8_t v_zetaHave_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_723_; 
v___x_634_ = l_Lean_Meta_Context_config(v_a_629_);
v_foApprox_635_ = lean_ctor_get_uint8(v___x_634_, 0);
v_ctxApprox_636_ = lean_ctor_get_uint8(v___x_634_, 1);
v_quasiPatternApprox_637_ = lean_ctor_get_uint8(v___x_634_, 2);
v_constApprox_638_ = lean_ctor_get_uint8(v___x_634_, 3);
v_isDefEqStuckEx_639_ = lean_ctor_get_uint8(v___x_634_, 4);
v_unificationHints_640_ = lean_ctor_get_uint8(v___x_634_, 5);
v_proofIrrelevance_641_ = lean_ctor_get_uint8(v___x_634_, 6);
v_assignSyntheticOpaque_642_ = lean_ctor_get_uint8(v___x_634_, 7);
v_offsetCnstrs_643_ = lean_ctor_get_uint8(v___x_634_, 8);
v_etaStruct_644_ = lean_ctor_get_uint8(v___x_634_, 10);
v_univApprox_645_ = lean_ctor_get_uint8(v___x_634_, 11);
v_iota_646_ = lean_ctor_get_uint8(v___x_634_, 12);
v_beta_647_ = lean_ctor_get_uint8(v___x_634_, 13);
v_proj_648_ = lean_ctor_get_uint8(v___x_634_, 14);
v_zeta_649_ = lean_ctor_get_uint8(v___x_634_, 15);
v_zetaDelta_650_ = lean_ctor_get_uint8(v___x_634_, 16);
v_zetaUnused_651_ = lean_ctor_get_uint8(v___x_634_, 17);
v_zetaHave_652_ = lean_ctor_get_uint8(v___x_634_, 18);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_723_ == 0)
{
v___x_654_ = v___x_634_;
v_isShared_655_ = v_isSharedCheck_723_;
goto v_resetjp_653_;
}
else
{
lean_dec(v___x_634_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_723_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
uint8_t v_trackZetaDelta_656_; lean_object* v_zetaDeltaSet_657_; lean_object* v_lctx_658_; lean_object* v_localInstances_659_; lean_object* v_defEqCtx_x3f_660_; lean_object* v_synthPendingDepth_661_; lean_object* v_canUnfold_x3f_662_; uint8_t v_univApprox_663_; uint8_t v_inTypeClassResolution_664_; uint8_t v_cacheInferType_665_; uint8_t v___x_666_; lean_object* v_config_668_; 
v_trackZetaDelta_656_ = lean_ctor_get_uint8(v_a_629_, sizeof(void*)*7);
v_zetaDeltaSet_657_ = lean_ctor_get(v_a_629_, 1);
v_lctx_658_ = lean_ctor_get(v_a_629_, 2);
v_localInstances_659_ = lean_ctor_get(v_a_629_, 3);
v_defEqCtx_x3f_660_ = lean_ctor_get(v_a_629_, 4);
v_synthPendingDepth_661_ = lean_ctor_get(v_a_629_, 5);
v_canUnfold_x3f_662_ = lean_ctor_get(v_a_629_, 6);
v_univApprox_663_ = lean_ctor_get_uint8(v_a_629_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_664_ = lean_ctor_get_uint8(v_a_629_, sizeof(void*)*7 + 2);
v_cacheInferType_665_ = lean_ctor_get_uint8(v_a_629_, sizeof(void*)*7 + 3);
v___x_666_ = 2;
if (v_isShared_655_ == 0)
{
v_config_668_ = v___x_654_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, 0, v_foApprox_635_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, 1, v_ctxApprox_636_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, 2, v_quasiPatternApprox_637_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, 3, v_constApprox_638_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, 4, v_isDefEqStuckEx_639_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, 5, v_unificationHints_640_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, 6, v_proofIrrelevance_641_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, 7, v_assignSyntheticOpaque_642_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, 8, v_offsetCnstrs_643_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, 10, v_etaStruct_644_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, 11, v_univApprox_645_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, 12, v_iota_646_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, 13, v_beta_647_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, 14, v_proj_648_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, 15, v_zeta_649_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, 16, v_zetaDelta_650_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, 17, v_zetaUnused_651_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, 18, v_zetaHave_652_);
v_config_668_ = v_reuseFailAlloc_722_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
uint64_t v___x_669_; uint64_t v___x_670_; uint64_t v___x_671_; uint64_t v___x_672_; uint64_t v___x_673_; uint64_t v_key_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_ctor_set_uint8(v_config_668_, 9, v___x_666_);
v___x_669_ = l_Lean_Meta_Context_configKey(v_a_629_);
v___x_670_ = 3ULL;
v___x_671_ = lean_uint64_shift_right(v___x_669_, v___x_670_);
v___x_672_ = lean_uint64_shift_left(v___x_671_, v___x_670_);
v___x_673_ = lean_uint64_once(&l_Lean_Server_getInstanceProjectionArg_x3f___closed__0, &l_Lean_Server_getInstanceProjectionArg_x3f___closed__0_once, _init_l_Lean_Server_getInstanceProjectionArg_x3f___closed__0);
v_key_674_ = lean_uint64_lor(v___x_672_, v___x_673_);
v___x_675_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_675_, 0, v_config_668_);
lean_ctor_set_uint64(v___x_675_, sizeof(void*)*1, v_key_674_);
lean_inc(v_canUnfold_x3f_662_);
lean_inc(v_synthPendingDepth_661_);
lean_inc(v_defEqCtx_x3f_660_);
lean_inc_ref(v_localInstances_659_);
lean_inc_ref(v_lctx_658_);
lean_inc(v_zetaDeltaSet_657_);
v___x_676_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v_zetaDeltaSet_657_);
lean_ctor_set(v___x_676_, 2, v_lctx_658_);
lean_ctor_set(v___x_676_, 3, v_localInstances_659_);
lean_ctor_set(v___x_676_, 4, v_defEqCtx_x3f_660_);
lean_ctor_set(v___x_676_, 5, v_synthPendingDepth_661_);
lean_ctor_set(v___x_676_, 6, v_canUnfold_x3f_662_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*7, v_trackZetaDelta_656_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*7 + 1, v_univApprox_663_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*7 + 2, v_inTypeClassResolution_664_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*7 + 3, v_cacheInferType_665_);
v___x_677_ = l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(v_e_628_, v___x_676_, v_a_630_, v_a_631_, v_a_632_);
lean_dec_ref_known(v___x_676_, 7);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_713_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_713_ == 0)
{
v___x_680_ = v___x_677_;
v_isShared_681_ = v_isSharedCheck_713_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_713_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
if (lean_obj_tag(v_a_678_) == 1)
{
lean_object* v_val_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_708_; 
v_val_682_ = lean_ctor_get(v_a_678_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v_a_678_);
if (v_isSharedCheck_708_ == 0)
{
v___x_684_ = v_a_678_;
v_isShared_685_ = v_isSharedCheck_708_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_val_682_);
lean_dec(v_a_678_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_708_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v_snd_686_; lean_object* v_fst_687_; lean_object* v_numParams_688_; lean_object* v_dummy_689_; lean_object* v_nargs_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v_snd_686_ = lean_ctor_get(v_val_682_, 1);
lean_inc(v_snd_686_);
v_fst_687_ = lean_ctor_get(v_val_682_, 0);
lean_inc(v_fst_687_);
lean_dec(v_val_682_);
v_numParams_688_ = lean_ctor_get(v_snd_686_, 1);
lean_inc(v_numParams_688_);
lean_dec(v_snd_686_);
v_dummy_689_ = lean_obj_once(&l_Lean_Server_getInstanceProjectionArg_x3f___closed__1, &l_Lean_Server_getInstanceProjectionArg_x3f___closed__1_once, _init_l_Lean_Server_getInstanceProjectionArg_x3f___closed__1);
v_nargs_690_ = l_Lean_Expr_getAppNumArgs(v_fst_687_);
lean_inc(v_nargs_690_);
v___x_691_ = lean_mk_array(v_nargs_690_, v_dummy_689_);
v___x_692_ = lean_unsigned_to_nat(1u);
v___x_693_ = lean_nat_sub(v_nargs_690_, v___x_692_);
lean_dec(v_nargs_690_);
v___x_694_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_687_, v___x_691_, v___x_693_);
v___x_695_ = lean_array_get_size(v___x_694_);
v___x_696_ = lean_nat_dec_lt(v_numParams_688_, v___x_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_699_; 
lean_dec_ref(v___x_694_);
lean_dec(v_numParams_688_);
lean_del_object(v___x_684_);
v___x_697_ = lean_box(0);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_697_);
v___x_699_ = v___x_680_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
else
{
lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_701_ = lean_array_fget(v___x_694_, v_numParams_688_);
lean_dec(v_numParams_688_);
lean_dec_ref(v___x_694_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_701_);
v___x_703_ = v___x_684_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_707_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_705_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_703_);
v___x_705_ = v___x_680_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
else
{
lean_object* v___x_709_; lean_object* v___x_711_; 
lean_dec(v_a_678_);
v___x_709_ = lean_box(0);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_709_);
v___x_711_ = v___x_680_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
v_a_714_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_677_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_677_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_getInstanceProjectionArg_x3f___boxed(lean_object* v_e_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Server_getInstanceProjectionArg_x3f(v_e_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
lean_dec(v_a_728_);
lean_dec_ref(v_a_727_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isInstanceProjection(lean_object* v_e_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Server_getInstanceProjectionArg_x3f(v_e_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_752_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_752_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_752_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_752_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
if (lean_obj_tag(v_a_738_) == 0)
{
uint8_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_742_ = 0;
v___x_743_ = lean_box(v___x_742_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_743_);
v___x_745_ = v___x_740_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
else
{
uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
lean_dec_ref_known(v_a_738_, 1);
v___x_747_ = 1;
v___x_748_ = lean_box(v___x_747_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_748_);
v___x_750_ = v___x_740_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
v_a_753_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_737_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_737_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isInstanceProjection___boxed(lean_object* v_e_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_Server_isInstanceProjection(v_e_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isInstanceProjectionInfoFor(uint8_t v_kind_768_, lean_object* v_ti1_769_, lean_object* v_ti2_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
uint8_t v___x_776_; uint8_t v___x_777_; 
v___x_776_ = 2;
v___x_777_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_768_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v_toElabInfo_778_; lean_object* v_expr_779_; lean_object* v_stx_780_; uint8_t v___x_781_; lean_object* v___x_782_; 
v_toElabInfo_778_ = lean_ctor_get(v_ti1_769_, 0);
lean_inc_ref(v_toElabInfo_778_);
v_expr_779_ = lean_ctor_get(v_ti1_769_, 3);
lean_inc_ref(v_expr_779_);
lean_dec_ref(v_ti1_769_);
v_stx_780_ = lean_ctor_get(v_toElabInfo_778_, 1);
lean_inc(v_stx_780_);
lean_dec_ref(v_toElabInfo_778_);
v___x_781_ = 1;
v___x_782_ = l_Lean_Syntax_getPos_x3f(v_stx_780_, v___x_781_);
lean_dec(v_stx_780_);
if (lean_obj_tag(v___x_782_) == 1)
{
lean_object* v_toElabInfo_783_; lean_object* v_val_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_836_; 
v_toElabInfo_783_ = lean_ctor_get(v_ti2_770_, 0);
lean_inc_ref(v_toElabInfo_783_);
v_val_784_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_836_ == 0)
{
v___x_786_ = v___x_782_;
v_isShared_787_ = v_isSharedCheck_836_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_val_784_);
lean_dec(v___x_782_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_836_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v_expr_788_; lean_object* v_stx_789_; lean_object* v___x_790_; 
v_expr_788_ = lean_ctor_get(v_ti2_770_, 3);
lean_inc_ref(v_expr_788_);
lean_dec_ref(v_ti2_770_);
v_stx_789_ = lean_ctor_get(v_toElabInfo_783_, 1);
lean_inc(v_stx_789_);
lean_dec_ref(v_toElabInfo_783_);
v___x_790_ = l_Lean_Syntax_getPos_x3f(v_stx_789_, v___x_781_);
lean_dec(v_stx_789_);
if (lean_obj_tag(v___x_790_) == 1)
{
lean_object* v_val_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_831_; 
lean_del_object(v___x_786_);
v_val_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_831_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_831_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_val_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_831_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
uint8_t v___x_795_; uint8_t v___x_796_; 
v___x_795_ = lean_nat_dec_eq(v_val_784_, v_val_791_);
lean_dec(v_val_791_);
lean_dec(v_val_784_);
v___x_796_ = lean_bool_not(v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v_a_798_; lean_object* v___x_799_; lean_object* v_a_800_; lean_object* v___x_801_; 
lean_del_object(v___x_793_);
v___x_797_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_expr_779_, v_a_772_);
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc_n(v_a_798_, 2);
lean_dec_ref(v___x_797_);
v___x_799_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_expr_788_, v_a_772_);
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref(v___x_799_);
v___x_801_ = l_Lean_Server_isInstanceProjection(v_a_798_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_803_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref_known(v___x_801_, 1);
lean_inc(v_a_800_);
v___x_803_ = l_Lean_Server_isInstanceProjection(v_a_800_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_826_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_826_ == 0)
{
v___x_806_ = v___x_803_;
v_isShared_807_ = v_isSharedCheck_826_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_803_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_826_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
uint8_t v___x_808_; uint8_t v___x_809_; 
v___x_808_ = lean_unbox(v_a_802_);
lean_dec(v_a_802_);
v___x_809_ = lean_bool_not(v___x_808_);
if (v___x_809_ == 0)
{
uint8_t v___x_810_; 
v___x_810_ = lean_unbox(v_a_804_);
lean_dec(v_a_804_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; uint8_t v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_811_ = l_Lean_Expr_getAppFn_x27(v_a_798_);
lean_dec(v_a_798_);
v___x_812_ = l_Lean_Expr_getAppFn_x27(v_a_800_);
lean_dec(v_a_800_);
v___x_813_ = lean_expr_eqv(v___x_811_, v___x_812_);
lean_dec_ref(v___x_812_);
lean_dec_ref(v___x_811_);
v___x_814_ = lean_box(v___x_813_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_814_);
v___x_816_ = v___x_806_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
else
{
lean_object* v___x_818_; lean_object* v___x_820_; 
lean_dec(v_a_800_);
lean_dec(v_a_798_);
v___x_818_ = lean_box(v___x_796_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_818_);
v___x_820_ = v___x_806_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
else
{
lean_object* v___x_822_; lean_object* v___x_824_; 
lean_dec(v_a_804_);
lean_dec(v_a_800_);
lean_dec(v_a_798_);
v___x_822_ = lean_box(v___x_796_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_822_);
v___x_824_ = v___x_806_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_dec(v_a_802_);
lean_dec(v_a_800_);
lean_dec(v_a_798_);
return v___x_803_;
}
}
else
{
lean_dec(v_a_800_);
lean_dec(v_a_798_);
return v___x_801_;
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_829_; 
lean_dec_ref(v_expr_788_);
lean_dec_ref(v_expr_779_);
v___x_827_ = lean_box(v___x_777_);
if (v_isShared_794_ == 0)
{
lean_ctor_set_tag(v___x_793_, 0);
lean_ctor_set(v___x_793_, 0, v___x_827_);
v___x_829_ = v___x_793_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
else
{
lean_object* v___x_832_; lean_object* v___x_834_; 
lean_dec(v___x_790_);
lean_dec_ref(v_expr_788_);
lean_dec(v_val_784_);
lean_dec_ref(v_expr_779_);
v___x_832_ = lean_box(v___x_777_);
if (v_isShared_787_ == 0)
{
lean_ctor_set_tag(v___x_786_, 0);
lean_ctor_set(v___x_786_, 0, v___x_832_);
v___x_834_ = v___x_786_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec(v___x_782_);
lean_dec_ref(v_expr_779_);
lean_dec_ref(v_ti2_770_);
v___x_837_ = lean_box(v___x_777_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
else
{
uint8_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec_ref(v_ti2_770_);
lean_dec_ref(v_ti1_769_);
v___x_839_ = 0;
v___x_840_ = lean_box(v___x_839_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isInstanceProjectionInfoFor___boxed(lean_object* v_kind_842_, lean_object* v_ti1_843_, lean_object* v_ti2_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
uint8_t v_kind_boxed_850_; lean_object* v_res_851_; 
v_kind_boxed_850_ = lean_unbox(v_kind_842_);
v_res_851_ = l_Lean_Server_isInstanceProjectionInfoFor(v_kind_boxed_850_, v_ti1_843_, v_ti2_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToM_run___redArg(lean_object* v_ctx_852_, lean_object* v_ci_853_, lean_object* v_lctx_854_, lean_object* v_act_855_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_apply_1(v_act_855_, v_ctx_852_);
v___x_858_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ci_853_, v_lctx_854_, v___x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToM_run___redArg___boxed(lean_object* v_ctx_859_, lean_object* v_ci_860_, lean_object* v_lctx_861_, lean_object* v_act_862_, lean_object* v_a_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_Server_GoToM_run___redArg(v_ctx_859_, v_ci_860_, v_lctx_861_, v_act_862_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToM_run(lean_object* v_00_u03b1_865_, lean_object* v_ctx_866_, lean_object* v_ci_867_, lean_object* v_lctx_868_, lean_object* v_act_869_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_Server_GoToM_run___redArg(v_ctx_866_, v_ci_867_, v_lctx_868_, v_act_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToM_run___boxed(lean_object* v_00_u03b1_872_, lean_object* v_ctx_873_, lean_object* v_ci_874_, lean_object* v_lctx_875_, lean_object* v_act_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_Server_GoToM_run(v_00_u03b1_872_, v_ctx_873_, v_ci_874_, v_lctx_875_, v_act_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___x_885_; lean_object* v_env_886_; lean_object* v___x_887_; lean_object* v_mctx_888_; lean_object* v_lctx_889_; lean_object* v_options_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_885_ = lean_st_ref_get(v___y_883_);
v_env_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc_ref(v_env_886_);
lean_dec(v___x_885_);
v___x_887_ = lean_st_ref_get(v___y_881_);
v_mctx_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc_ref(v_mctx_888_);
lean_dec(v___x_887_);
v_lctx_889_ = lean_ctor_get(v___y_880_, 2);
v_options_890_ = lean_ctor_get(v___y_882_, 2);
lean_inc_ref(v_options_890_);
lean_inc_ref(v_lctx_889_);
v___x_891_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_891_, 0, v_env_886_);
lean_ctor_set(v___x_891_, 1, v_mctx_888_);
lean_ctor_set(v___x_891_, 2, v_lctx_889_);
lean_ctor_set(v___x_891_, 3, v_options_890_);
v___x_892_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
lean_ctor_set(v___x_892_, 1, v_msgData_879_);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_ref_907_; lean_object* v___x_908_; lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_917_; 
v_ref_907_ = lean_ctor_get(v___y_904_, 5);
v___x_908_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_917_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_917_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_917_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; lean_object* v___x_915_; 
lean_inc(v_ref_907_);
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v_ref_907_);
lean_ctor_set(v___x_913_, 1, v_a_909_);
if (v_isShared_912_ == 0)
{
lean_ctor_set_tag(v___x_911_, 1);
lean_ctor_set(v___x_911_, 0, v___x_913_);
v___x_915_ = v___x_911_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_925_, lean_object* v_msg_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_fileName_933_; lean_object* v_fileMap_934_; lean_object* v_options_935_; lean_object* v_currRecDepth_936_; lean_object* v_maxRecDepth_937_; lean_object* v_ref_938_; lean_object* v_currNamespace_939_; lean_object* v_openDecls_940_; lean_object* v_initHeartbeats_941_; lean_object* v_maxHeartbeats_942_; lean_object* v_quotContext_943_; lean_object* v_currMacroScope_944_; uint8_t v_diag_945_; lean_object* v_cancelTk_x3f_946_; uint8_t v_suppressElabErrors_947_; lean_object* v_inheritedTraceOptions_948_; lean_object* v_ref_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_fileName_933_ = lean_ctor_get(v___y_930_, 0);
v_fileMap_934_ = lean_ctor_get(v___y_930_, 1);
v_options_935_ = lean_ctor_get(v___y_930_, 2);
v_currRecDepth_936_ = lean_ctor_get(v___y_930_, 3);
v_maxRecDepth_937_ = lean_ctor_get(v___y_930_, 4);
v_ref_938_ = lean_ctor_get(v___y_930_, 5);
v_currNamespace_939_ = lean_ctor_get(v___y_930_, 6);
v_openDecls_940_ = lean_ctor_get(v___y_930_, 7);
v_initHeartbeats_941_ = lean_ctor_get(v___y_930_, 8);
v_maxHeartbeats_942_ = lean_ctor_get(v___y_930_, 9);
v_quotContext_943_ = lean_ctor_get(v___y_930_, 10);
v_currMacroScope_944_ = lean_ctor_get(v___y_930_, 11);
v_diag_945_ = lean_ctor_get_uint8(v___y_930_, sizeof(void*)*14);
v_cancelTk_x3f_946_ = lean_ctor_get(v___y_930_, 12);
v_suppressElabErrors_947_ = lean_ctor_get_uint8(v___y_930_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_948_ = lean_ctor_get(v___y_930_, 13);
v_ref_949_ = l_Lean_replaceRef(v_ref_925_, v_ref_938_);
lean_inc_ref(v_inheritedTraceOptions_948_);
lean_inc(v_cancelTk_x3f_946_);
lean_inc(v_currMacroScope_944_);
lean_inc(v_quotContext_943_);
lean_inc(v_maxHeartbeats_942_);
lean_inc(v_initHeartbeats_941_);
lean_inc(v_openDecls_940_);
lean_inc(v_currNamespace_939_);
lean_inc(v_maxRecDepth_937_);
lean_inc(v_currRecDepth_936_);
lean_inc_ref(v_options_935_);
lean_inc_ref(v_fileMap_934_);
lean_inc_ref(v_fileName_933_);
v___x_950_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_950_, 0, v_fileName_933_);
lean_ctor_set(v___x_950_, 1, v_fileMap_934_);
lean_ctor_set(v___x_950_, 2, v_options_935_);
lean_ctor_set(v___x_950_, 3, v_currRecDepth_936_);
lean_ctor_set(v___x_950_, 4, v_maxRecDepth_937_);
lean_ctor_set(v___x_950_, 5, v_ref_949_);
lean_ctor_set(v___x_950_, 6, v_currNamespace_939_);
lean_ctor_set(v___x_950_, 7, v_openDecls_940_);
lean_ctor_set(v___x_950_, 8, v_initHeartbeats_941_);
lean_ctor_set(v___x_950_, 9, v_maxHeartbeats_942_);
lean_ctor_set(v___x_950_, 10, v_quotContext_943_);
lean_ctor_set(v___x_950_, 11, v_currMacroScope_944_);
lean_ctor_set(v___x_950_, 12, v_cancelTk_x3f_946_);
lean_ctor_set(v___x_950_, 13, v_inheritedTraceOptions_948_);
lean_ctor_set_uint8(v___x_950_, sizeof(void*)*14, v_diag_945_);
lean_ctor_set_uint8(v___x_950_, sizeof(void*)*14 + 1, v_suppressElabErrors_947_);
v___x_951_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_926_, v___y_928_, v___y_929_, v___x_950_, v___y_931_);
lean_dec_ref_known(v___x_950_, 14);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_952_, lean_object* v_msg_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_952_, v_msg_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v_ref_952_);
return v_res_960_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_961_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
return v___x_963_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_964_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_965_ = lean_unsigned_to_nat(0u);
v___x_966_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
lean_ctor_set(v___x_966_, 2, v___x_965_);
lean_ctor_set(v___x_966_, 3, v___x_965_);
lean_ctor_set(v___x_966_, 4, v___x_964_);
lean_ctor_set(v___x_966_, 5, v___x_964_);
lean_ctor_set(v___x_966_, 6, v___x_964_);
lean_ctor_set(v___x_966_, 7, v___x_964_);
lean_ctor_set(v___x_966_, 8, v___x_964_);
lean_ctor_set(v___x_966_, 9, v___x_964_);
return v___x_966_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = lean_unsigned_to_nat(32u);
v___x_968_ = lean_mk_empty_array_with_capacity(v___x_967_);
v___x_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
return v___x_969_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_970_ = ((size_t)5ULL);
v___x_971_ = lean_unsigned_to_nat(0u);
v___x_972_ = lean_unsigned_to_nat(32u);
v___x_973_ = lean_mk_empty_array_with_capacity(v___x_972_);
v___x_974_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_975_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v___x_973_);
lean_ctor_set(v___x_975_, 2, v___x_971_);
lean_ctor_set(v___x_975_, 3, v___x_971_);
lean_ctor_set_usize(v___x_975_, 4, v___x_970_);
return v___x_975_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_976_ = lean_box(1);
v___x_977_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_978_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_979_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v___x_977_);
lean_ctor_set(v___x_979_, 2, v___x_976_);
return v___x_979_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_982_ = l_Lean_stringToMessageData(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_985_ = l_Lean_stringToMessageData(v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_988_ = l_Lean_stringToMessageData(v___x_987_);
return v___x_988_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_991_ = l_Lean_stringToMessageData(v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_994_ = l_Lean_stringToMessageData(v___x_993_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_997_ = l_Lean_stringToMessageData(v___x_996_);
return v___x_997_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1000_ = l_Lean_stringToMessageData(v___x_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1001_, lean_object* v_declHint_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; lean_object* v_env_1006_; uint8_t v___y_1008_; uint8_t v___x_1064_; uint8_t v___x_1065_; 
v___x_1005_ = lean_st_ref_get(v___y_1003_);
v_env_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc_ref(v_env_1006_);
lean_dec(v___x_1005_);
v___x_1064_ = l_Lean_Name_isAnonymous(v_declHint_1002_);
v___x_1065_ = lean_bool_not(v___x_1064_);
if (v___x_1065_ == 0)
{
v___y_1008_ = v___x_1065_;
goto v___jp_1007_;
}
else
{
uint8_t v_isExporting_1066_; 
v_isExporting_1066_ = lean_ctor_get_uint8(v_env_1006_, sizeof(void*)*8);
v___y_1008_ = v_isExporting_1066_;
goto v___jp_1007_;
}
v___jp_1007_:
{
if (v___y_1008_ == 0)
{
lean_object* v___x_1009_; 
lean_dec_ref(v_env_1006_);
lean_dec(v_declHint_1002_);
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v_msg_1001_);
return v___x_1009_;
}
else
{
uint8_t v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1010_ = 0;
lean_inc_ref(v_env_1006_);
v___x_1011_ = l_Lean_Environment_setExporting(v_env_1006_, v___x_1010_);
lean_inc(v_declHint_1002_);
lean_inc_ref(v___x_1011_);
v___x_1012_ = l_Lean_Environment_contains(v___x_1011_, v_declHint_1002_, v___y_1008_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; 
lean_dec_ref(v___x_1011_);
lean_dec_ref(v_env_1006_);
lean_dec(v_declHint_1002_);
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v_msg_1001_);
return v___x_1013_;
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v_c_1019_; lean_object* v___x_1020_; 
v___x_1014_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1015_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1016_ = l_Lean_Options_empty;
v___x_1017_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1011_);
lean_ctor_set(v___x_1017_, 1, v___x_1014_);
lean_ctor_set(v___x_1017_, 2, v___x_1015_);
lean_ctor_set(v___x_1017_, 3, v___x_1016_);
lean_inc(v_declHint_1002_);
v___x_1018_ = l_Lean_MessageData_ofConstName(v_declHint_1002_, v___x_1010_);
v_c_1019_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1019_, 0, v___x_1017_);
lean_ctor_set(v_c_1019_, 1, v___x_1018_);
v___x_1020_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1006_, v_declHint_1002_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_dec_ref(v_env_1006_);
lean_dec(v_declHint_1002_);
v___x_1021_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v_c_1019_);
v___x_1023_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = l_Lean_MessageData_note(v___x_1024_);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_msg_1001_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
return v___x_1027_;
}
else
{
lean_object* v_val_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1063_; 
v_val_1028_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1030_ = v___x_1020_;
v_isShared_1031_ = v_isSharedCheck_1063_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_val_1028_);
lean_dec(v___x_1020_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1063_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v_mod_1035_; uint8_t v___x_1036_; 
v___x_1032_ = lean_box(0);
v___x_1033_ = l_Lean_Environment_header(v_env_1006_);
lean_dec_ref(v_env_1006_);
v___x_1034_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1033_);
v_mod_1035_ = lean_array_get(v___x_1032_, v___x_1034_, v_val_1028_);
lean_dec(v_val_1028_);
lean_dec_ref(v___x_1034_);
v___x_1036_ = l_Lean_isPrivateName(v_declHint_1002_);
lean_dec(v_declHint_1002_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1037_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v_c_1019_);
v___x_1039_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_MessageData_ofName(v_mod_1035_);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1042_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = l_Lean_MessageData_note(v___x_1044_);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v_msg_1001_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1046_);
v___x_1048_ = v___x_1030_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
else
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1050_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
lean_ctor_set(v___x_1051_, 1, v_c_1019_);
v___x_1052_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = l_Lean_MessageData_ofName(v_mod_1035_);
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = l_Lean_MessageData_note(v___x_1057_);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v_msg_1001_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1059_);
v___x_1061_ = v___x_1030_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1067_, lean_object* v_declHint_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1067_, v_declHint_1068_, v___y_1069_);
lean_dec(v___y_1069_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1072_, lean_object* v_declHint_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___x_1080_; lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1090_; 
v___x_1080_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1072_, v_declHint_1073_, v___y_1078_);
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1090_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1090_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1085_ = l_Lean_unknownIdentifierMessageTag;
v___x_1086_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v_a_1081_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1086_);
v___x_1088_ = v___x_1083_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1091_, lean_object* v_declHint_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1091_, v_declHint_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec_ref(v___y_1093_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_1100_, lean_object* v_msg_1101_, lean_object* v_declHint_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; lean_object* v_a_1110_; lean_object* v___x_1111_; 
v___x_1109_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1101_, v_declHint_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref(v___x_1109_);
v___x_1111_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_1100_, v_a_1110_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1112_, lean_object* v_msg_1113_, lean_object* v_declHint_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_1112_, v_msg_1113_, v_declHint_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v_ref_1112_);
return v_res_1121_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1124_ = l_Lean_stringToMessageData(v___x_1123_);
return v___x_1124_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2));
v___x_1127_ = l_Lean_stringToMessageData(v___x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1128_, lean_object* v_constName_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1136_; uint8_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1136_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1137_ = 0;
lean_inc(v_constName_1129_);
v___x_1138_ = l_Lean_MessageData_ofConstName(v_constName_1129_, v___x_1137_);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1136_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1139_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_1128_, v___x_1141_, v_constName_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1143_, lean_object* v_constName_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1143_, v_constName_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v_ref_1143_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v_ref_1159_; lean_object* v___x_1160_; 
v_ref_1159_ = lean_ctor_get(v___y_1156_, 5);
v___x_1160_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1159_, v_constName_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec_ref(v___y_1162_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(lean_object* v_constName_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v___x_1176_; lean_object* v_env_1177_; uint8_t v___x_1178_; lean_object* v___x_1179_; 
v___x_1176_ = lean_st_ref_get(v___y_1174_);
v_env_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc_ref(v_env_1177_);
lean_dec(v___x_1176_);
v___x_1178_ = 0;
lean_inc(v_constName_1169_);
v___x_1179_ = l_Lean_Environment_find_x3f(v_env_1177_, v_constName_1169_, v___x_1178_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
return v___x_1180_;
}
else
{
lean_object* v_val_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v_constName_1169_);
v_val_1181_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1179_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_val_1181_);
lean_dec(v___x_1179_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set_tag(v___x_1183_, 0);
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_val_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0___boxed(lean_object* v_constName_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(v_constName_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec_ref(v___y_1190_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(lean_object* v_declName_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v___x_1204_; 
lean_inc(v_declName_1197_);
v___x_1204_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(v_declName_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1231_; 
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v___x_1204_, 0);
lean_dec(v_unused_1232_);
v___x_1206_ = v___x_1204_;
v_isShared_1207_ = v_isSharedCheck_1231_;
goto v_resetjp_1205_;
}
else
{
lean_dec(v___x_1204_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1231_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v_env_1209_; lean_object* v___x_1210_; 
v___x_1208_ = lean_st_ref_get(v___y_1202_);
v_env_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc_ref(v_env_1209_);
lean_dec(v___x_1208_);
v___x_1210_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1209_, v_declName_1197_);
lean_dec(v_declName_1197_);
lean_dec_ref(v_env_1209_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1211_ = lean_box(0);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1211_);
v___x_1213_ = v___x_1206_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
else
{
lean_object* v_val_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1230_; 
v_val_1215_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1217_ = v___x_1210_;
v_isShared_1218_ = v_isSharedCheck_1230_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_val_1215_);
lean_dec(v___x_1210_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1230_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v_env_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1219_ = lean_st_ref_get(v___y_1202_);
v_env_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc_ref(v_env_1220_);
lean_dec(v___x_1219_);
v___x_1221_ = lean_box(0);
v___x_1222_ = l_Lean_Environment_allImportedModuleNames(v_env_1220_);
lean_dec_ref(v_env_1220_);
v___x_1223_ = lean_array_get(v___x_1221_, v___x_1222_, v_val_1215_);
lean_dec(v_val_1215_);
lean_dec_ref(v___x_1222_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1223_);
v___x_1225_ = v___x_1217_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1227_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1225_);
v___x_1227_ = v___x_1206_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v_declName_1197_);
v_a_1233_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1204_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1204_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0___boxed(lean_object* v_declName_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(v_declName_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(lean_object* v_declName_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(v_declName_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1311_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1311_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1311_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
if (lean_obj_tag(v_a_1257_) == 0)
{
lean_object* v_doc_1261_; lean_object* v_uri_1262_; lean_object* v_mod_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
v_doc_1261_ = lean_ctor_get(v_a_1250_, 0);
v_uri_1262_ = lean_ctor_get(v_doc_1261_, 0);
v_mod_1263_ = lean_ctor_get(v_doc_1261_, 1);
lean_inc_ref(v_uri_1262_);
lean_inc(v_mod_1263_);
v___x_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1264_, 0, v_mod_1263_);
lean_ctor_set(v___x_1264_, 1, v_uri_1262_);
v___x_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
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
else
{
lean_object* v_val_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1310_; 
lean_del_object(v___x_1259_);
v_val_1269_ = lean_ctor_get(v_a_1257_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_a_1257_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1271_ = v_a_1257_;
v_isShared_1272_ = v_isSharedCheck_1310_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_val_1269_);
lean_dec(v_a_1257_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1310_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; 
lean_inc(v_val_1269_);
v___x_1273_ = l_Lean_Server_documentUriFromModule_x3f(v_val_1269_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1294_; 
lean_del_object(v___x_1271_);
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1294_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1294_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
if (lean_obj_tag(v_a_1274_) == 1)
{
lean_object* v_val_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1289_; 
v_val_1278_ = lean_ctor_get(v_a_1274_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_a_1274_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1280_ = v_a_1274_;
v_isShared_1281_ = v_isSharedCheck_1289_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_val_1278_);
lean_dec(v_a_1274_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1289_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v_val_1269_);
lean_ctor_set(v___x_1282_, 1, v_val_1278_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1282_);
v___x_1284_ = v___x_1280_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1286_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1284_);
v___x_1286_ = v___x_1276_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v___x_1290_; lean_object* v___x_1292_; 
lean_dec(v_a_1274_);
lean_dec(v_val_1269_);
v___x_1290_ = lean_box(0);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1290_);
v___x_1292_ = v___x_1276_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1309_; 
lean_dec(v_val_1269_);
v_a_1295_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1297_ = v___x_1273_;
v_isShared_1298_ = v_isSharedCheck_1309_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1273_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1309_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v_ref_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
v_ref_1299_ = lean_ctor_get(v_a_1253_, 5);
v___x_1300_ = lean_io_error_to_string(v_a_1295_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set_tag(v___x_1271_, 3);
lean_ctor_set(v___x_1271_, 0, v___x_1300_);
v___x_1302_ = v___x_1271_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1303_ = l_Lean_MessageData_ofFormat(v___x_1302_);
lean_inc(v_ref_1299_);
v___x_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1304_, 0, v_ref_1299_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1304_);
v___x_1306_ = v___x_1297_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
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
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
v_a_1312_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1256_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1256_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f___boxed(lean_object* v_declName_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(v_declName_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1322_);
lean_dec_ref(v_a_1321_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1328_, lean_object* v_constName_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1337_, lean_object* v_constName_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1(v_00_u03b1_1337_, v_constName_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec_ref(v___y_1339_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1346_, lean_object* v_ref_1347_, lean_object* v_constName_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1347_, v_constName_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1356_, lean_object* v_ref_1357_, lean_object* v_constName_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1356_, v_ref_1357_, v_constName_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v_ref_1357_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_1366_, lean_object* v_ref_1367_, lean_object* v_msg_1368_, lean_object* v_declHint_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_1367_, v_msg_1368_, v_declHint_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1377_, lean_object* v_ref_1378_, lean_object* v_msg_1379_, lean_object* v_declHint_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b1_1377_, v_ref_1378_, v_msg_1379_, v_declHint_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v_ref_1378_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1388_, lean_object* v_declHint_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1388_, v_declHint_1389_, v___y_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1397_, lean_object* v_declHint_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1397_, v_declHint_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec_ref(v___y_1399_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1406_, lean_object* v_ref_1407_, lean_object* v_msg_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_1407_, v_msg_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1416_, lean_object* v_ref_1417_, lean_object* v_msg_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_1416_, v_ref_1417_, v_msg_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v_ref_1417_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1426_, lean_object* v_msg_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1427_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1435_, lean_object* v_msg_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1435_, v_msg_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec_ref(v___y_1437_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(lean_object* v_declName_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1447_; lean_object* v_env_1448_; uint8_t v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1447_ = lean_st_ref_get(v___y_1445_);
v_env_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc_ref(v_env_1448_);
lean_dec(v___x_1447_);
v___x_1449_ = l_Lean_isRecCore(v_env_1448_, v_declName_1444_);
v___x_1450_ = lean_box(v___x_1449_);
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_1452_, v___y_1453_);
lean_dec(v___y_1453_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(lean_object* v_declName_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___x_1459_; lean_object* v_env_1460_; lean_object* v___x_1461_; lean_object* v_env_1462_; lean_object* v___x_1463_; lean_object* v_toEnvExtension_1464_; lean_object* v_asyncMode_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; lean_object* v___x_1468_; 
v___x_1459_ = lean_st_ref_get(v___y_1457_);
v_env_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc_ref(v_env_1460_);
lean_dec(v___x_1459_);
v___x_1461_ = lean_st_ref_get(v___y_1457_);
v_env_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc_ref(v_env_1462_);
lean_dec(v___x_1461_);
v___x_1463_ = l_Lean_declRangeExt;
v_toEnvExtension_1464_ = lean_ctor_get(v___x_1463_, 0);
v_asyncMode_1465_ = lean_ctor_get(v_toEnvExtension_1464_, 2);
v___x_1466_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1467_ = 0;
lean_inc(v_declName_1456_);
v___x_1468_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1466_, v___x_1463_, v_env_1460_, v_declName_1456_, v_asyncMode_1465_, v___x_1467_);
if (lean_obj_tag(v___x_1468_) == 0)
{
uint8_t v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1469_ = 1;
v___x_1470_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1466_, v___x_1463_, v_env_1462_, v_declName_1456_, v_asyncMode_1465_, v___x_1469_);
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
else
{
lean_object* v___x_1472_; 
lean_dec_ref(v_env_1462_);
lean_dec(v_declName_1456_);
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1468_);
return v___x_1472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_1473_, v___y_1474_);
lean_dec(v___y_1474_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(lean_object* v_declName_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_ranges_1485_; lean_object* v___x_1491_; lean_object* v_env_1492_; lean_object* v___x_1493_; lean_object* v_a_1494_; uint8_t v___y_1500_; uint8_t v___x_1504_; 
v___x_1491_ = lean_st_ref_get(v___y_1482_);
v_env_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc_ref_n(v_env_1492_, 2);
lean_dec(v___x_1491_);
lean_inc_n(v_declName_1477_, 2);
v___x_1493_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_1477_, v___y_1482_);
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref(v___x_1493_);
v___x_1504_ = l_Lean_isAuxRecursor(v_env_1492_, v_declName_1477_);
if (v___x_1504_ == 0)
{
uint8_t v___x_1505_; 
lean_inc(v_declName_1477_);
v___x_1505_ = l_Lean_isNoConfusion(v_env_1492_, v_declName_1477_);
v___y_1500_ = v___x_1505_;
goto v___jp_1499_;
}
else
{
lean_dec_ref(v_env_1492_);
v___y_1500_ = v___x_1504_;
goto v___jp_1499_;
}
v___jp_1484_:
{
if (lean_obj_tag(v_ranges_1485_) == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1486_ = l_Lean_builtinDeclRanges;
v___x_1487_ = lean_st_ref_get(v___x_1486_);
v___x_1488_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1487_, v_declName_1477_);
lean_dec(v_declName_1477_);
lean_dec(v___x_1487_);
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
return v___x_1489_;
}
else
{
lean_object* v___x_1490_; 
lean_dec(v_declName_1477_);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v_ranges_1485_);
return v___x_1490_;
}
}
v___jp_1495_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v_a_1498_; 
v___x_1496_ = l_Lean_Name_getPrefix(v_declName_1477_);
v___x_1497_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v___x_1496_, v___y_1482_);
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref(v___x_1497_);
v_ranges_1485_ = v_a_1498_;
goto v___jp_1484_;
}
v___jp_1499_:
{
if (v___y_1500_ == 0)
{
uint8_t v___x_1501_; 
v___x_1501_ = lean_unbox(v_a_1494_);
lean_dec(v_a_1494_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v_a_1503_; 
lean_inc(v_declName_1477_);
v___x_1502_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_1477_, v___y_1482_);
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
lean_dec_ref(v___x_1502_);
v_ranges_1485_ = v_a_1503_;
goto v___jp_1484_;
}
else
{
goto v___jp_1495_;
}
}
else
{
lean_dec(v_a_1494_);
goto v___jp_1495_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0___boxed(lean_object* v_declName_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(v_declName_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec_ref(v___y_1507_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl(lean_object* v_declName_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v___x_1523_; lean_object* v_env_1524_; uint8_t v___x_1525_; uint8_t v___x_1526_; uint8_t v___x_1527_; 
v___x_1523_ = lean_st_ref_get(v_a_1521_);
v_env_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc_ref(v_env_1524_);
lean_dec(v___x_1523_);
v___x_1525_ = 1;
lean_inc(v_declName_1516_);
v___x_1526_ = l_Lean_Environment_contains(v_env_1524_, v_declName_1516_, v___x_1525_);
v___x_1527_ = lean_bool_not(v___x_1526_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; 
lean_inc(v_declName_1516_);
v___x_1528_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(v_declName_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1604_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1531_ = v___x_1528_;
v_isShared_1532_ = v_isSharedCheck_1604_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1604_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
if (lean_obj_tag(v_a_1529_) == 1)
{
lean_object* v_val_1533_; lean_object* v_fst_1534_; lean_object* v_snd_1535_; lean_object* v___x_1536_; 
lean_del_object(v___x_1531_);
v_val_1533_ = lean_ctor_get(v_a_1529_, 0);
lean_inc(v_val_1533_);
lean_dec_ref_known(v_a_1529_, 1);
v_fst_1534_ = lean_ctor_get(v_val_1533_, 0);
lean_inc(v_fst_1534_);
v_snd_1535_ = lean_ctor_get(v_val_1533_, 1);
lean_inc(v_snd_1535_);
lean_dec(v_val_1533_);
lean_inc(v_declName_1516_);
v___x_1536_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(v_declName_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1591_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1591_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1591_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
if (lean_obj_tag(v_a_1537_) == 1)
{
lean_object* v_val_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1586_; 
v_val_1541_ = lean_ctor_get(v_a_1537_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_a_1537_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1543_ = v_a_1537_;
v_isShared_1544_ = v_isSharedCheck_1586_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_val_1541_);
lean_dec(v_a_1537_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1586_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___y_1546_; lean_object* v_originInfo_x3f_1570_; 
v_originInfo_x3f_1570_ = lean_ctor_get(v_a_1517_, 2);
if (lean_obj_tag(v_originInfo_x3f_1570_) == 0)
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_box(0);
v___y_1546_ = v___x_1571_;
goto v___jp_1545_;
}
else
{
lean_object* v_doc_1572_; lean_object* v_val_1573_; lean_object* v___x_1574_; 
v_doc_1572_ = lean_ctor_get(v_a_1517_, 0);
v_val_1573_ = lean_ctor_get(v_originInfo_x3f_1570_, 0);
v___x_1574_ = l_Lean_Elab_Info_range_x3f(v_val_1573_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_box(0);
v___y_1546_ = v___x_1575_;
goto v___jp_1545_;
}
else
{
lean_object* v_val_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1585_; 
v_val_1576_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1578_ = v___x_1574_;
v_isShared_1579_ = v_isSharedCheck_1585_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_val_1576_);
lean_dec(v___x_1574_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1585_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v_text_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
v_text_1580_ = lean_ctor_get(v_doc_1572_, 3);
lean_inc_ref(v_text_1580_);
v___x_1581_ = l_Lean_Syntax_Range_toLspRange(v_text_1580_, v_val_1576_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1581_);
v___x_1583_ = v___x_1578_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
v___y_1546_ = v___x_1583_;
goto v___jp_1545_;
}
}
}
}
v___jp_1545_:
{
lean_object* v_range_1547_; lean_object* v_selectionRange_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1569_; 
v_range_1547_ = lean_ctor_get(v_val_1541_, 0);
v_selectionRange_1548_ = lean_ctor_get(v_val_1541_, 1);
v_isSharedCheck_1569_ = !lean_is_exclusive(v_val_1541_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1550_ = v_val_1541_;
v_isShared_1551_ = v_isSharedCheck_1569_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_selectionRange_1548_);
lean_inc(v_range_1547_);
lean_dec(v_val_1541_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1569_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
v___x_1552_ = l_Lean_DeclarationRange_toLspRange(v_range_1547_);
v___x_1553_ = l_Lean_DeclarationRange_toLspRange(v_selectionRange_1548_);
v___x_1554_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1554_, 0, v___y_1546_);
lean_ctor_set(v___x_1554_, 1, v_snd_1535_);
lean_ctor_set(v___x_1554_, 2, v___x_1552_);
lean_ctor_set(v___x_1554_, 3, v___x_1553_);
v___x_1555_ = l_Lean_Name_eraseMacroScopes(v_declName_1516_);
lean_dec(v_declName_1516_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 1, v___x_1555_);
lean_ctor_set(v___x_1550_, 0, v_fst_1534_);
v___x_1557_ = v___x_1550_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_fst_1534_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1559_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1557_);
v___x_1559_ = v___x_1543_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1560_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1560_, 0, v___x_1554_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
lean_ctor_set_uint8(v___x_1560_, sizeof(void*)*2, v___x_1527_);
v___x_1561_ = lean_unsigned_to_nat(1u);
v___x_1562_ = lean_mk_empty_array_with_capacity(v___x_1561_);
v___x_1563_ = lean_array_push(v___x_1562_, v___x_1560_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1563_);
v___x_1565_ = v___x_1539_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1589_; 
lean_dec(v_a_1537_);
lean_dec(v_snd_1535_);
lean_dec(v_fst_1534_);
lean_dec(v_declName_1516_);
v___x_1587_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1587_);
v___x_1589_ = v___x_1539_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec(v_snd_1535_);
lean_dec(v_fst_1534_);
lean_dec(v_declName_1516_);
v_a_1592_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1536_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1536_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1602_; 
lean_dec(v_a_1529_);
lean_dec(v_declName_1516_);
v___x_1600_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1600_);
v___x_1602_ = v___x_1531_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec(v_declName_1516_);
v_a_1605_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1528_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1528_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
lean_dec(v_declName_1516_);
v___x_1613_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
return v___x_1614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl___boxed(lean_object* v_declName_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_Server_locationLinksFromDecl(v_declName_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
lean_dec(v_a_1620_);
lean_dec_ref(v_a_1619_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec_ref(v_a_1616_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0(lean_object* v_declName_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_1623_, v___y_1628_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___boxed(lean_object* v_declName_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0(v_declName_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec_ref(v___y_1632_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1(lean_object* v_declName_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_1639_, v___y_1644_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___boxed(lean_object* v_declName_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1(v_declName_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec_ref(v___y_1648_);
return v_res_1654_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0(lean_object* v_id_1655_, lean_object* v_x_1656_){
_start:
{
if (lean_obj_tag(v_x_1656_) == 1)
{
lean_object* v_i_1657_; lean_object* v_expr_1658_; 
v_i_1657_ = lean_ctor_get(v_x_1656_, 0);
v_expr_1658_ = lean_ctor_get(v_i_1657_, 3);
if (lean_obj_tag(v_expr_1658_) == 1)
{
uint8_t v_isBinder_1659_; 
v_isBinder_1659_ = lean_ctor_get_uint8(v_i_1657_, sizeof(void*)*4);
if (v_isBinder_1659_ == 1)
{
lean_object* v_fvarId_1660_; uint8_t v___x_1661_; 
v_fvarId_1660_ = lean_ctor_get(v_expr_1658_, 0);
v___x_1661_ = l_Lean_instBEqFVarId_beq(v_fvarId_1660_, v_id_1655_);
return v___x_1661_;
}
else
{
uint8_t v___x_1662_; 
v___x_1662_ = 0;
return v___x_1662_;
}
}
else
{
uint8_t v___x_1663_; 
v___x_1663_ = 0;
return v___x_1663_;
}
}
else
{
uint8_t v___x_1664_; 
v___x_1664_ = 0;
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0___boxed(lean_object* v_id_1665_, lean_object* v_x_1666_){
_start:
{
uint8_t v_res_1667_; lean_object* v_r_1668_; 
v_res_1667_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0(v_id_1665_, v_x_1666_);
lean_dec_ref(v_x_1666_);
lean_dec(v_id_1665_);
v_r_1668_ = lean_box(v_res_1667_);
return v_r_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(lean_object* v_id_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v_infoTree_x3f_1672_; 
v_infoTree_x3f_1672_ = lean_ctor_get(v_a_1670_, 1);
if (lean_obj_tag(v_infoTree_x3f_1672_) == 1)
{
lean_object* v_val_1673_; lean_object* v___f_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v_val_1673_ = lean_ctor_get(v_infoTree_x3f_1672_, 0);
v___f_1674_ = lean_alloc_closure((void*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1674_, 0, v_id_1669_);
lean_inc(v_val_1673_);
v___x_1675_ = l_Lean_Elab_InfoTree_findInfo_x3f(v___f_1674_, v_val_1673_);
v___x_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
return v___x_1676_;
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec(v_id_1669_);
v___x_1677_ = lean_box(0);
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
return v___x_1678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___boxed(lean_object* v_id_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(v_id_1679_, v_a_1680_);
lean_dec_ref(v_a_1680_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f(lean_object* v_id_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(v_id_1683_, v_a_1684_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___boxed(lean_object* v_id_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f(v_id_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
lean_dec_ref(v_a_1692_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromBinder___redArg(lean_object* v_id_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v___x_1702_; lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1748_; 
v___x_1702_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(v_id_1699_, v_a_1700_);
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1705_ = v___x_1702_;
v_isShared_1706_ = v_isSharedCheck_1748_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1702_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1748_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
if (lean_obj_tag(v_a_1703_) == 1)
{
lean_object* v_val_1707_; lean_object* v___x_1708_; 
v_val_1707_ = lean_ctor_get(v_a_1703_, 0);
lean_inc(v_val_1707_);
lean_dec_ref_known(v_a_1703_, 1);
v___x_1708_ = l_Lean_Elab_Info_range_x3f(v_val_1707_);
lean_dec(v_val_1707_);
if (lean_obj_tag(v___x_1708_) == 1)
{
lean_object* v_doc_1709_; lean_object* v_val_1710_; lean_object* v_originInfo_x3f_1711_; lean_object* v_uri_1712_; lean_object* v_text_1713_; lean_object* v___x_1714_; lean_object* v___y_1716_; 
v_doc_1709_ = lean_ctor_get(v_a_1700_, 0);
v_val_1710_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_val_1710_);
lean_dec_ref_known(v___x_1708_, 1);
v_originInfo_x3f_1711_ = lean_ctor_get(v_a_1700_, 2);
v_uri_1712_ = lean_ctor_get(v_doc_1709_, 0);
v_text_1713_ = lean_ctor_get(v_doc_1709_, 3);
lean_inc_ref(v_text_1713_);
v___x_1714_ = l_Lean_Syntax_Range_toLspRange(v_text_1713_, v_val_1710_);
if (lean_obj_tag(v_originInfo_x3f_1711_) == 0)
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_box(0);
v___y_1716_ = v___x_1727_;
goto v___jp_1715_;
}
else
{
lean_object* v_val_1728_; lean_object* v___x_1729_; 
v_val_1728_ = lean_ctor_get(v_originInfo_x3f_1711_, 0);
v___x_1729_ = l_Lean_Elab_Info_range_x3f(v_val_1728_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v___x_1730_; 
v___x_1730_ = lean_box(0);
v___y_1716_ = v___x_1730_;
goto v___jp_1715_;
}
else
{
lean_object* v_val_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1739_; 
v_val_1731_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1733_ = v___x_1729_;
v_isShared_1734_ = v_isSharedCheck_1739_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_val_1731_);
lean_dec(v___x_1729_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1739_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1735_; lean_object* v___x_1737_; 
lean_inc_ref(v_text_1713_);
v___x_1735_ = l_Lean_Syntax_Range_toLspRange(v_text_1713_, v_val_1731_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v___x_1735_);
v___x_1737_ = v___x_1733_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
v___y_1716_ = v___x_1737_;
goto v___jp_1715_;
}
}
}
}
v___jp_1715_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1725_; 
lean_inc_ref(v___x_1714_);
lean_inc_ref(v_uri_1712_);
v___x_1717_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1717_, 0, v___y_1716_);
lean_ctor_set(v___x_1717_, 1, v_uri_1712_);
lean_ctor_set(v___x_1717_, 2, v___x_1714_);
lean_ctor_set(v___x_1717_, 3, v___x_1714_);
v___x_1718_ = lean_box(0);
v___x_1719_ = 0;
v___x_1720_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1720_, 0, v___x_1717_);
lean_ctor_set(v___x_1720_, 1, v___x_1718_);
lean_ctor_set_uint8(v___x_1720_, sizeof(void*)*2, v___x_1719_);
v___x_1721_ = lean_unsigned_to_nat(1u);
v___x_1722_ = lean_mk_empty_array_with_capacity(v___x_1721_);
v___x_1723_ = lean_array_push(v___x_1722_, v___x_1720_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1723_);
v___x_1725_ = v___x_1705_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1742_; 
lean_dec(v___x_1708_);
v___x_1740_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1740_);
v___x_1742_ = v___x_1705_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1746_; 
lean_dec(v_a_1703_);
v___x_1744_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1744_);
v___x_1746_ = v___x_1705_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromBinder___redArg___boxed(lean_object* v_id_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_Server_locationLinksFromBinder___redArg(v_id_1749_, v_a_1750_);
lean_dec_ref(v_a_1750_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromBinder(lean_object* v_id_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_Server_locationLinksFromBinder___redArg(v_id_1753_, v_a_1754_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromBinder___boxed(lean_object* v_id_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_Server_locationLinksFromBinder(v_id_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
lean_dec(v_a_1766_);
lean_dec_ref(v_a_1765_);
lean_dec(v_a_1764_);
lean_dec_ref(v_a_1763_);
lean_dec_ref(v_a_1762_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromImport___redArg(lean_object* v_i_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v_stx_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1913_; 
v_stx_1816_ = lean_ctor_get(v_i_1800_, 1);
v_isSharedCheck_1913_ = !lean_is_exclusive(v_i_1800_);
if (v_isSharedCheck_1913_ == 0)
{
lean_object* v_unused_1914_; 
v_unused_1914_ = lean_ctor_get(v_i_1800_, 0);
lean_dec(v_unused_1914_);
v___x_1818_ = v_i_1800_;
v_isShared_1819_ = v_isSharedCheck_1913_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_stx_1816_);
lean_dec(v_i_1800_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1913_;
goto v_resetjp_1817_;
}
v___jp_1804_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
lean_inc_ref_n(v___y_1805_, 2);
v___x_1808_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1808_, 0, v___y_1807_);
lean_ctor_set(v___x_1808_, 1, v___y_1806_);
lean_ctor_set(v___x_1808_, 2, v___y_1805_);
lean_ctor_set(v___x_1808_, 3, v___y_1805_);
v___x_1809_ = lean_box(0);
v___x_1810_ = 0;
v___x_1811_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1811_, 0, v___x_1808_);
lean_ctor_set(v___x_1811_, 1, v___x_1809_);
lean_ctor_set_uint8(v___x_1811_, sizeof(void*)*2, v___x_1810_);
v___x_1812_ = lean_unsigned_to_nat(1u);
v___x_1813_ = lean_mk_empty_array_with_capacity(v___x_1812_);
v___x_1814_ = lean_array_push(v___x_1813_, v___x_1811_);
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
return v___x_1815_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1820_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__4));
lean_inc(v_stx_1816_);
v___x_1821_ = l_Lean_Syntax_isOfKind(v_stx_1816_, v___x_1820_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_del_object(v___x_1818_);
lean_dec(v_stx_1816_);
v___x_1822_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
return v___x_1823_;
}
else
{
lean_object* v___x_1824_; lean_object* v___y_1826_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1890_; lean_object* v___x_1902_; uint8_t v___x_1903_; 
v___x_1824_ = lean_unsigned_to_nat(0u);
v___x_1902_ = l_Lean_Syntax_getArg(v_stx_1816_, v___x_1824_);
v___x_1903_ = l_Lean_Syntax_isNone(v___x_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1904_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1902_);
v___x_1905_ = l_Lean_Syntax_matchesNull(v___x_1902_, v___x_1904_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
lean_dec(v___x_1902_);
lean_del_object(v___x_1818_);
lean_dec(v_stx_1816_);
v___x_1906_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
return v___x_1907_;
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; 
v___x_1908_ = l_Lean_Syntax_getArg(v___x_1902_, v___x_1824_);
lean_dec(v___x_1902_);
v___x_1909_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__12));
v___x_1910_ = l_Lean_Syntax_isOfKind(v___x_1908_, v___x_1909_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
lean_del_object(v___x_1818_);
lean_dec(v_stx_1816_);
v___x_1911_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
return v___x_1912_;
}
else
{
v___y_1890_ = v_a_1802_;
goto v___jp_1889_;
}
}
}
else
{
lean_dec(v___x_1902_);
v___y_1890_ = v_a_1802_;
goto v___jp_1889_;
}
v___jp_1825_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1827_ = lean_unsigned_to_nat(5u);
v___x_1828_ = l_Lean_Syntax_getArg(v_stx_1816_, v___x_1827_);
v___x_1829_ = l_Lean_Syntax_matchesNull(v___x_1828_, v___x_1824_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_del_object(v___x_1818_);
lean_dec(v_stx_1816_);
v___x_1830_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
return v___x_1831_;
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1832_ = lean_unsigned_to_nat(4u);
v___x_1833_ = l_Lean_Syntax_getArg(v_stx_1816_, v___x_1832_);
lean_dec(v_stx_1816_);
v___x_1834_ = l_Lean_TSyntax_getId(v___x_1833_);
v___x_1835_ = l_Lean_Server_documentUriFromModule_x3f(v___x_1834_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1859_; 
lean_del_object(v___x_1818_);
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1859_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1859_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
if (lean_obj_tag(v_a_1836_) == 1)
{
lean_object* v_val_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_del_object(v___x_1838_);
v_val_1840_ = lean_ctor_get(v_a_1836_, 0);
lean_inc(v_val_1840_);
lean_dec_ref_known(v_a_1836_, 1);
v___x_1841_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__6));
v___x_1842_ = l_Lean_Syntax_getRange_x3f(v___x_1833_, v___x_1821_);
lean_dec(v___x_1833_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_box(0);
v___y_1805_ = v___x_1841_;
v___y_1806_ = v_val_1840_;
v___y_1807_ = v___x_1843_;
goto v___jp_1804_;
}
else
{
lean_object* v_doc_1844_; lean_object* v_val_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1854_; 
v_doc_1844_ = lean_ctor_get(v_a_1801_, 0);
v_val_1845_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1847_ = v___x_1842_;
v_isShared_1848_ = v_isSharedCheck_1854_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_val_1845_);
lean_dec(v___x_1842_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1854_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v_text_1849_; lean_object* v___x_1850_; lean_object* v___x_1852_; 
v_text_1849_ = lean_ctor_get(v_doc_1844_, 3);
lean_inc_ref(v_text_1849_);
v___x_1850_ = l_Lean_Syntax_Range_toLspRange(v_text_1849_, v_val_1845_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1850_);
v___x_1852_ = v___x_1847_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
v___y_1805_ = v___x_1841_;
v___y_1806_ = v_val_1840_;
v___y_1807_ = v___x_1852_;
goto v___jp_1804_;
}
}
}
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
lean_dec(v_a_1836_);
lean_dec(v___x_1833_);
v___x_1855_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1855_);
v___x_1857_ = v___x_1838_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1874_; 
lean_dec(v___x_1833_);
v_a_1860_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1862_ = v___x_1835_;
v_isShared_1863_ = v_isSharedCheck_1874_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1835_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1874_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v_ref_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v_ref_1864_ = lean_ctor_get(v___y_1826_, 5);
v___x_1865_ = lean_io_error_to_string(v_a_1860_);
v___x_1866_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
v___x_1867_ = l_Lean_MessageData_ofFormat(v___x_1866_);
lean_inc(v_ref_1864_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 1, v___x_1867_);
lean_ctor_set(v___x_1818_, 0, v_ref_1864_);
v___x_1869_ = v___x_1818_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_ref_1864_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1871_; 
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1869_);
v___x_1871_ = v___x_1862_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
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
v___jp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; 
v___x_1878_ = lean_unsigned_to_nat(3u);
v___x_1879_ = l_Lean_Syntax_getArg(v_stx_1816_, v___x_1878_);
v___x_1880_ = l_Lean_Syntax_isNone(v___x_1879_);
if (v___x_1880_ == 0)
{
uint8_t v___x_1881_; 
lean_inc(v___x_1879_);
v___x_1881_ = l_Lean_Syntax_matchesNull(v___x_1879_, v___y_1876_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_dec(v___x_1879_);
lean_del_object(v___x_1818_);
lean_dec(v_stx_1816_);
v___x_1882_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1884_ = l_Lean_Syntax_getArg(v___x_1879_, v___x_1824_);
lean_dec(v___x_1879_);
v___x_1885_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__8));
v___x_1886_ = l_Lean_Syntax_isOfKind(v___x_1884_, v___x_1885_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_del_object(v___x_1818_);
lean_dec(v_stx_1816_);
v___x_1887_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
return v___x_1888_;
}
else
{
v___y_1826_ = v___y_1877_;
goto v___jp_1825_;
}
}
}
else
{
lean_dec(v___x_1879_);
v___y_1826_ = v___y_1877_;
goto v___jp_1825_;
}
}
v___jp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; 
v___x_1891_ = lean_unsigned_to_nat(1u);
v___x_1892_ = l_Lean_Syntax_getArg(v_stx_1816_, v___x_1891_);
v___x_1893_ = l_Lean_Syntax_isNone(v___x_1892_);
if (v___x_1893_ == 0)
{
uint8_t v___x_1894_; 
lean_inc(v___x_1892_);
v___x_1894_ = l_Lean_Syntax_matchesNull(v___x_1892_, v___x_1891_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
lean_dec(v___x_1892_);
lean_del_object(v___x_1818_);
lean_dec(v_stx_1816_);
v___x_1895_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
return v___x_1896_;
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1897_ = l_Lean_Syntax_getArg(v___x_1892_, v___x_1824_);
lean_dec(v___x_1892_);
v___x_1898_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__10));
v___x_1899_ = l_Lean_Syntax_isOfKind(v___x_1897_, v___x_1898_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
lean_del_object(v___x_1818_);
lean_dec(v_stx_1816_);
v___x_1900_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
else
{
v___y_1876_ = v___x_1891_;
v___y_1877_ = v___y_1890_;
goto v___jp_1875_;
}
}
}
else
{
lean_dec(v___x_1892_);
v___y_1876_ = v___x_1891_;
v___y_1877_ = v___y_1890_;
goto v___jp_1875_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromImport___redArg___boxed(lean_object* v_i_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_Server_locationLinksFromImport___redArg(v_i_1915_, v_a_1916_, v_a_1917_);
lean_dec_ref(v_a_1917_);
lean_dec_ref(v_a_1916_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromImport(lean_object* v_i_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Lean_Server_locationLinksFromImport___redArg(v_i_1920_, v_a_1921_, v_a_1924_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromImport___boxed(lean_object* v_i_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_Server_locationLinksFromImport(v_i_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
lean_dec(v_a_1933_);
lean_dec_ref(v_a_1932_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec_ref(v_a_1929_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v___x_1958_; lean_object* v_originInfo_x3f_1962_; 
v___x_1958_ = lean_st_ref_get(v_a_1956_);
v_originInfo_x3f_1962_ = lean_ctor_get(v_a_1955_, 2);
if (lean_obj_tag(v_originInfo_x3f_1962_) == 1)
{
uint8_t v_kind_1963_; lean_object* v_val_1964_; lean_object* v___x_1965_; 
v_kind_1963_ = lean_ctor_get_uint8(v_a_1955_, sizeof(void*)*4);
v_val_1964_ = lean_ctor_get(v_originInfo_x3f_1962_, 0);
lean_inc(v_val_1964_);
v___x_1965_ = l_Lean_Elab_Info_toElabInfo_x3f(v_val_1964_);
if (lean_obj_tag(v___x_1965_) == 1)
{
lean_object* v_val_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_2002_; 
v_val_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_2002_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_val_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_2002_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v_elaborator_1970_; lean_object* v_stx_1971_; lean_object* v___y_1973_; uint8_t v___y_1974_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
v_elaborator_1970_ = lean_ctor_get(v_val_1966_, 0);
lean_inc(v_elaborator_1970_);
v_stx_1971_ = lean_ctor_get(v_val_1966_, 1);
lean_inc(v_stx_1971_);
lean_dec(v_val_1966_);
v___x_1983_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__2));
v___x_1984_ = lean_name_eq(v_elaborator_1970_, v___x_1983_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1985_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6));
v___x_1986_ = lean_name_eq(v_elaborator_1970_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8));
v___x_1988_ = lean_name_eq(v_elaborator_1970_, v___x_1987_);
if (v___x_1988_ == 0)
{
lean_object* v_env_1989_; uint8_t v___x_1990_; lean_object* v_names_1992_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v_env_1989_ = lean_ctor_get(v___x_1958_, 0);
lean_inc_ref_n(v_env_1989_, 2);
lean_dec(v___x_1958_);
v___x_1990_ = 1;
v___x_1997_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
lean_inc(v_elaborator_1970_);
v___x_1998_ = l_Lean_Environment_contains(v_env_1989_, v_elaborator_1970_, v___x_1990_);
if (v___x_1998_ == 0)
{
lean_dec(v_elaborator_1970_);
v_names_1992_ = v___x_1997_;
goto v___jp_1991_;
}
else
{
lean_object* v___x_1999_; 
v___x_1999_ = lean_array_push(v___x_1997_, v_elaborator_1970_);
v_names_1992_ = v___x_1999_;
goto v___jp_1991_;
}
v___jp_1991_:
{
uint8_t v___x_1993_; uint8_t v___x_1994_; 
v___x_1993_ = 0;
v___x_1994_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_1963_, v___x_1993_);
if (v___x_1994_ == 0)
{
lean_dec_ref(v_env_1989_);
v___y_1973_ = v_names_1992_;
v___y_1974_ = v___x_1994_;
goto v___jp_1972_;
}
else
{
lean_object* v___x_1995_; uint8_t v___x_1996_; 
lean_inc(v_stx_1971_);
v___x_1995_ = l_Lean_Syntax_getKind(v_stx_1971_);
v___x_1996_ = l_Lean_Environment_contains(v_env_1989_, v___x_1995_, v___x_1990_);
v___y_1973_ = v_names_1992_;
v___y_1974_ = v___x_1996_;
goto v___jp_1972_;
}
}
}
else
{
lean_dec(v_stx_1971_);
lean_dec(v_elaborator_1970_);
lean_del_object(v___x_1968_);
lean_dec(v___x_1958_);
goto v___jp_1959_;
}
}
else
{
lean_dec(v_stx_1971_);
lean_dec(v_elaborator_1970_);
lean_del_object(v___x_1968_);
lean_dec(v___x_1958_);
goto v___jp_1959_;
}
}
else
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
lean_dec(v_stx_1971_);
lean_dec(v_elaborator_1970_);
lean_del_object(v___x_1968_);
lean_dec(v___x_1958_);
v___x_2000_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
v___x_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
return v___x_2001_;
}
v___jp_1972_:
{
if (v___y_1974_ == 0)
{
lean_object* v___x_1976_; 
lean_dec(v_stx_1971_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set_tag(v___x_1968_, 0);
lean_ctor_set(v___x_1968_, 0, v___y_1973_);
v___x_1976_ = v___x_1968_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___y_1973_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1978_ = l_Lean_Syntax_getKind(v_stx_1971_);
v___x_1979_ = lean_array_push(v___y_1973_, v___x_1978_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set_tag(v___x_1968_, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1979_);
v___x_1981_ = v___x_1968_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
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
}
else
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
lean_dec(v___x_1965_);
lean_dec(v___x_1958_);
v___x_2003_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
v___x_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
return v___x_2004_;
}
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_dec(v___x_1958_);
v___x_2005_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
v___x_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
return v___x_2006_;
}
v___jp_1959_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
v___x_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
return v___x_1961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___boxed(lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(v_a_2007_, v_a_2008_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames(lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(v_a_2011_, v_a_2015_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___boxed(lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames(v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
lean_dec_ref(v_a_2018_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(lean_object* v_as_2025_, size_t v_sz_2026_, size_t v_i_2027_, lean_object* v_b_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
uint8_t v___x_2035_; 
v___x_2035_ = lean_usize_dec_lt(v_i_2027_, v_sz_2026_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; 
v___x_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2036_, 0, v_b_2028_);
return v___x_2036_;
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2038_; 
v_a_2037_ = lean_array_uget_borrowed(v_as_2025_, v_i_2027_);
lean_inc(v_a_2037_);
v___x_2038_ = l_Lean_Server_locationLinksFromDecl(v_a_2037_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v___x_2040_; size_t v___x_2041_; size_t v___x_2042_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v___x_2040_ = l_Array_append___redArg(v_b_2028_, v_a_2039_);
lean_dec(v_a_2039_);
v___x_2041_ = ((size_t)1ULL);
v___x_2042_ = lean_usize_add(v_i_2027_, v___x_2041_);
v_i_2027_ = v___x_2042_;
v_b_2028_ = v___x_2040_;
goto _start;
}
else
{
lean_dec_ref(v_b_2028_);
return v___x_2038_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0___boxed(lean_object* v_as_2044_, lean_object* v_sz_2045_, lean_object* v_i_2046_, lean_object* v_b_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
size_t v_sz_boxed_2054_; size_t v_i_boxed_2055_; lean_object* v_res_2056_; 
v_sz_boxed_2054_ = lean_unbox_usize(v_sz_2045_);
lean_dec(v_sz_2045_);
v_i_boxed_2055_ = lean_unbox_usize(v_i_2046_);
lean_dec(v_i_2046_);
v_res_2056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_as_2044_, v_sz_boxed_2054_, v_i_boxed_2055_, v_b_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec_ref(v_as_2044_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(size_t v_sz_2057_, size_t v_i_2058_, lean_object* v_bs_2059_){
_start:
{
uint8_t v___x_2060_; 
v___x_2060_ = lean_usize_dec_lt(v_i_2058_, v_sz_2057_);
if (v___x_2060_ == 0)
{
return v_bs_2059_;
}
else
{
lean_object* v_v_2061_; lean_object* v_toLocationLink_2062_; lean_object* v_ident_x3f_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2076_; 
v_v_2061_ = lean_array_uget(v_bs_2059_, v_i_2058_);
v_toLocationLink_2062_ = lean_ctor_get(v_v_2061_, 0);
v_ident_x3f_2063_ = lean_ctor_get(v_v_2061_, 1);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_v_2061_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2065_ = v_v_2061_;
v_isShared_2066_ = v_isSharedCheck_2076_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_ident_x3f_2063_);
lean_inc(v_toLocationLink_2062_);
lean_dec(v_v_2061_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2076_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v_bs_x27_2068_; lean_object* v___x_2070_; 
v___x_2067_ = lean_unsigned_to_nat(0u);
v_bs_x27_2068_ = lean_array_uset(v_bs_2059_, v_i_2058_, v___x_2067_);
if (v_isShared_2066_ == 0)
{
v___x_2070_ = v___x_2065_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_toLocationLink_2062_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_ident_x3f_2063_);
v___x_2070_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
size_t v___x_2071_; size_t v___x_2072_; lean_object* v___x_2073_; 
lean_ctor_set_uint8(v___x_2070_, sizeof(void*)*2, v___x_2060_);
v___x_2071_ = ((size_t)1ULL);
v___x_2072_ = lean_usize_add(v_i_2058_, v___x_2071_);
v___x_2073_ = lean_array_uset(v_bs_x27_2068_, v_i_2058_, v___x_2070_);
v_i_2058_ = v___x_2072_;
v_bs_2059_ = v___x_2073_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1___boxed(lean_object* v_sz_2077_, lean_object* v_i_2078_, lean_object* v_bs_2079_){
_start:
{
size_t v_sz_boxed_2080_; size_t v_i_boxed_2081_; lean_object* v_res_2082_; 
v_sz_boxed_2080_ = lean_unbox_usize(v_sz_2077_);
lean_dec(v_sz_2077_);
v_i_boxed_2081_ = lean_unbox_usize(v_i_2078_);
lean_dec(v_i_2078_);
v_res_2082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(v_sz_boxed_2080_, v_i_boxed_2081_, v_bs_2079_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksDefault(lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v___x_2089_; lean_object* v_a_2090_; lean_object* v___x_2091_; size_t v_sz_2092_; size_t v___x_2093_; lean_object* v___x_2094_; 
v___x_2089_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(v_a_2083_, v_a_2087_);
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref(v___x_2089_);
v___x_2091_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v_sz_2092_ = lean_array_size(v_a_2090_);
v___x_2093_ = ((size_t)0ULL);
v___x_2094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_a_2090_, v_sz_2092_, v___x_2093_, v___x_2091_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
lean_dec(v_a_2090_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2104_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2104_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2104_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
size_t v_sz_2099_; lean_object* v___x_2100_; lean_object* v___x_2102_; 
v_sz_2099_ = lean_array_size(v_a_2095_);
v___x_2100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(v_sz_2099_, v___x_2093_, v_a_2095_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2100_);
v___x_2102_ = v___x_2097_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
else
{
return v___x_2094_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksDefault___boxed(lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_Server_locationLinksDefault(v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec(v_a_2107_);
lean_dec_ref(v_a_2106_);
lean_dec_ref(v_a_2105_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(lean_object* v_name_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; lean_object* v_env_2116_; lean_object* v___x_2117_; lean_object* v_toEnvExtension_2118_; lean_object* v_asyncMode_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2115_ = lean_st_ref_get(v___y_2113_);
v_env_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc_ref(v_env_2116_);
lean_dec(v___x_2115_);
v___x_2117_ = l_Lean_errorExplanationExt;
v_toEnvExtension_2118_ = lean_ctor_get(v___x_2117_, 0);
v_asyncMode_2119_ = lean_ctor_get(v_toEnvExtension_2118_, 2);
v___x_2120_ = lean_box(1);
v___x_2121_ = lean_box(0);
v___x_2122_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2120_, v___x_2117_, v_env_2116_, v_asyncMode_2119_, v___x_2121_);
v___x_2123_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2122_, v_name_2112_);
lean_dec(v___x_2122_);
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg___boxed(lean_object* v_name_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_name_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec(v_name_2125_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0(lean_object* v_name_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_name_2129_, v___y_2134_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___boxed(lean_object* v_name_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0(v_name_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v_name_2137_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromErrorNameInfo(lean_object* v_eni_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v_stx_2152_; lean_object* v_errorName_2153_; lean_object* v___x_2154_; lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2235_; 
v_stx_2152_ = lean_ctor_get(v_eni_2145_, 0);
v_errorName_2153_ = lean_ctor_get(v_eni_2145_, 1);
v___x_2154_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_errorName_2153_, v_a_2150_);
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2157_ = v___x_2154_;
v_isShared_2158_ = v_isSharedCheck_2235_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2154_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2235_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
if (lean_obj_tag(v_a_2155_) == 1)
{
lean_object* v_val_2159_; lean_object* v_declLoc_x3f_2160_; 
v_val_2159_ = lean_ctor_get(v_a_2155_, 0);
lean_inc(v_val_2159_);
lean_dec_ref_known(v_a_2155_, 1);
v_declLoc_x3f_2160_ = lean_ctor_get(v_val_2159_, 2);
lean_inc(v_declLoc_x3f_2160_);
lean_dec(v_val_2159_);
if (lean_obj_tag(v_declLoc_x3f_2160_) == 1)
{
lean_object* v_val_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2226_; 
lean_del_object(v___x_2157_);
v_val_2161_ = lean_ctor_get(v_declLoc_x3f_2160_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_declLoc_x3f_2160_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2163_ = v_declLoc_x3f_2160_;
v_isShared_2164_ = v_isSharedCheck_2226_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_val_2161_);
lean_dec(v_declLoc_x3f_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2226_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v_module_2165_; lean_object* v_range_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2225_; 
v_module_2165_ = lean_ctor_get(v_val_2161_, 0);
v_range_2166_ = lean_ctor_get(v_val_2161_, 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_val_2161_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2168_ = v_val_2161_;
v_isShared_2169_ = v_isSharedCheck_2225_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_range_2166_);
lean_inc(v_module_2165_);
lean_dec(v_val_2161_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2225_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_Server_documentUriFromModule_x3f(v_module_2165_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2207_; 
lean_del_object(v___x_2168_);
lean_del_object(v___x_2163_);
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2207_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2207_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
if (lean_obj_tag(v_a_2171_) == 1)
{
lean_object* v_val_2175_; lean_object* v___x_2176_; lean_object* v___y_2178_; uint8_t v___x_2189_; lean_object* v___x_2190_; 
v_val_2175_ = lean_ctor_get(v_a_2171_, 0);
lean_inc(v_val_2175_);
lean_dec_ref_known(v_a_2171_, 1);
v___x_2176_ = l_Lean_DeclarationRange_toLspRange(v_range_2166_);
v___x_2189_ = 1;
v___x_2190_ = l_Lean_Syntax_getRange_x3f(v_stx_2152_, v___x_2189_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v___x_2191_; 
v___x_2191_ = lean_box(0);
v___y_2178_ = v___x_2191_;
goto v___jp_2177_;
}
else
{
lean_object* v_doc_2192_; lean_object* v_val_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2202_; 
v_doc_2192_ = lean_ctor_get(v_a_2146_, 0);
v_val_2193_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2195_ = v___x_2190_;
v_isShared_2196_ = v_isSharedCheck_2202_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_val_2193_);
lean_dec(v___x_2190_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2202_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v_text_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
v_text_2197_ = lean_ctor_get(v_doc_2192_, 3);
lean_inc_ref(v_text_2197_);
v___x_2198_ = l_Lean_Syntax_Range_toLspRange(v_text_2197_, v_val_2193_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v___x_2198_);
v___x_2200_ = v___x_2195_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
v___y_2178_ = v___x_2200_;
goto v___jp_2177_;
}
}
}
v___jp_2177_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2187_; 
lean_inc_ref(v___x_2176_);
v___x_2179_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2179_, 0, v___y_2178_);
lean_ctor_set(v___x_2179_, 1, v_val_2175_);
lean_ctor_set(v___x_2179_, 2, v___x_2176_);
lean_ctor_set(v___x_2179_, 3, v___x_2176_);
v___x_2180_ = lean_box(0);
v___x_2181_ = 0;
v___x_2182_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2182_, 0, v___x_2179_);
lean_ctor_set(v___x_2182_, 1, v___x_2180_);
lean_ctor_set_uint8(v___x_2182_, sizeof(void*)*2, v___x_2181_);
v___x_2183_ = lean_unsigned_to_nat(1u);
v___x_2184_ = lean_mk_empty_array_with_capacity(v___x_2183_);
v___x_2185_ = lean_array_push(v___x_2184_, v___x_2182_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2185_);
v___x_2187_ = v___x_2173_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2205_; 
lean_dec(v_a_2171_);
lean_dec_ref(v_range_2166_);
v___x_2203_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2203_);
v___x_2205_ = v___x_2173_;
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
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2224_; 
lean_dec_ref(v_range_2166_);
v_a_2208_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2210_ = v___x_2170_;
v_isShared_2211_ = v_isSharedCheck_2224_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2170_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2224_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v_ref_2212_; lean_object* v___x_2213_; lean_object* v___x_2215_; 
v_ref_2212_ = lean_ctor_get(v_a_2149_, 5);
v___x_2213_ = lean_io_error_to_string(v_a_2208_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set_tag(v___x_2163_, 3);
lean_ctor_set(v___x_2163_, 0, v___x_2213_);
v___x_2215_ = v___x_2163_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2216_ = l_Lean_MessageData_ofFormat(v___x_2215_);
lean_inc(v_ref_2212_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 1, v___x_2216_);
lean_ctor_set(v___x_2168_, 0, v_ref_2212_);
v___x_2218_ = v___x_2168_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_ref_2212_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2220_; 
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v___x_2218_);
v___x_2220_ = v___x_2210_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
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
lean_object* v___x_2227_; lean_object* v___x_2229_; 
lean_dec(v_declLoc_x3f_2160_);
v___x_2227_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2227_);
v___x_2229_ = v___x_2157_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
else
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
lean_dec(v_a_2155_);
v___x_2231_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2231_);
v___x_2233_ = v___x_2157_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
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
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromErrorNameInfo___boxed(lean_object* v_eni_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_Server_locationLinksFromErrorNameInfo(v_eni_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_);
lean_dec(v_a_2241_);
lean_dec_ref(v_a_2240_);
lean_dec(v_a_2239_);
lean_dec_ref(v_a_2238_);
lean_dec_ref(v_a_2237_);
lean_dec_ref(v_eni_2236_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(lean_object* v_e_2244_, lean_object* v_a_2245_){
_start:
{
switch(lean_obj_tag(v_e_2244_))
{
case 4:
{
lean_object* v_declName_2247_; lean_object* v___x_2248_; 
v_declName_2247_ = lean_ctor_get(v_e_2244_, 0);
lean_inc(v_declName_2247_);
lean_dec_ref_known(v_e_2244_, 2);
v___x_2248_ = l_Lean_Meta_isInstance___redArg(v_declName_2247_, v_a_2245_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2265_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2251_ = v___x_2248_;
v_isShared_2252_ = v_isSharedCheck_2265_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2248_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2265_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
uint8_t v___x_2253_; uint8_t v___x_2254_; 
v___x_2253_ = lean_unbox(v_a_2249_);
lean_dec(v_a_2249_);
v___x_2254_ = lean_bool_not(v___x_2253_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2255_ = lean_unsigned_to_nat(1u);
v___x_2256_ = lean_mk_empty_array_with_capacity(v___x_2255_);
v___x_2257_ = lean_array_push(v___x_2256_, v_declName_2247_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2257_);
v___x_2259_ = v___x_2251_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2257_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
else
{
lean_object* v___x_2261_; lean_object* v___x_2263_; 
lean_dec(v_declName_2247_);
v___x_2261_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2261_);
v___x_2263_ = v___x_2251_;
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
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec(v_declName_2247_);
v_a_2266_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2248_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2248_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
case 5:
{
lean_object* v_fn_2274_; lean_object* v_arg_2275_; lean_object* v___x_2276_; 
v_fn_2274_ = lean_ctor_get(v_e_2244_, 0);
lean_inc_ref(v_fn_2274_);
v_arg_2275_ = lean_ctor_get(v_e_2244_, 1);
lean_inc_ref(v_arg_2275_);
lean_dec_ref_known(v_e_2244_, 2);
v___x_2276_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_fn_2274_, v_a_2245_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2278_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref_known(v___x_2276_, 1);
v___x_2278_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_arg_2275_, v_a_2245_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2287_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2281_ = v___x_2278_;
v_isShared_2282_ = v_isSharedCheck_2287_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2287_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2283_; lean_object* v___x_2285_; 
v___x_2283_ = l_Array_append___redArg(v_a_2279_, v_a_2277_);
lean_dec(v_a_2277_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v___x_2283_);
v___x_2285_ = v___x_2281_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
else
{
lean_dec(v_a_2277_);
return v___x_2278_;
}
}
else
{
lean_dec_ref(v_arg_2275_);
return v___x_2276_;
}
}
case 10:
{
lean_object* v_expr_2288_; 
v_expr_2288_ = lean_ctor_get(v_e_2244_, 1);
lean_inc_ref(v_expr_2288_);
lean_dec_ref_known(v_e_2244_, 2);
v_e_2244_ = v_expr_2288_;
goto _start;
}
default: 
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
lean_dec_ref(v_e_2244_);
v___x_2290_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
v___x_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
return v___x_2291_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg___boxed(lean_object* v_e_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_e_2292_, v_a_2293_);
lean_dec(v_a_2293_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances(lean_object* v_e_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_e_2296_, v_a_2301_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___boxed(lean_object* v_e_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances(v_e_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
lean_dec_ref(v_a_2305_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromInstanceProjection(lean_object* v_e_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = l_Lean_Expr_getAppFn(v_e_2312_);
v___x_2320_ = l_Lean_Expr_consumeMData(v___x_2319_);
lean_dec_ref(v___x_2319_);
if (lean_obj_tag(v___x_2320_) == 4)
{
lean_object* v_declName_2321_; lean_object* v___x_2322_; 
v_declName_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_declName_2321_);
lean_dec_ref_known(v___x_2320_, 2);
v___x_2322_ = l_Lean_Server_getInstanceProjectionArg_x3f(v_e_2312_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2357_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2357_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2357_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
if (lean_obj_tag(v_a_2323_) == 1)
{
lean_object* v_val_2327_; lean_object* v___x_2328_; 
lean_del_object(v___x_2325_);
v_val_2327_ = lean_ctor_get(v_a_2323_, 0);
lean_inc(v_val_2327_);
lean_dec_ref_known(v_a_2323_, 1);
v___x_2328_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_val_2327_, v_a_2317_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2330_; size_t v_sz_2331_; size_t v___x_2332_; lean_object* v___x_2333_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2328_, 1);
v___x_2330_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v_sz_2331_ = lean_array_size(v_a_2329_);
v___x_2332_ = ((size_t)0ULL);
v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_a_2329_, v_sz_2331_, v___x_2332_, v___x_2330_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
lean_dec(v_a_2329_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2335_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref_known(v___x_2333_, 1);
v___x_2335_ = l_Lean_Server_locationLinksFromDecl(v_declName_2321_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2344_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2344_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2344_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2340_; lean_object* v___x_2342_; 
v___x_2340_ = l_Array_append___redArg(v_a_2334_, v_a_2336_);
lean_dec(v_a_2336_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2340_);
v___x_2342_ = v___x_2338_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2340_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
else
{
lean_dec(v_a_2334_);
return v___x_2335_;
}
}
else
{
lean_dec(v_declName_2321_);
return v___x_2333_;
}
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec(v_declName_2321_);
v_a_2345_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2328_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2328_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2355_; 
lean_dec(v_a_2323_);
lean_dec(v_declName_2321_);
v___x_2353_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2353_);
v___x_2355_ = v___x_2325_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec(v_declName_2321_);
v_a_2358_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2322_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2322_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
lean_dec_ref(v___x_2320_);
lean_dec_ref(v_e_2312_);
v___x_2366_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
return v___x_2367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromInstanceProjection___boxed(lean_object* v_e_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_Server_locationLinksFromInstanceProjection(v_e_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec(v_a_2371_);
lean_dec_ref(v_a_2370_);
lean_dec_ref(v_a_2369_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(lean_object* v_as_2376_, size_t v_sz_2377_, size_t v_i_2378_, lean_object* v_b_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v_newLL_2387_; uint8_t v___x_2392_; 
v___x_2392_ = lean_usize_dec_lt(v_i_2378_, v_sz_2377_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; 
v___x_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2393_, 0, v_b_2379_);
return v___x_2393_;
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2395_; 
v_a_2394_ = lean_array_uget_borrowed(v_as_2376_, v_i_2378_);
v___x_2395_ = l_Lean_Expr_consumeMData(v_a_2394_);
switch(lean_obj_tag(v___x_2395_))
{
case 4:
{
lean_object* v_declName_2396_; lean_object* v___x_2397_; 
v_declName_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_declName_2396_);
lean_dec_ref_known(v___x_2395_, 2);
v___x_2397_ = l_Lean_Server_locationLinksFromDecl(v_declName_2396_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref_known(v___x_2397_, 1);
v_newLL_2387_ = v_a_2398_;
goto v___jp_2386_;
}
else
{
lean_dec_ref(v_b_2379_);
return v___x_2397_;
}
}
case 1:
{
lean_object* v_fvarId_2399_; lean_object* v___x_2400_; 
v_fvarId_2399_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_fvarId_2399_);
lean_dec_ref_known(v___x_2395_, 1);
v___x_2400_ = l_Lean_Server_locationLinksFromBinder___redArg(v_fvarId_2399_, v___y_2380_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2400_, 1);
v_newLL_2387_ = v_a_2401_;
goto v___jp_2386_;
}
else
{
lean_dec_ref(v_b_2379_);
return v___x_2400_;
}
}
default: 
{
lean_object* v___x_2402_; 
lean_dec_ref(v___x_2395_);
lean_inc(v_a_2394_);
v___x_2402_ = l_Lean_Server_locationLinksFromInstanceProjection(v_a_2394_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref_known(v___x_2402_, 1);
v_newLL_2387_ = v_a_2403_;
goto v___jp_2386_;
}
else
{
lean_dec_ref(v_b_2379_);
return v___x_2402_;
}
}
}
}
v___jp_2386_:
{
lean_object* v___x_2388_; size_t v___x_2389_; size_t v___x_2390_; 
v___x_2388_ = l_Array_append___redArg(v_b_2379_, v_newLL_2387_);
lean_dec_ref(v_newLL_2387_);
v___x_2389_ = ((size_t)1ULL);
v___x_2390_ = lean_usize_add(v_i_2378_, v___x_2389_);
v_i_2378_ = v___x_2390_;
v_b_2379_ = v___x_2388_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0___boxed(lean_object* v_as_2404_, lean_object* v_sz_2405_, lean_object* v_i_2406_, lean_object* v_b_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
size_t v_sz_boxed_2414_; size_t v_i_boxed_2415_; lean_object* v_res_2416_; 
v_sz_boxed_2414_ = lean_unbox_usize(v_sz_2405_);
lean_dec(v_sz_2405_);
v_i_boxed_2415_ = lean_unbox_usize(v_i_2406_);
lean_dec(v_i_2406_);
v_res_2416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(v_as_2404_, v_sz_boxed_2414_, v_i_boxed_2415_, v_b_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec_ref(v_as_2404_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromTermInfo(lean_object* v_ti_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
uint8_t v_kind_2424_; lean_object* v___x_2425_; 
v_kind_2424_ = lean_ctor_get_uint8(v_a_2418_, sizeof(void*)*4);
v___x_2425_ = l_Lean_Server_GoToKind_determineTargetExprs(v_kind_2424_, v_ti_2417_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2427_; size_t v_sz_2428_; size_t v___x_2429_; lean_object* v___x_2430_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___x_2425_, 1);
v___x_2427_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v_sz_2428_ = lean_array_size(v_a_2426_);
v___x_2429_ = ((size_t)0ULL);
v___x_2430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(v_a_2426_, v_sz_2428_, v___x_2429_, v___x_2427_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
lean_dec(v_a_2426_);
return v___x_2430_;
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
v_a_2431_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2425_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2425_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromTermInfo___boxed(lean_object* v_ti_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_Server_locationLinksFromTermInfo(v_ti_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec_ref(v_a_2440_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDelabTermInfo(lean_object* v_dti_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v_location_x3f_2454_; 
v_location_x3f_2454_ = lean_ctor_get(v_dti_2447_, 1);
lean_inc(v_location_x3f_2454_);
if (lean_obj_tag(v_location_x3f_2454_) == 1)
{
lean_object* v_val_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2524_; 
v_val_2455_ = lean_ctor_get(v_location_x3f_2454_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_location_x3f_2454_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2457_ = v_location_x3f_2454_;
v_isShared_2458_ = v_isSharedCheck_2524_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_val_2455_);
lean_dec(v_location_x3f_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2524_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v_toTermInfo_2459_; lean_object* v_module_2460_; lean_object* v_range_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2523_; 
v_toTermInfo_2459_ = lean_ctor_get(v_dti_2447_, 0);
v_module_2460_ = lean_ctor_get(v_val_2455_, 0);
v_range_2461_ = lean_ctor_get(v_val_2455_, 1);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_val_2455_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2463_ = v_val_2455_;
v_isShared_2464_ = v_isSharedCheck_2523_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_range_2461_);
lean_inc(v_module_2460_);
lean_dec(v_val_2455_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2523_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_Server_documentUriFromModule_x3f(v_module_2460_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2505_; 
lean_del_object(v___x_2463_);
lean_del_object(v___x_2457_);
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2468_ = v___x_2465_;
v_isShared_2469_ = v_isSharedCheck_2505_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2465_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2505_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
if (lean_obj_tag(v_a_2466_) == 1)
{
lean_object* v_val_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2503_; 
v_val_2470_ = lean_ctor_get(v_a_2466_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_a_2466_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2472_ = v_a_2466_;
v_isShared_2473_ = v_isSharedCheck_2503_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_val_2470_);
lean_dec(v_a_2466_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2503_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2474_; lean_object* v___y_2476_; lean_object* v___x_2488_; 
v___x_2474_ = l_Lean_DeclarationRange_toLspRange(v_range_2461_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set_tag(v___x_2472_, 13);
lean_ctor_set(v___x_2472_, 0, v_dti_2447_);
v___x_2488_ = v___x_2472_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_dti_2447_);
v___x_2488_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2487_;
}
v___jp_2475_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2485_; 
lean_inc_ref(v___x_2474_);
v___x_2477_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2477_, 0, v___y_2476_);
lean_ctor_set(v___x_2477_, 1, v_val_2470_);
lean_ctor_set(v___x_2477_, 2, v___x_2474_);
lean_ctor_set(v___x_2477_, 3, v___x_2474_);
v___x_2478_ = lean_box(0);
v___x_2479_ = 0;
v___x_2480_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2480_, 0, v___x_2477_);
lean_ctor_set(v___x_2480_, 1, v___x_2478_);
lean_ctor_set_uint8(v___x_2480_, sizeof(void*)*2, v___x_2479_);
v___x_2481_ = lean_unsigned_to_nat(1u);
v___x_2482_ = lean_mk_empty_array_with_capacity(v___x_2481_);
v___x_2483_ = lean_array_push(v___x_2482_, v___x_2480_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 0, v___x_2483_);
v___x_2485_ = v___x_2468_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2483_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
v_reusejp_2487_:
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Lean_Elab_Info_range_x3f(v___x_2488_);
lean_dec_ref(v___x_2488_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v___x_2490_; 
v___x_2490_ = lean_box(0);
v___y_2476_ = v___x_2490_;
goto v___jp_2475_;
}
else
{
lean_object* v_doc_2491_; lean_object* v_val_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2501_; 
v_doc_2491_ = lean_ctor_get(v_a_2448_, 0);
v_val_2492_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2494_ = v___x_2489_;
v_isShared_2495_ = v_isSharedCheck_2501_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_val_2492_);
lean_dec(v___x_2489_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2501_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v_text_2496_; lean_object* v___x_2497_; lean_object* v___x_2499_; 
v_text_2496_ = lean_ctor_get(v_doc_2491_, 3);
lean_inc_ref(v_text_2496_);
v___x_2497_ = l_Lean_Syntax_Range_toLspRange(v_text_2496_, v_val_2492_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v___x_2497_);
v___x_2499_ = v___x_2494_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
v___y_2476_ = v___x_2499_;
goto v___jp_2475_;
}
}
}
}
}
}
else
{
lean_object* v___x_2504_; 
lean_inc_ref(v_toTermInfo_2459_);
lean_del_object(v___x_2468_);
lean_dec(v_a_2466_);
lean_dec_ref(v_range_2461_);
lean_dec_ref(v_dti_2447_);
v___x_2504_ = l_Lean_Server_locationLinksFromTermInfo(v_toTermInfo_2459_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
return v___x_2504_;
}
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2522_; 
lean_dec_ref(v_range_2461_);
lean_dec_ref(v_dti_2447_);
v_a_2506_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2508_ = v___x_2465_;
v_isShared_2509_ = v_isSharedCheck_2522_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2465_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2522_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v_ref_2510_; lean_object* v___x_2511_; lean_object* v___x_2513_; 
v_ref_2510_ = lean_ctor_get(v_a_2451_, 5);
v___x_2511_ = lean_io_error_to_string(v_a_2506_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set_tag(v___x_2457_, 3);
lean_ctor_set(v___x_2457_, 0, v___x_2511_);
v___x_2513_ = v___x_2457_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2511_);
v___x_2513_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
lean_object* v___x_2514_; lean_object* v___x_2516_; 
v___x_2514_ = l_Lean_MessageData_ofFormat(v___x_2513_);
lean_inc(v_ref_2510_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 1, v___x_2514_);
lean_ctor_set(v___x_2463_, 0, v_ref_2510_);
v___x_2516_ = v___x_2463_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_ref_2510_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2518_; 
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 0, v___x_2516_);
v___x_2518_ = v___x_2508_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
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
lean_object* v_toTermInfo_2525_; lean_object* v___x_2526_; 
lean_dec(v_location_x3f_2454_);
v_toTermInfo_2525_ = lean_ctor_get(v_dti_2447_, 0);
lean_inc_ref(v_toTermInfo_2525_);
lean_dec_ref(v_dti_2447_);
v___x_2526_ = l_Lean_Server_locationLinksFromTermInfo(v_toTermInfo_2525_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
return v___x_2526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDelabTermInfo___boxed(lean_object* v_dti_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Lean_Server_locationLinksFromDelabTermInfo(v_dti_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec(v_a_2530_);
lean_dec_ref(v_a_2529_);
lean_dec_ref(v_a_2528_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(lean_object* v_e_2535_, lean_object* v___y_2536_){
_start:
{
uint8_t v___x_2538_; uint8_t v___x_2539_; 
v___x_2538_ = l_Lean_Expr_hasMVar(v_e_2535_);
v___x_2539_ = lean_bool_not(v___x_2538_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; lean_object* v_mctx_2541_; lean_object* v___x_2542_; lean_object* v_fst_2543_; lean_object* v_snd_2544_; lean_object* v___x_2545_; lean_object* v_cache_2546_; lean_object* v_zetaDeltaFVarIds_2547_; lean_object* v_postponed_2548_; lean_object* v_diag_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2558_; 
v___x_2540_ = lean_st_ref_get(v___y_2536_);
v_mctx_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc_ref(v_mctx_2541_);
lean_dec(v___x_2540_);
v___x_2542_ = l_Lean_instantiateMVarsCore(v_mctx_2541_, v_e_2535_);
v_fst_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_fst_2543_);
v_snd_2544_ = lean_ctor_get(v___x_2542_, 1);
lean_inc(v_snd_2544_);
lean_dec_ref(v___x_2542_);
v___x_2545_ = lean_st_ref_take(v___y_2536_);
v_cache_2546_ = lean_ctor_get(v___x_2545_, 1);
v_zetaDeltaFVarIds_2547_ = lean_ctor_get(v___x_2545_, 2);
v_postponed_2548_ = lean_ctor_get(v___x_2545_, 3);
v_diag_2549_ = lean_ctor_get(v___x_2545_, 4);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2558_ == 0)
{
lean_object* v_unused_2559_; 
v_unused_2559_ = lean_ctor_get(v___x_2545_, 0);
lean_dec(v_unused_2559_);
v___x_2551_ = v___x_2545_;
v_isShared_2552_ = v_isSharedCheck_2558_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_diag_2549_);
lean_inc(v_postponed_2548_);
lean_inc(v_zetaDeltaFVarIds_2547_);
lean_inc(v_cache_2546_);
lean_dec(v___x_2545_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2558_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v_snd_2544_);
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_snd_2544_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_cache_2546_);
lean_ctor_set(v_reuseFailAlloc_2557_, 2, v_zetaDeltaFVarIds_2547_);
lean_ctor_set(v_reuseFailAlloc_2557_, 3, v_postponed_2548_);
lean_ctor_set(v_reuseFailAlloc_2557_, 4, v_diag_2549_);
v___x_2554_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = lean_st_ref_set(v___y_2536_, v___x_2554_);
v___x_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2556_, 0, v_fst_2543_);
return v___x_2556_;
}
}
}
else
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v_e_2535_);
return v___x_2560_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg___boxed(lean_object* v_e_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(v_e_2561_, v___y_2562_);
lean_dec(v___y_2562_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0(lean_object* v_e_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(v_e_2565_, v___y_2568_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___boxed(lean_object* v_e_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0(v_e_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2574_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromFieldInfo(lean_object* v_fi_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_){
_start:
{
uint8_t v_kind_2588_; uint8_t v___x_2589_; uint8_t v___x_2590_; uint8_t v___x_2591_; 
v_kind_2588_ = lean_ctor_get_uint8(v_a_2582_, sizeof(void*)*4);
v___x_2589_ = 2;
v___x_2590_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_2588_, v___x_2589_);
v___x_2591_ = lean_bool_not(v___x_2590_);
if (v___x_2591_ == 0)
{
lean_object* v_val_2592_; lean_object* v___x_2593_; 
v_val_2592_ = lean_ctor_get(v_fi_2581_, 3);
lean_inc_ref(v_val_2592_);
lean_dec_ref(v_fi_2581_);
lean_inc(v_a_2586_);
lean_inc_ref(v_a_2585_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
v___x_2593_ = lean_infer_type(v_val_2592_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2595_; lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2608_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
v___x_2595_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(v_a_2594_, v_a_2584_);
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2598_ = v___x_2595_;
v_isShared_2599_ = v_isSharedCheck_2608_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2595_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2608_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = l_Lean_Expr_getAppFn(v_a_2596_);
lean_dec(v_a_2596_);
v___x_2601_ = l_Lean_Expr_constName_x3f(v___x_2600_);
lean_dec_ref(v___x_2600_);
if (lean_obj_tag(v___x_2601_) == 1)
{
lean_object* v_val_2602_; lean_object* v___x_2603_; 
lean_del_object(v___x_2598_);
v_val_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_val_2602_);
lean_dec_ref_known(v___x_2601_, 1);
v___x_2603_ = l_Lean_Server_locationLinksFromDecl(v_val_2602_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
return v___x_2603_;
}
else
{
lean_object* v___x_2604_; lean_object* v___x_2606_; 
lean_dec(v___x_2601_);
v___x_2604_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2604_);
v___x_2606_ = v___x_2598_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
v_a_2609_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2593_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2593_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
else
{
lean_object* v_projName_2617_; lean_object* v___x_2618_; 
v_projName_2617_ = lean_ctor_get(v_fi_2581_, 0);
lean_inc(v_projName_2617_);
lean_dec_ref(v_fi_2581_);
v___x_2618_ = l_Lean_Server_locationLinksFromDecl(v_projName_2617_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
return v___x_2618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromFieldInfo___boxed(lean_object* v_fi_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_Server_locationLinksFromFieldInfo(v_fi_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
lean_dec_ref(v_a_2620_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromOptionInfo(lean_object* v_i_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_){
_start:
{
lean_object* v_declName_2634_; lean_object* v___x_2635_; 
v_declName_2634_ = lean_ctor_get(v_i_2627_, 2);
lean_inc(v_declName_2634_);
lean_dec_ref(v_i_2627_);
v___x_2635_ = l_Lean_Server_locationLinksFromDecl(v_declName_2634_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromOptionInfo___boxed(lean_object* v_i_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_Lean_Server_locationLinksFromOptionInfo(v_i_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
lean_dec_ref(v_a_2638_);
lean_dec_ref(v_a_2637_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromCommandInfo___redArg(lean_object* v_i_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
uint8_t v___y_2649_; uint8_t v___y_2654_; lean_object* v_elaborator_2659_; 
v_elaborator_2659_ = lean_ctor_get(v_i_2644_, 0);
if (lean_obj_tag(v_elaborator_2659_) == 1)
{
lean_object* v_pre_2660_; 
v_pre_2660_ = lean_ctor_get(v_elaborator_2659_, 0);
if (lean_obj_tag(v_pre_2660_) == 0)
{
lean_object* v_str_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; 
v_str_2661_ = lean_ctor_get(v_elaborator_2659_, 1);
v___x_2662_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__3));
v___x_2663_ = lean_string_dec_eq(v_str_2661_, v___x_2662_);
v___y_2654_ = v___x_2663_;
goto v___jp_2653_;
}
else
{
uint8_t v___x_2664_; 
v___x_2664_ = 0;
v___y_2654_ = v___x_2664_;
goto v___jp_2653_;
}
}
else
{
uint8_t v___x_2665_; 
v___x_2665_ = 0;
v___y_2654_ = v___x_2665_;
goto v___jp_2653_;
}
v___jp_2648_:
{
if (v___y_2649_ == 0)
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Lean_Server_locationLinksFromImport___redArg(v_i_2644_, v_a_2645_, v_a_2646_);
return v___x_2650_;
}
else
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
lean_dec_ref(v_i_2644_);
v___x_2651_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
return v___x_2652_;
}
}
v___jp_2653_:
{
uint8_t v___x_2655_; 
v___x_2655_ = lean_bool_not(v___y_2654_);
if (v___x_2655_ == 0)
{
uint8_t v_kind_2656_; uint8_t v___x_2657_; uint8_t v___x_2658_; 
v_kind_2656_ = lean_ctor_get_uint8(v_a_2645_, sizeof(void*)*4);
v___x_2657_ = 2;
v___x_2658_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_2656_, v___x_2657_);
v___y_2649_ = v___x_2658_;
goto v___jp_2648_;
}
else
{
v___y_2649_ = v___x_2655_;
goto v___jp_2648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromCommandInfo___redArg___boxed(lean_object* v_i_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_Server_locationLinksFromCommandInfo___redArg(v_i_2666_, v_a_2667_, v_a_2668_);
lean_dec_ref(v_a_2668_);
lean_dec_ref(v_a_2667_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromCommandInfo(lean_object* v_i_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l_Lean_Server_locationLinksFromCommandInfo___redArg(v_i_2671_, v_a_2672_, v_a_2675_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromCommandInfo___boxed(lean_object* v_i_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Lean_Server_locationLinksFromCommandInfo(v_i_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec_ref(v_a_2680_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___lam__0(uint8_t v_kind_2687_, lean_object* v_ll_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
uint8_t v___y_2696_; uint8_t v___x_2708_; uint8_t v___x_2709_; 
v___x_2708_ = 0;
v___x_2709_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_2687_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; lean_object* v___x_2711_; uint8_t v___x_2712_; 
v___x_2710_ = lean_array_get_size(v_ll_2688_);
v___x_2711_ = lean_unsigned_to_nat(0u);
v___x_2712_ = lean_nat_dec_eq(v___x_2710_, v___x_2711_);
v___y_2696_ = v___x_2712_;
goto v___jp_2695_;
}
else
{
v___y_2696_ = v___x_2709_;
goto v___jp_2695_;
}
v___jp_2695_:
{
if (v___y_2696_ == 0)
{
lean_object* v___x_2697_; 
v___x_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2697_, 0, v_ll_2688_);
return v___x_2697_;
}
else
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Lean_Server_locationLinksDefault(v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2707_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2701_ = v___x_2698_;
v_isShared_2702_ = v_isSharedCheck_2707_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2698_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2707_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2703_ = l_Array_append___redArg(v_ll_2688_, v_a_2699_);
lean_dec(v_a_2699_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 0, v___x_2703_);
v___x_2705_ = v___x_2701_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
else
{
lean_dec_ref(v_ll_2688_);
return v___x_2698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___lam__0___boxed(lean_object* v_kind_2713_, lean_object* v_ll_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
uint8_t v_kind_boxed_2721_; lean_object* v_res_2722_; 
v_kind_boxed_2721_ = lean_unbox(v_kind_2713_);
v_res_2722_ = l_Lean_Server_locationLinksOfInfo___lam__0(v_kind_boxed_2721_, v_ll_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec_ref(v___y_2715_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___lam__1(lean_object* v_info_2723_, lean_object* v___f_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
switch(lean_obj_tag(v_info_2723_))
{
case 1:
{
lean_object* v_i_2731_; lean_object* v___x_2732_; 
v_i_2731_ = lean_ctor_get(v_info_2723_, 0);
lean_inc_ref(v_i_2731_);
lean_dec_ref_known(v_info_2723_, 1);
v___x_2732_ = l_Lean_Server_locationLinksFromTermInfo(v_i_2731_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2734_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
lean_inc(v___y_2729_);
lean_inc_ref(v___y_2728_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc_ref(v___y_2725_);
v___x_2734_ = lean_apply_7(v___f_2724_, v_a_2733_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, lean_box(0));
return v___x_2734_;
}
else
{
lean_dec_ref(v___f_2724_);
return v___x_2732_;
}
}
case 13:
{
lean_object* v_i_2735_; lean_object* v___x_2736_; 
v_i_2735_ = lean_ctor_get(v_info_2723_, 0);
lean_inc_ref(v_i_2735_);
lean_dec_ref_known(v_info_2723_, 1);
v___x_2736_ = l_Lean_Server_locationLinksFromDelabTermInfo(v_i_2735_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2738_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
lean_inc(v___y_2729_);
lean_inc_ref(v___y_2728_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc_ref(v___y_2725_);
v___x_2738_ = lean_apply_7(v___f_2724_, v_a_2737_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, lean_box(0));
return v___x_2738_;
}
else
{
lean_dec_ref(v___f_2724_);
return v___x_2736_;
}
}
case 7:
{
lean_object* v_i_2739_; lean_object* v___x_2740_; 
v_i_2739_ = lean_ctor_get(v_info_2723_, 0);
lean_inc_ref(v_i_2739_);
lean_dec_ref_known(v_info_2723_, 1);
v___x_2740_ = l_Lean_Server_locationLinksFromFieldInfo(v_i_2739_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2742_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2740_, 1);
lean_inc(v___y_2729_);
lean_inc_ref(v___y_2728_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc_ref(v___y_2725_);
v___x_2742_ = lean_apply_7(v___f_2724_, v_a_2741_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, lean_box(0));
return v___x_2742_;
}
else
{
lean_dec_ref(v___f_2724_);
return v___x_2740_;
}
}
case 5:
{
lean_object* v_i_2743_; lean_object* v___x_2744_; 
v_i_2743_ = lean_ctor_get(v_info_2723_, 0);
lean_inc_ref(v_i_2743_);
lean_dec_ref_known(v_info_2723_, 1);
v___x_2744_ = l_Lean_Server_locationLinksFromOptionInfo(v_i_2743_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2746_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref_known(v___x_2744_, 1);
lean_inc(v___y_2729_);
lean_inc_ref(v___y_2728_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc_ref(v___y_2725_);
v___x_2746_ = lean_apply_7(v___f_2724_, v_a_2745_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, lean_box(0));
return v___x_2746_;
}
else
{
lean_dec_ref(v___f_2724_);
return v___x_2744_;
}
}
case 3:
{
lean_object* v_i_2747_; lean_object* v___x_2748_; 
v_i_2747_ = lean_ctor_get(v_info_2723_, 0);
lean_inc_ref(v_i_2747_);
lean_dec_ref_known(v_info_2723_, 1);
v___x_2748_ = l_Lean_Server_locationLinksFromCommandInfo___redArg(v_i_2747_, v___y_2725_, v___y_2728_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2750_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v___x_2748_, 1);
lean_inc(v___y_2729_);
lean_inc_ref(v___y_2728_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc_ref(v___y_2725_);
v___x_2750_ = lean_apply_7(v___f_2724_, v_a_2749_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, lean_box(0));
return v___x_2750_;
}
else
{
lean_dec_ref(v___f_2724_);
return v___x_2748_;
}
}
case 6:
{
lean_object* v_i_2751_; lean_object* v___x_2752_; 
v_i_2751_ = lean_ctor_get(v_info_2723_, 0);
lean_inc_ref(v_i_2751_);
lean_dec_ref_known(v_info_2723_, 1);
v___x_2752_ = l_Lean_Server_locationLinksFromErrorNameInfo(v_i_2751_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec_ref(v_i_2751_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2754_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v___x_2752_, 1);
lean_inc(v___y_2729_);
lean_inc_ref(v___y_2728_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc_ref(v___y_2725_);
v___x_2754_ = lean_apply_7(v___f_2724_, v_a_2753_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, lean_box(0));
return v___x_2754_;
}
else
{
lean_dec_ref(v___f_2724_);
return v___x_2752_;
}
}
case 16:
{
lean_object* v_i_2755_; lean_object* v_name_2756_; lean_object* v___x_2757_; 
v_i_2755_ = lean_ctor_get(v_info_2723_, 0);
lean_inc_ref(v_i_2755_);
lean_dec_ref_known(v_info_2723_, 1);
v_name_2756_ = lean_ctor_get(v_i_2755_, 1);
lean_inc(v_name_2756_);
lean_dec_ref(v_i_2755_);
v___x_2757_ = l_Lean_Server_locationLinksFromDecl(v_name_2756_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2759_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_a_2758_);
lean_dec_ref_known(v___x_2757_, 1);
lean_inc(v___y_2729_);
lean_inc_ref(v___y_2728_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc_ref(v___y_2725_);
v___x_2759_ = lean_apply_7(v___f_2724_, v_a_2758_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, lean_box(0));
return v___x_2759_;
}
else
{
lean_dec_ref(v___f_2724_);
return v___x_2757_;
}
}
default: 
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
lean_dec_ref(v_info_2723_);
v___x_2760_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
lean_inc(v___y_2729_);
lean_inc_ref(v___y_2728_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc_ref(v___y_2725_);
v___x_2761_ = lean_apply_7(v___f_2724_, v___x_2760_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, lean_box(0));
return v___x_2761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___lam__1___boxed(lean_object* v_info_2762_, lean_object* v___f_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_Lean_Server_locationLinksOfInfo___lam__1(v_info_2762_, v___f_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec_ref(v___y_2764_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo(lean_object* v_doc_2771_, uint8_t v_kind_2772_, lean_object* v_ictx_2773_, lean_object* v_infoTree_x3f_2774_){
_start:
{
lean_object* v_ctx_2776_; lean_object* v_info_2777_; lean_object* v_children_2778_; lean_object* v___x_2779_; lean_object* v___f_2780_; lean_object* v___y_2781_; lean_object* v___x_2782_; lean_object* v_ctx_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v_ctx_2776_ = lean_ctor_get(v_ictx_2773_, 0);
lean_inc_ref(v_ctx_2776_);
v_info_2777_ = lean_ctor_get(v_ictx_2773_, 1);
lean_inc_ref_n(v_info_2777_, 3);
v_children_2778_ = lean_ctor_get(v_ictx_2773_, 2);
lean_inc_ref(v_children_2778_);
lean_dec_ref(v_ictx_2773_);
v___x_2779_ = lean_box(v_kind_2772_);
v___f_2780_ = lean_alloc_closure((void*)(l_Lean_Server_locationLinksOfInfo___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2780_, 0, v___x_2779_);
v___y_2781_ = lean_alloc_closure((void*)(l_Lean_Server_locationLinksOfInfo___lam__1___boxed), 8, 2);
lean_closure_set(v___y_2781_, 0, v_info_2777_);
lean_closure_set(v___y_2781_, 1, v___f_2780_);
v___x_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2782_, 0, v_info_2777_);
v_ctx_2783_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_ctx_2783_, 0, v_doc_2771_);
lean_ctor_set(v_ctx_2783_, 1, v_infoTree_x3f_2774_);
lean_ctor_set(v_ctx_2783_, 2, v___x_2782_);
lean_ctor_set(v_ctx_2783_, 3, v_children_2778_);
lean_ctor_set_uint8(v_ctx_2783_, sizeof(void*)*4, v_kind_2772_);
v___x_2784_ = l_Lean_Elab_Info_lctx(v_info_2777_);
lean_dec_ref(v_info_2777_);
v___x_2785_ = l_Lean_Server_GoToM_run___redArg(v_ctx_2783_, v_ctx_2776_, v___x_2784_, v___y_2781_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___boxed(lean_object* v_doc_2786_, lean_object* v_kind_2787_, lean_object* v_ictx_2788_, lean_object* v_infoTree_x3f_2789_, lean_object* v_a_2790_){
_start:
{
uint8_t v_kind_boxed_2791_; lean_object* v_res_2792_; 
v_kind_boxed_2791_ = lean_unbox(v_kind_2787_);
v_res_2792_ = l_Lean_Server_locationLinksOfInfo(v_doc_2786_, v_kind_boxed_2791_, v_ictx_2788_, v_infoTree_x3f_2789_);
return v_res_2792_;
}
}
lean_object* runtime_initialize_Lean_Server_Utils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_Internal(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ForEachExpr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_GoTo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Server_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_GoTo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_Utils(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_Internal(uint8_t builtin);
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_GoTo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_GoTo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_GoTo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_GoTo(builtin);
}
#ifdef __cplusplus
}
#endif
