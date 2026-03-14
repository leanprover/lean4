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
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
lean_object* lean_erase_macro_scopes(lean_object*);
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
static lean_once_cell_t l_Lean_Server_locationLinksFromImport___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_locationLinksFromImport___redArg___closed__6;
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
lean_dec_ref(v___x_114_);
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
uint8_t v___x_132_; 
v___x_132_ = l_Lean_Expr_hasMVar(v_e_129_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v_e_129_);
return v___x_133_;
}
else
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
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg___boxed(lean_object* v_e_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_e_154_, v___y_155_);
lean_dec(v___y_155_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0(lean_object* v_e_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_e_158_, v___y_160_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___boxed(lean_object* v_e_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0(v_e_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_determineTargetExprs___lam__0(lean_object* v_e_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_snd_180_; 
switch(lean_obj_tag(v_e_172_))
{
case 1:
{
lean_object* v___x_185_; 
v___x_185_ = lean_array_push(v___y_173_, v_e_172_);
v_snd_180_ = v___x_185_;
goto v___jp_179_;
}
case 4:
{
lean_object* v___x_186_; 
v___x_186_ = lean_array_push(v___y_173_, v_e_172_);
v_snd_180_ = v___x_186_;
goto v___jp_179_;
}
default: 
{
lean_dec_ref(v_e_172_);
v_snd_180_ = v___y_173_;
goto v___jp_179_;
}
}
v___jp_179_:
{
uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_181_ = 1;
v___x_182_ = lean_box(v___x_181_);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v_snd_180_);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_determineTargetExprs___lam__0___boxed(lean_object* v_e_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Server_GoToKind_determineTargetExprs___lam__0(v_e_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(lean_object* v_a_195_, lean_object* v_b_196_, lean_object* v_x_197_){
_start:
{
if (lean_obj_tag(v_x_197_) == 0)
{
lean_dec(v_b_196_);
lean_dec_ref(v_a_195_);
return v_x_197_;
}
else
{
lean_object* v_key_198_; lean_object* v_value_199_; lean_object* v_tail_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_212_; 
v_key_198_ = lean_ctor_get(v_x_197_, 0);
v_value_199_ = lean_ctor_get(v_x_197_, 1);
v_tail_200_ = lean_ctor_get(v_x_197_, 2);
v_isSharedCheck_212_ = !lean_is_exclusive(v_x_197_);
if (v_isSharedCheck_212_ == 0)
{
v___x_202_ = v_x_197_;
v_isShared_203_ = v_isSharedCheck_212_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_tail_200_);
lean_inc(v_value_199_);
lean_inc(v_key_198_);
lean_dec(v_x_197_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_212_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
uint8_t v___x_204_; 
v___x_204_ = lean_expr_eqv(v_key_198_, v_a_195_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_205_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(v_a_195_, v_b_196_, v_tail_200_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 2, v___x_205_);
v___x_207_ = v___x_202_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_key_198_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_value_199_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
else
{
lean_object* v___x_210_; 
lean_dec(v_value_199_);
lean_dec(v_key_198_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 1, v_b_196_);
lean_ctor_set(v___x_202_, 0, v_a_195_);
v___x_210_ = v___x_202_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_195_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_b_196_);
lean_ctor_set(v_reuseFailAlloc_211_, 2, v_tail_200_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(lean_object* v_a_213_, lean_object* v_x_214_){
_start:
{
if (lean_obj_tag(v_x_214_) == 0)
{
uint8_t v___x_215_; 
v___x_215_ = 0;
return v___x_215_;
}
else
{
lean_object* v_key_216_; lean_object* v_tail_217_; uint8_t v___x_218_; 
v_key_216_ = lean_ctor_get(v_x_214_, 0);
v_tail_217_ = lean_ctor_get(v_x_214_, 2);
v___x_218_ = lean_expr_eqv(v_key_216_, v_a_213_);
if (v___x_218_ == 0)
{
v_x_214_ = v_tail_217_;
goto _start;
}
else
{
return v___x_218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_220_, lean_object* v_x_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(v_a_220_, v_x_221_);
lean_dec(v_x_221_);
lean_dec_ref(v_a_220_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(lean_object* v_x_224_, lean_object* v_x_225_){
_start:
{
if (lean_obj_tag(v_x_225_) == 0)
{
return v_x_224_;
}
else
{
lean_object* v_key_226_; lean_object* v_value_227_; lean_object* v_tail_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_251_; 
v_key_226_ = lean_ctor_get(v_x_225_, 0);
v_value_227_ = lean_ctor_get(v_x_225_, 1);
v_tail_228_ = lean_ctor_get(v_x_225_, 2);
v_isSharedCheck_251_ = !lean_is_exclusive(v_x_225_);
if (v_isSharedCheck_251_ == 0)
{
v___x_230_ = v_x_225_;
v_isShared_231_ = v_isSharedCheck_251_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_tail_228_);
lean_inc(v_value_227_);
lean_inc(v_key_226_);
lean_dec(v_x_225_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_251_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v_fold_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; size_t v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_232_ = lean_array_get_size(v_x_224_);
v___x_233_ = l_Lean_Expr_hash(v_key_226_);
v___x_234_ = 32ULL;
v___x_235_ = lean_uint64_shift_right(v___x_233_, v___x_234_);
v_fold_236_ = lean_uint64_xor(v___x_233_, v___x_235_);
v___x_237_ = 16ULL;
v___x_238_ = lean_uint64_shift_right(v_fold_236_, v___x_237_);
v___x_239_ = lean_uint64_xor(v_fold_236_, v___x_238_);
v___x_240_ = lean_uint64_to_usize(v___x_239_);
v___x_241_ = lean_usize_of_nat(v___x_232_);
v___x_242_ = ((size_t)1ULL);
v___x_243_ = lean_usize_sub(v___x_241_, v___x_242_);
v___x_244_ = lean_usize_land(v___x_240_, v___x_243_);
v___x_245_ = lean_array_uget_borrowed(v_x_224_, v___x_244_);
lean_inc(v___x_245_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 2, v___x_245_);
v___x_247_ = v___x_230_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_key_226_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_value_227_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v___x_245_);
v___x_247_ = v_reuseFailAlloc_250_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_248_; 
v___x_248_ = lean_array_uset(v_x_224_, v___x_244_, v___x_247_);
v_x_224_ = v___x_248_;
v_x_225_ = v_tail_228_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6___redArg(lean_object* v_i_252_, lean_object* v_source_253_, lean_object* v_target_254_){
_start:
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = lean_array_get_size(v_source_253_);
v___x_256_ = lean_nat_dec_lt(v_i_252_, v___x_255_);
if (v___x_256_ == 0)
{
lean_dec_ref(v_source_253_);
lean_dec(v_i_252_);
return v_target_254_;
}
else
{
lean_object* v_es_257_; lean_object* v___x_258_; lean_object* v_source_259_; lean_object* v_target_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_es_257_ = lean_array_fget(v_source_253_, v_i_252_);
v___x_258_ = lean_box(0);
v_source_259_ = lean_array_fset(v_source_253_, v_i_252_, v___x_258_);
v_target_260_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(v_target_254_, v_es_257_);
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_nat_add(v_i_252_, v___x_261_);
lean_dec(v_i_252_);
v_i_252_ = v___x_262_;
v_source_253_ = v_source_259_;
v_target_254_ = v_target_260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5___redArg(lean_object* v_data_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v_nbuckets_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_265_ = lean_array_get_size(v_data_264_);
v___x_266_ = lean_unsigned_to_nat(2u);
v_nbuckets_267_ = lean_nat_mul(v___x_265_, v___x_266_);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_box(0);
v___x_270_ = lean_mk_array(v_nbuckets_267_, v___x_269_);
v___x_271_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6___redArg(v___x_268_, v_data_264_, v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2___redArg(lean_object* v_m_272_, lean_object* v_a_273_, lean_object* v_b_274_){
_start:
{
lean_object* v_size_275_; lean_object* v_buckets_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_319_; 
v_size_275_ = lean_ctor_get(v_m_272_, 0);
v_buckets_276_ = lean_ctor_get(v_m_272_, 1);
v_isSharedCheck_319_ = !lean_is_exclusive(v_m_272_);
if (v_isSharedCheck_319_ == 0)
{
v___x_278_ = v_m_272_;
v_isShared_279_ = v_isSharedCheck_319_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_buckets_276_);
lean_inc(v_size_275_);
lean_dec(v_m_272_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_319_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; uint64_t v___x_281_; uint64_t v___x_282_; uint64_t v___x_283_; uint64_t v_fold_284_; uint64_t v___x_285_; uint64_t v___x_286_; uint64_t v___x_287_; size_t v___x_288_; size_t v___x_289_; size_t v___x_290_; size_t v___x_291_; size_t v___x_292_; lean_object* v_bkt_293_; uint8_t v___x_294_; 
v___x_280_ = lean_array_get_size(v_buckets_276_);
v___x_281_ = l_Lean_Expr_hash(v_a_273_);
v___x_282_ = 32ULL;
v___x_283_ = lean_uint64_shift_right(v___x_281_, v___x_282_);
v_fold_284_ = lean_uint64_xor(v___x_281_, v___x_283_);
v___x_285_ = 16ULL;
v___x_286_ = lean_uint64_shift_right(v_fold_284_, v___x_285_);
v___x_287_ = lean_uint64_xor(v_fold_284_, v___x_286_);
v___x_288_ = lean_uint64_to_usize(v___x_287_);
v___x_289_ = lean_usize_of_nat(v___x_280_);
v___x_290_ = ((size_t)1ULL);
v___x_291_ = lean_usize_sub(v___x_289_, v___x_290_);
v___x_292_ = lean_usize_land(v___x_288_, v___x_291_);
v_bkt_293_ = lean_array_uget_borrowed(v_buckets_276_, v___x_292_);
v___x_294_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(v_a_273_, v_bkt_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v_size_x27_296_; lean_object* v___x_297_; lean_object* v_buckets_x27_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_295_ = lean_unsigned_to_nat(1u);
v_size_x27_296_ = lean_nat_add(v_size_275_, v___x_295_);
lean_dec(v_size_275_);
lean_inc(v_bkt_293_);
v___x_297_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_297_, 0, v_a_273_);
lean_ctor_set(v___x_297_, 1, v_b_274_);
lean_ctor_set(v___x_297_, 2, v_bkt_293_);
v_buckets_x27_298_ = lean_array_uset(v_buckets_276_, v___x_292_, v___x_297_);
v___x_299_ = lean_unsigned_to_nat(4u);
v___x_300_ = lean_nat_mul(v_size_x27_296_, v___x_299_);
v___x_301_ = lean_unsigned_to_nat(3u);
v___x_302_ = lean_nat_div(v___x_300_, v___x_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_array_get_size(v_buckets_x27_298_);
v___x_304_ = lean_nat_dec_le(v___x_302_, v___x_303_);
lean_dec(v___x_302_);
if (v___x_304_ == 0)
{
lean_object* v_val_305_; lean_object* v___x_307_; 
v_val_305_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5___redArg(v_buckets_x27_298_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 1, v_val_305_);
lean_ctor_set(v___x_278_, 0, v_size_x27_296_);
v___x_307_ = v___x_278_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_size_x27_296_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_val_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
else
{
lean_object* v___x_310_; 
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 1, v_buckets_x27_298_);
lean_ctor_set(v___x_278_, 0, v_size_x27_296_);
v___x_310_ = v___x_278_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_size_x27_296_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_buckets_x27_298_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
else
{
lean_object* v___x_312_; lean_object* v_buckets_x27_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
lean_inc(v_bkt_293_);
v___x_312_ = lean_box(0);
v_buckets_x27_313_ = lean_array_uset(v_buckets_276_, v___x_292_, v___x_312_);
v___x_314_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(v_a_273_, v_b_274_, v_bkt_293_);
v___x_315_ = lean_array_uset(v_buckets_x27_313_, v___x_292_, v___x_314_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 1, v___x_315_);
v___x_317_ = v___x_278_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_size_275_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(lean_object* v_a_320_, lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_321_) == 0)
{
lean_object* v___x_322_; 
v___x_322_ = lean_box(0);
return v___x_322_;
}
else
{
lean_object* v_key_323_; lean_object* v_value_324_; lean_object* v_tail_325_; uint8_t v___x_326_; 
v_key_323_ = lean_ctor_get(v_x_321_, 0);
v_value_324_ = lean_ctor_get(v_x_321_, 1);
v_tail_325_ = lean_ctor_get(v_x_321_, 2);
v___x_326_ = lean_expr_eqv(v_key_323_, v_a_320_);
if (v___x_326_ == 0)
{
v_x_321_ = v_tail_325_;
goto _start;
}
else
{
lean_object* v___x_328_; 
lean_inc(v_value_324_);
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v_value_324_);
return v___x_328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_a_329_, lean_object* v_x_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(v_a_329_, v_x_330_);
lean_dec(v_x_330_);
lean_dec_ref(v_a_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(lean_object* v_m_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_buckets_334_; lean_object* v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v_fold_339_; uint64_t v___x_340_; uint64_t v___x_341_; uint64_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_buckets_334_ = lean_ctor_get(v_m_332_, 1);
v___x_335_ = lean_array_get_size(v_buckets_334_);
v___x_336_ = l_Lean_Expr_hash(v_a_333_);
v___x_337_ = 32ULL;
v___x_338_ = lean_uint64_shift_right(v___x_336_, v___x_337_);
v_fold_339_ = lean_uint64_xor(v___x_336_, v___x_338_);
v___x_340_ = 16ULL;
v___x_341_ = lean_uint64_shift_right(v_fold_339_, v___x_340_);
v___x_342_ = lean_uint64_xor(v_fold_339_, v___x_341_);
v___x_343_ = lean_uint64_to_usize(v___x_342_);
v___x_344_ = lean_usize_of_nat(v___x_335_);
v___x_345_ = ((size_t)1ULL);
v___x_346_ = lean_usize_sub(v___x_344_, v___x_345_);
v___x_347_ = lean_usize_land(v___x_343_, v___x_346_);
v___x_348_ = lean_array_uget_borrowed(v_buckets_334_, v___x_347_);
v___x_349_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(v_a_333_, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg___boxed(lean_object* v_m_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(v_m_350_, v_a_351_);
lean_dec_ref(v_a_351_);
lean_dec_ref(v_m_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(lean_object* v_g_353_, lean_object* v_e_354_, lean_object* v_a_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_a_363_; lean_object* v_fst_364_; lean_object* v___y_370_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_st_ref_get(v_a_355_);
v___x_374_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(v___x_373_, v_e_354_);
lean_dec(v___x_373_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v___x_375_; 
lean_inc_ref(v_g_353_);
lean_inc(v___y_360_);
lean_inc_ref(v___y_359_);
lean_inc(v___y_358_);
lean_inc_ref(v___y_357_);
lean_inc_ref(v_e_354_);
v___x_375_ = lean_apply_7(v_g_353_, v_e_354_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, lean_box(0));
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v_fst_377_; lean_object* v_snd_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_423_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_376_);
lean_dec_ref(v___x_375_);
v_fst_377_ = lean_ctor_get(v_a_376_, 0);
v_snd_378_ = lean_ctor_get(v_a_376_, 1);
v_isSharedCheck_423_ = !lean_is_exclusive(v_a_376_);
if (v_isSharedCheck_423_ == 0)
{
v___x_380_ = v_a_376_;
v_isShared_381_ = v_isSharedCheck_423_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_snd_378_);
lean_inc(v_fst_377_);
lean_dec(v_a_376_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_423_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v_d_383_; lean_object* v_b_384_; lean_object* v___y_385_; uint8_t v___x_390_; 
v___x_390_ = lean_unbox(v_fst_377_);
lean_dec(v_fst_377_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_393_; 
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec_ref(v_g_353_);
v___x_391_ = lean_box(0);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_391_);
v___x_393_ = v___x_380_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_snd_378_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
v_a_363_ = v___x_393_;
v_fst_364_ = v___x_391_;
goto v___jp_362_;
}
}
else
{
switch(lean_obj_tag(v_e_354_))
{
case 7:
{
lean_object* v_binderType_395_; lean_object* v_body_396_; 
lean_del_object(v___x_380_);
v_binderType_395_ = lean_ctor_get(v_e_354_, 1);
v_body_396_ = lean_ctor_get(v_e_354_, 2);
lean_inc_ref(v_body_396_);
lean_inc_ref(v_binderType_395_);
v_d_383_ = v_binderType_395_;
v_b_384_ = v_body_396_;
v___y_385_ = v_a_355_;
goto v___jp_382_;
}
case 6:
{
lean_object* v_binderType_397_; lean_object* v_body_398_; 
lean_del_object(v___x_380_);
v_binderType_397_ = lean_ctor_get(v_e_354_, 1);
v_body_398_ = lean_ctor_get(v_e_354_, 2);
lean_inc_ref(v_body_398_);
lean_inc_ref(v_binderType_397_);
v_d_383_ = v_binderType_397_;
v_b_384_ = v_body_398_;
v___y_385_ = v_a_355_;
goto v___jp_382_;
}
case 8:
{
lean_object* v_type_399_; lean_object* v_value_400_; lean_object* v_body_401_; lean_object* v___x_402_; 
lean_del_object(v___x_380_);
v_type_399_ = lean_ctor_get(v_e_354_, 1);
v_value_400_ = lean_ctor_get(v_e_354_, 2);
v_body_401_ = lean_ctor_get(v_e_354_, 3);
lean_inc(v___y_360_);
lean_inc_ref(v___y_359_);
lean_inc(v___y_358_);
lean_inc_ref(v___y_357_);
lean_inc_ref(v_type_399_);
lean_inc_ref(v_g_353_);
v___x_402_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_353_, v_type_399_, v_a_355_, v_snd_378_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v_snd_404_; lean_object* v___x_405_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref(v___x_402_);
v_snd_404_ = lean_ctor_get(v_a_403_, 1);
lean_inc(v_snd_404_);
lean_dec(v_a_403_);
lean_inc(v___y_360_);
lean_inc_ref(v___y_359_);
lean_inc(v___y_358_);
lean_inc_ref(v___y_357_);
lean_inc_ref(v_value_400_);
lean_inc_ref(v_g_353_);
v___x_405_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_353_, v_value_400_, v_a_355_, v_snd_404_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v_snd_407_; lean_object* v___x_408_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref(v___x_405_);
v_snd_407_ = lean_ctor_get(v_a_406_, 1);
lean_inc(v_snd_407_);
lean_dec(v_a_406_);
lean_inc_ref(v_body_401_);
v___x_408_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_353_, v_body_401_, v_a_355_, v_snd_407_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
v___y_370_ = v___x_408_;
goto v___jp_369_;
}
else
{
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec_ref(v_g_353_);
v___y_370_ = v___x_405_;
goto v___jp_369_;
}
}
else
{
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec_ref(v_g_353_);
v___y_370_ = v___x_402_;
goto v___jp_369_;
}
}
case 5:
{
lean_object* v_fn_409_; lean_object* v_arg_410_; lean_object* v___x_411_; 
lean_del_object(v___x_380_);
v_fn_409_ = lean_ctor_get(v_e_354_, 0);
v_arg_410_ = lean_ctor_get(v_e_354_, 1);
lean_inc(v___y_360_);
lean_inc_ref(v___y_359_);
lean_inc(v___y_358_);
lean_inc_ref(v___y_357_);
lean_inc_ref(v_fn_409_);
lean_inc_ref(v_g_353_);
v___x_411_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_353_, v_fn_409_, v_a_355_, v_snd_378_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v_snd_413_; lean_object* v___x_414_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref(v___x_411_);
v_snd_413_ = lean_ctor_get(v_a_412_, 1);
lean_inc(v_snd_413_);
lean_dec(v_a_412_);
lean_inc_ref(v_arg_410_);
v___x_414_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_353_, v_arg_410_, v_a_355_, v_snd_413_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
v___y_370_ = v___x_414_;
goto v___jp_369_;
}
else
{
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec_ref(v_g_353_);
v___y_370_ = v___x_411_;
goto v___jp_369_;
}
}
case 10:
{
lean_object* v_expr_415_; lean_object* v___x_416_; 
lean_del_object(v___x_380_);
v_expr_415_ = lean_ctor_get(v_e_354_, 1);
lean_inc_ref(v_expr_415_);
v___x_416_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_353_, v_expr_415_, v_a_355_, v_snd_378_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
v___y_370_ = v___x_416_;
goto v___jp_369_;
}
case 11:
{
lean_object* v_struct_417_; lean_object* v___x_418_; 
lean_del_object(v___x_380_);
v_struct_417_ = lean_ctor_get(v_e_354_, 2);
lean_inc_ref(v_struct_417_);
v___x_418_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_353_, v_struct_417_, v_a_355_, v_snd_378_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
v___y_370_ = v___x_418_;
goto v___jp_369_;
}
default: 
{
lean_object* v___x_419_; lean_object* v___x_421_; 
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec_ref(v_g_353_);
v___x_419_ = lean_box(0);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_419_);
v___x_421_ = v___x_380_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_snd_378_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
v_a_363_ = v___x_421_;
v_fst_364_ = v___x_419_;
goto v___jp_362_;
}
}
}
}
v___jp_382_:
{
lean_object* v___x_386_; 
lean_inc(v___y_360_);
lean_inc_ref(v___y_359_);
lean_inc(v___y_358_);
lean_inc_ref(v___y_357_);
lean_inc_ref(v_g_353_);
v___x_386_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_353_, v_d_383_, v___y_385_, v_snd_378_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v_snd_388_; lean_object* v___x_389_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
lean_dec_ref(v___x_386_);
v_snd_388_ = lean_ctor_get(v_a_387_, 1);
lean_inc(v_snd_388_);
lean_dec(v_a_387_);
v___x_389_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_353_, v_b_384_, v___y_385_, v_snd_388_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
v___y_370_ = v___x_389_;
goto v___jp_369_;
}
else
{
lean_dec_ref(v_b_384_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec_ref(v_g_353_);
v___y_370_ = v___x_386_;
goto v___jp_369_;
}
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec_ref(v_e_354_);
lean_dec_ref(v_g_353_);
v_a_424_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_375_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_375_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
else
{
lean_object* v_val_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_440_; 
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec_ref(v_e_354_);
lean_dec_ref(v_g_353_);
v_val_432_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_440_ == 0)
{
v___x_434_ = v___x_374_;
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_val_432_);
lean_dec(v___x_374_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v_val_432_);
lean_ctor_set(v___x_436_, 1, v___y_356_);
if (v_isShared_435_ == 0)
{
lean_ctor_set_tag(v___x_434_, 0);
lean_ctor_set(v___x_434_, 0, v___x_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
v___jp_362_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_365_ = lean_st_ref_take(v_a_355_);
v___x_366_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2___redArg(v___x_365_, v_e_354_, v_fst_364_);
v___x_367_ = lean_st_ref_set(v_a_355_, v___x_366_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v_a_363_);
return v___x_368_;
}
v___jp_369_:
{
if (lean_obj_tag(v___y_370_) == 0)
{
lean_object* v_a_371_; lean_object* v_fst_372_; 
v_a_371_ = lean_ctor_get(v___y_370_, 0);
lean_inc(v_a_371_);
lean_dec_ref(v___y_370_);
v_fst_372_ = lean_ctor_get(v_a_371_, 0);
lean_inc(v_fst_372_);
v_a_363_ = v_a_371_;
v_fst_364_ = v_fst_372_;
goto v___jp_362_;
}
else
{
lean_dec_ref(v_e_354_);
return v___y_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1___boxed(lean_object* v_g_441_, lean_object* v_e_442_, lean_object* v_a_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_441_, v_e_442_, v_a_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
lean_dec(v_a_443_);
return v_res_450_;
}
}
static lean_object* _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__0(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = lean_box(0);
v___x_452_ = lean_unsigned_to_nat(16u);
v___x_453_ = lean_mk_array(v___x_452_, v___x_451_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__1(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = lean_obj_once(&l_Lean_Server_GoToKind_determineTargetExprs___closed__0, &l_Lean_Server_GoToKind_determineTargetExprs___closed__0_once, _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__0);
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___x_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_determineTargetExprs(uint8_t v_kind_460_, lean_object* v_ti_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
if (v_kind_460_ == 2)
{
lean_object* v_expr_467_; lean_object* v___x_468_; 
v_expr_467_ = lean_ctor_get(v_ti_461_, 3);
lean_inc_ref(v_expr_467_);
lean_dec_ref(v_ti_461_);
lean_inc(v_a_465_);
lean_inc_ref(v_a_464_);
lean_inc(v_a_463_);
lean_inc_ref(v_a_462_);
v___x_468_ = lean_infer_type(v_expr_467_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_470_; lean_object* v_a_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___f_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref(v___x_468_);
v___x_470_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_a_469_, v_a_463_);
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref(v___x_470_);
v___x_472_ = lean_obj_once(&l_Lean_Server_GoToKind_determineTargetExprs___closed__1, &l_Lean_Server_GoToKind_determineTargetExprs___closed__1_once, _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__1);
v___x_473_ = lean_st_mk_ref(v___x_472_);
v___f_474_ = ((lean_object*)(l_Lean_Server_GoToKind_determineTargetExprs___closed__2));
v___x_475_ = ((lean_object*)(l_Lean_Server_GoToKind_determineTargetExprs___closed__3));
v___x_476_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v___f_474_, v_a_471_, v___x_473_, v___x_475_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_486_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_486_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v_snd_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
v_snd_481_ = lean_ctor_get(v_a_477_, 1);
lean_inc(v_snd_481_);
lean_dec(v_a_477_);
v___x_482_ = lean_st_ref_get(v___x_473_);
lean_dec(v___x_473_);
lean_dec(v___x_482_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v_snd_481_);
v___x_484_ = v___x_479_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_snd_481_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_dec(v___x_473_);
v_a_487_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_476_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_476_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
v_a_495_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_468_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_468_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
else
{
lean_object* v_expr_503_; lean_object* v___x_504_; lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_515_; 
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec_ref(v_a_462_);
v_expr_503_ = lean_ctor_get(v_ti_461_, 3);
lean_inc_ref(v_expr_503_);
lean_dec_ref(v_ti_461_);
v___x_504_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_expr_503_, v_a_463_);
lean_dec(v_a_463_);
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_515_ == 0)
{
v___x_507_ = v___x_504_;
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_509_ = lean_unsigned_to_nat(1u);
v___x_510_ = lean_mk_empty_array_with_capacity(v___x_509_);
v___x_511_ = lean_array_push(v___x_510_, v_a_505_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_511_);
v___x_513_ = v___x_507_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
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
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_determineTargetExprs___boxed(lean_object* v_kind_516_, lean_object* v_ti_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
uint8_t v_kind_boxed_523_; lean_object* v_res_524_; 
v_kind_boxed_523_ = lean_unbox(v_kind_516_);
v_res_524_ = l_Lean_Server_GoToKind_determineTargetExprs(v_kind_boxed_523_, v_ti_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1(lean_object* v_00_u03b2_525_, lean_object* v_m_526_, lean_object* v_a_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(v_m_526_, v_a_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___boxed(lean_object* v_00_u03b2_529_, lean_object* v_m_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1(v_00_u03b2_529_, v_m_530_, v_a_531_);
lean_dec_ref(v_a_531_);
lean_dec_ref(v_m_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2(lean_object* v_00_u03b2_533_, lean_object* v_m_534_, lean_object* v_a_535_, lean_object* v_b_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2___redArg(v_m_534_, v_a_535_, v_b_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_538_, lean_object* v_a_539_, lean_object* v_x_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(v_a_539_, v_x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_542_, lean_object* v_a_543_, lean_object* v_x_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2(v_00_u03b2_542_, v_a_543_, v_x_544_);
lean_dec(v_x_544_);
lean_dec_ref(v_a_543_);
return v_res_545_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_546_, lean_object* v_a_547_, lean_object* v_x_548_){
_start:
{
uint8_t v___x_549_; 
v___x_549_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(v_a_547_, v_x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_550_, lean_object* v_a_551_, lean_object* v_x_552_){
_start:
{
uint8_t v_res_553_; lean_object* v_r_554_; 
v_res_553_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4(v_00_u03b2_550_, v_a_551_, v_x_552_);
lean_dec(v_x_552_);
lean_dec_ref(v_a_551_);
v_r_554_ = lean_box(v_res_553_);
return v_r_554_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_555_, lean_object* v_data_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5___redArg(v_data_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_558_, lean_object* v_a_559_, lean_object* v_b_560_, lean_object* v_x_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(v_a_559_, v_b_560_, v_x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_563_, lean_object* v_i_564_, lean_object* v_source_565_, lean_object* v_target_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6___redArg(v_i_564_, v_source_565_, v_target_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_568_, lean_object* v_x_569_, lean_object* v_x_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(v_x_569_, v_x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(lean_object* v_e_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_st_ref_get(v_a_576_);
v___x_579_ = l_Lean_Expr_getAppFn_x27(v_e_572_);
if (lean_obj_tag(v___x_579_) == 4)
{
lean_object* v_declName_580_; lean_object* v_env_581_; lean_object* v___x_582_; 
v_declName_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_declName_580_);
lean_dec_ref(v___x_579_);
v_env_581_ = lean_ctor_get(v___x_578_, 0);
lean_inc_ref(v_env_581_);
lean_dec(v___x_578_);
v___x_582_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_581_, v_declName_580_);
if (lean_obj_tag(v___x_582_) == 1)
{
lean_object* v_val_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_592_; 
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
v_val_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_592_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_592_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_val_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_592_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v_e_572_);
lean_ctor_set(v___x_587_, 1, v_val_583_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_587_);
v___x_589_ = v___x_585_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_591_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; 
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
}
else
{
uint8_t v___x_593_; lean_object* v___x_594_; 
lean_dec(v___x_582_);
v___x_593_ = 0;
lean_inc(v_a_576_);
lean_inc_ref(v_a_575_);
lean_inc(v_a_574_);
lean_inc_ref(v_a_573_);
v___x_594_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_572_, v___x_593_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_605_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_605_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_605_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_605_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
if (lean_obj_tag(v_a_595_) == 1)
{
lean_object* v_val_599_; 
lean_del_object(v___x_597_);
v_val_599_ = lean_ctor_get(v_a_595_, 0);
lean_inc(v_val_599_);
lean_dec_ref(v_a_595_);
v_e_572_ = v_val_599_;
goto _start;
}
else
{
lean_object* v___x_601_; lean_object* v___x_603_; 
lean_dec(v_a_595_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
v___x_601_ = lean_box(0);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_601_);
v___x_603_ = v___x_597_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
v_a_606_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_594_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_594_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; 
lean_dec_ref(v___x_579_);
lean_dec(v___x_578_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec_ref(v_e_572_);
v___x_614_ = lean_box(0);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f___boxed(lean_object* v_e_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(v_e_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
return v_res_622_;
}
}
static uint64_t _init_l_Lean_Server_getInstanceProjectionArg_x3f___closed__0(void){
_start:
{
uint8_t v___x_623_; uint64_t v___x_624_; 
v___x_623_ = 2;
v___x_624_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_623_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_Server_getInstanceProjectionArg_x3f___closed__1(void){
_start:
{
lean_object* v___x_625_; lean_object* v_dummy_626_; 
v___x_625_ = lean_box(0);
v_dummy_626_ = l_Lean_Expr_sort___override(v___x_625_);
return v_dummy_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_getInstanceProjectionArg_x3f(lean_object* v_e_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v___x_633_; uint8_t v_foApprox_634_; uint8_t v_ctxApprox_635_; uint8_t v_quasiPatternApprox_636_; uint8_t v_constApprox_637_; uint8_t v_isDefEqStuckEx_638_; uint8_t v_unificationHints_639_; uint8_t v_proofIrrelevance_640_; uint8_t v_assignSyntheticOpaque_641_; uint8_t v_offsetCnstrs_642_; uint8_t v_etaStruct_643_; uint8_t v_univApprox_644_; uint8_t v_iota_645_; uint8_t v_beta_646_; uint8_t v_proj_647_; uint8_t v_zeta_648_; uint8_t v_zetaDelta_649_; uint8_t v_zetaUnused_650_; uint8_t v_zetaHave_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_735_; 
v___x_633_ = l_Lean_Meta_Context_config(v_a_628_);
v_foApprox_634_ = lean_ctor_get_uint8(v___x_633_, 0);
v_ctxApprox_635_ = lean_ctor_get_uint8(v___x_633_, 1);
v_quasiPatternApprox_636_ = lean_ctor_get_uint8(v___x_633_, 2);
v_constApprox_637_ = lean_ctor_get_uint8(v___x_633_, 3);
v_isDefEqStuckEx_638_ = lean_ctor_get_uint8(v___x_633_, 4);
v_unificationHints_639_ = lean_ctor_get_uint8(v___x_633_, 5);
v_proofIrrelevance_640_ = lean_ctor_get_uint8(v___x_633_, 6);
v_assignSyntheticOpaque_641_ = lean_ctor_get_uint8(v___x_633_, 7);
v_offsetCnstrs_642_ = lean_ctor_get_uint8(v___x_633_, 8);
v_etaStruct_643_ = lean_ctor_get_uint8(v___x_633_, 10);
v_univApprox_644_ = lean_ctor_get_uint8(v___x_633_, 11);
v_iota_645_ = lean_ctor_get_uint8(v___x_633_, 12);
v_beta_646_ = lean_ctor_get_uint8(v___x_633_, 13);
v_proj_647_ = lean_ctor_get_uint8(v___x_633_, 14);
v_zeta_648_ = lean_ctor_get_uint8(v___x_633_, 15);
v_zetaDelta_649_ = lean_ctor_get_uint8(v___x_633_, 16);
v_zetaUnused_650_ = lean_ctor_get_uint8(v___x_633_, 17);
v_zetaHave_651_ = lean_ctor_get_uint8(v___x_633_, 18);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_735_ == 0)
{
v___x_653_ = v___x_633_;
v_isShared_654_ = v_isSharedCheck_735_;
goto v_resetjp_652_;
}
else
{
lean_dec(v___x_633_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_735_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
uint8_t v_trackZetaDelta_655_; lean_object* v_zetaDeltaSet_656_; lean_object* v_lctx_657_; lean_object* v_localInstances_658_; lean_object* v_defEqCtx_x3f_659_; lean_object* v_synthPendingDepth_660_; lean_object* v_canUnfold_x3f_661_; uint8_t v_univApprox_662_; uint8_t v_inTypeClassResolution_663_; uint8_t v_cacheInferType_664_; uint8_t v___x_665_; lean_object* v_config_667_; 
v_trackZetaDelta_655_ = lean_ctor_get_uint8(v_a_628_, sizeof(void*)*7);
v_zetaDeltaSet_656_ = lean_ctor_get(v_a_628_, 1);
lean_inc(v_zetaDeltaSet_656_);
v_lctx_657_ = lean_ctor_get(v_a_628_, 2);
lean_inc_ref(v_lctx_657_);
v_localInstances_658_ = lean_ctor_get(v_a_628_, 3);
lean_inc_ref(v_localInstances_658_);
v_defEqCtx_x3f_659_ = lean_ctor_get(v_a_628_, 4);
lean_inc(v_defEqCtx_x3f_659_);
v_synthPendingDepth_660_ = lean_ctor_get(v_a_628_, 5);
lean_inc(v_synthPendingDepth_660_);
v_canUnfold_x3f_661_ = lean_ctor_get(v_a_628_, 6);
lean_inc(v_canUnfold_x3f_661_);
v_univApprox_662_ = lean_ctor_get_uint8(v_a_628_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_663_ = lean_ctor_get_uint8(v_a_628_, sizeof(void*)*7 + 2);
v_cacheInferType_664_ = lean_ctor_get_uint8(v_a_628_, sizeof(void*)*7 + 3);
v___x_665_ = 2;
if (v_isShared_654_ == 0)
{
v_config_667_ = v___x_653_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, 0, v_foApprox_634_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, 1, v_ctxApprox_635_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, 2, v_quasiPatternApprox_636_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, 3, v_constApprox_637_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, 4, v_isDefEqStuckEx_638_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, 5, v_unificationHints_639_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, 6, v_proofIrrelevance_640_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, 7, v_assignSyntheticOpaque_641_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, 8, v_offsetCnstrs_642_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, 10, v_etaStruct_643_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, 11, v_univApprox_644_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, 12, v_iota_645_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, 13, v_beta_646_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, 14, v_proj_647_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, 15, v_zeta_648_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, 16, v_zetaDelta_649_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, 17, v_zetaUnused_650_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, 18, v_zetaHave_651_);
v_config_667_ = v_reuseFailAlloc_734_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
uint64_t v___x_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_726_; 
lean_ctor_set_uint8(v_config_667_, 9, v___x_665_);
v___x_668_ = l_Lean_Meta_Context_configKey(v_a_628_);
v_isSharedCheck_726_ = !lean_is_exclusive(v_a_628_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; lean_object* v_unused_728_; lean_object* v_unused_729_; lean_object* v_unused_730_; lean_object* v_unused_731_; lean_object* v_unused_732_; lean_object* v_unused_733_; 
v_unused_727_ = lean_ctor_get(v_a_628_, 6);
lean_dec(v_unused_727_);
v_unused_728_ = lean_ctor_get(v_a_628_, 5);
lean_dec(v_unused_728_);
v_unused_729_ = lean_ctor_get(v_a_628_, 4);
lean_dec(v_unused_729_);
v_unused_730_ = lean_ctor_get(v_a_628_, 3);
lean_dec(v_unused_730_);
v_unused_731_ = lean_ctor_get(v_a_628_, 2);
lean_dec(v_unused_731_);
v_unused_732_ = lean_ctor_get(v_a_628_, 1);
lean_dec(v_unused_732_);
v_unused_733_ = lean_ctor_get(v_a_628_, 0);
lean_dec(v_unused_733_);
v___x_670_ = v_a_628_;
v_isShared_671_ = v_isSharedCheck_726_;
goto v_resetjp_669_;
}
else
{
lean_dec(v_a_628_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_726_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
uint64_t v___x_672_; uint64_t v___x_673_; uint64_t v___x_674_; uint64_t v___x_675_; uint64_t v_key_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_672_ = 2ULL;
v___x_673_ = lean_uint64_shift_right(v___x_668_, v___x_672_);
v___x_674_ = lean_uint64_shift_left(v___x_673_, v___x_672_);
v___x_675_ = lean_uint64_once(&l_Lean_Server_getInstanceProjectionArg_x3f___closed__0, &l_Lean_Server_getInstanceProjectionArg_x3f___closed__0_once, _init_l_Lean_Server_getInstanceProjectionArg_x3f___closed__0);
v_key_676_ = lean_uint64_lor(v___x_674_, v___x_675_);
v___x_677_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_677_, 0, v_config_667_);
lean_ctor_set_uint64(v___x_677_, sizeof(void*)*1, v_key_676_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_677_);
v___x_679_ = v___x_670_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_zetaDeltaSet_656_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v_lctx_657_);
lean_ctor_set(v_reuseFailAlloc_725_, 3, v_localInstances_658_);
lean_ctor_set(v_reuseFailAlloc_725_, 4, v_defEqCtx_x3f_659_);
lean_ctor_set(v_reuseFailAlloc_725_, 5, v_synthPendingDepth_660_);
lean_ctor_set(v_reuseFailAlloc_725_, 6, v_canUnfold_x3f_661_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, sizeof(void*)*7, v_trackZetaDelta_655_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, sizeof(void*)*7 + 1, v_univApprox_662_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, sizeof(void*)*7 + 2, v_inTypeClassResolution_663_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, sizeof(void*)*7 + 3, v_cacheInferType_664_);
v___x_679_ = v_reuseFailAlloc_725_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; 
v___x_680_ = l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(v_e_627_, v___x_679_, v_a_629_, v_a_630_, v_a_631_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_716_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_716_ == 0)
{
v___x_683_ = v___x_680_;
v_isShared_684_ = v_isSharedCheck_716_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_680_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_716_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
if (lean_obj_tag(v_a_681_) == 1)
{
lean_object* v_val_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_711_; 
v_val_685_ = lean_ctor_get(v_a_681_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v_a_681_);
if (v_isSharedCheck_711_ == 0)
{
v___x_687_ = v_a_681_;
v_isShared_688_ = v_isSharedCheck_711_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_val_685_);
lean_dec(v_a_681_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_711_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_snd_689_; lean_object* v_fst_690_; lean_object* v_numParams_691_; lean_object* v_dummy_692_; lean_object* v_nargs_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_snd_689_ = lean_ctor_get(v_val_685_, 1);
lean_inc(v_snd_689_);
v_fst_690_ = lean_ctor_get(v_val_685_, 0);
lean_inc(v_fst_690_);
lean_dec(v_val_685_);
v_numParams_691_ = lean_ctor_get(v_snd_689_, 1);
lean_inc(v_numParams_691_);
lean_dec(v_snd_689_);
v_dummy_692_ = lean_obj_once(&l_Lean_Server_getInstanceProjectionArg_x3f___closed__1, &l_Lean_Server_getInstanceProjectionArg_x3f___closed__1_once, _init_l_Lean_Server_getInstanceProjectionArg_x3f___closed__1);
v_nargs_693_ = l_Lean_Expr_getAppNumArgs(v_fst_690_);
lean_inc(v_nargs_693_);
v___x_694_ = lean_mk_array(v_nargs_693_, v_dummy_692_);
v___x_695_ = lean_unsigned_to_nat(1u);
v___x_696_ = lean_nat_sub(v_nargs_693_, v___x_695_);
lean_dec(v_nargs_693_);
v___x_697_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_690_, v___x_694_, v___x_696_);
v___x_698_ = lean_array_get_size(v___x_697_);
v___x_699_ = lean_nat_dec_lt(v_numParams_691_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_702_; 
lean_dec_ref(v___x_697_);
lean_dec(v_numParams_691_);
lean_del_object(v___x_687_);
v___x_700_ = lean_box(0);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_700_);
v___x_702_ = v___x_683_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
else
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = lean_array_fget(v___x_697_, v_numParams_691_);
lean_dec(v_numParams_691_);
lean_dec_ref(v___x_697_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_704_);
v___x_706_ = v___x_687_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_708_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_706_);
v___x_708_ = v___x_683_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
else
{
lean_object* v___x_712_; lean_object* v___x_714_; 
lean_dec(v_a_681_);
v___x_712_ = lean_box(0);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_712_);
v___x_714_ = v___x_683_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
v_a_717_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_680_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_680_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_getInstanceProjectionArg_x3f___boxed(lean_object* v_e_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Server_getInstanceProjectionArg_x3f(v_e_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isInstanceProjection(lean_object* v_e_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Server_getInstanceProjectionArg_x3f(v_e_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_764_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_764_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_764_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_764_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
if (lean_obj_tag(v_a_750_) == 0)
{
uint8_t v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_754_ = 0;
v___x_755_ = lean_box(v___x_754_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_755_);
v___x_757_ = v___x_752_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
else
{
uint8_t v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
lean_dec_ref(v_a_750_);
v___x_759_ = 1;
v___x_760_ = lean_box(v___x_759_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_760_);
v___x_762_ = v___x_752_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
v_a_765_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_749_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_749_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isInstanceProjection___boxed(lean_object* v_e_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_Server_isInstanceProjection(v_e_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isInstanceProjectionInfoFor(uint8_t v_kind_780_, lean_object* v_ti1_781_, lean_object* v_ti2_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
uint8_t v___x_788_; uint8_t v___x_789_; 
v___x_788_ = 2;
v___x_789_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_780_, v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v_toElabInfo_790_; lean_object* v_expr_791_; lean_object* v_stx_792_; uint8_t v___x_793_; lean_object* v___x_794_; 
v_toElabInfo_790_ = lean_ctor_get(v_ti1_781_, 0);
lean_inc_ref(v_toElabInfo_790_);
v_expr_791_ = lean_ctor_get(v_ti1_781_, 3);
lean_inc_ref(v_expr_791_);
lean_dec_ref(v_ti1_781_);
v_stx_792_ = lean_ctor_get(v_toElabInfo_790_, 1);
lean_inc(v_stx_792_);
lean_dec_ref(v_toElabInfo_790_);
v___x_793_ = 1;
v___x_794_ = l_Lean_Syntax_getPos_x3f(v_stx_792_, v___x_793_);
lean_dec(v_stx_792_);
if (lean_obj_tag(v___x_794_) == 1)
{
lean_object* v_toElabInfo_795_; lean_object* v_val_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_852_; 
v_toElabInfo_795_ = lean_ctor_get(v_ti2_782_, 0);
lean_inc_ref(v_toElabInfo_795_);
v_val_796_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_852_ == 0)
{
v___x_798_ = v___x_794_;
v_isShared_799_ = v_isSharedCheck_852_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_val_796_);
lean_dec(v___x_794_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_852_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v_expr_800_; lean_object* v_stx_801_; lean_object* v___x_802_; 
v_expr_800_ = lean_ctor_get(v_ti2_782_, 3);
lean_inc_ref(v_expr_800_);
lean_dec_ref(v_ti2_782_);
v_stx_801_ = lean_ctor_get(v_toElabInfo_795_, 1);
lean_inc(v_stx_801_);
lean_dec_ref(v_toElabInfo_795_);
v___x_802_ = l_Lean_Syntax_getPos_x3f(v_stx_801_, v___x_793_);
lean_dec(v_stx_801_);
if (lean_obj_tag(v___x_802_) == 1)
{
lean_object* v_val_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_847_; 
lean_del_object(v___x_798_);
v_val_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_847_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_847_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_val_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_847_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
uint8_t v___x_807_; 
v___x_807_ = lean_nat_dec_eq(v_val_796_, v_val_803_);
lean_dec(v_val_803_);
lean_dec(v_val_796_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_810_; 
lean_dec_ref(v_expr_800_);
lean_dec_ref(v_expr_791_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
v___x_808_ = lean_box(v___x_789_);
if (v_isShared_806_ == 0)
{
lean_ctor_set_tag(v___x_805_, 0);
lean_ctor_set(v___x_805_, 0, v___x_808_);
v___x_810_ = v___x_805_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
else
{
if (v___x_789_ == 0)
{
lean_object* v___x_812_; lean_object* v_a_813_; lean_object* v___x_814_; lean_object* v_a_815_; lean_object* v___x_816_; 
lean_del_object(v___x_805_);
v___x_812_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_expr_791_, v_a_784_);
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref(v___x_812_);
v___x_814_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_expr_800_, v_a_784_);
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref(v___x_814_);
lean_inc(v_a_786_);
lean_inc_ref(v_a_785_);
lean_inc(v_a_784_);
lean_inc_ref(v_a_783_);
lean_inc(v_a_813_);
v___x_816_ = l_Lean_Server_isInstanceProjection(v_a_813_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_818_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref(v___x_816_);
lean_inc(v_a_815_);
v___x_818_ = l_Lean_Server_isInstanceProjection(v_a_815_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_842_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_842_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_842_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_842_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
uint8_t v___y_824_; uint8_t v___x_841_; 
v___x_841_ = lean_unbox(v_a_817_);
lean_dec(v_a_817_);
if (v___x_841_ == 0)
{
v___y_824_ = v___x_807_;
goto v___jp_823_;
}
else
{
v___y_824_ = v___x_789_;
goto v___jp_823_;
}
v___jp_823_:
{
if (v___y_824_ == 0)
{
uint8_t v___x_825_; 
v___x_825_ = lean_unbox(v_a_819_);
lean_dec(v_a_819_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_826_ = l_Lean_Expr_getAppFn_x27(v_a_813_);
lean_dec(v_a_813_);
v___x_827_ = l_Lean_Expr_getAppFn_x27(v_a_815_);
lean_dec(v_a_815_);
v___x_828_ = lean_expr_eqv(v___x_826_, v___x_827_);
lean_dec_ref(v___x_827_);
lean_dec_ref(v___x_826_);
v___x_829_ = lean_box(v___x_828_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_829_);
v___x_831_ = v___x_821_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
else
{
lean_object* v___x_833_; lean_object* v___x_835_; 
lean_dec(v_a_815_);
lean_dec(v_a_813_);
v___x_833_ = lean_box(v___x_789_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_833_);
v___x_835_ = v___x_821_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
else
{
lean_object* v___x_837_; lean_object* v___x_839_; 
lean_dec(v_a_819_);
lean_dec(v_a_815_);
lean_dec(v_a_813_);
v___x_837_ = lean_box(v___x_789_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_837_);
v___x_839_ = v___x_821_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
else
{
lean_dec(v_a_817_);
lean_dec(v_a_815_);
lean_dec(v_a_813_);
return v___x_818_;
}
}
else
{
lean_dec(v_a_815_);
lean_dec(v_a_813_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
return v___x_816_;
}
}
else
{
lean_object* v___x_843_; lean_object* v___x_845_; 
lean_dec_ref(v_expr_800_);
lean_dec_ref(v_expr_791_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
v___x_843_ = lean_box(v___x_789_);
if (v_isShared_806_ == 0)
{
lean_ctor_set_tag(v___x_805_, 0);
lean_ctor_set(v___x_805_, 0, v___x_843_);
v___x_845_ = v___x_805_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
else
{
lean_object* v___x_848_; lean_object* v___x_850_; 
lean_dec(v___x_802_);
lean_dec_ref(v_expr_800_);
lean_dec(v_val_796_);
lean_dec_ref(v_expr_791_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
v___x_848_ = lean_box(v___x_789_);
if (v_isShared_799_ == 0)
{
lean_ctor_set_tag(v___x_798_, 0);
lean_ctor_set(v___x_798_, 0, v___x_848_);
v___x_850_ = v___x_798_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec(v___x_794_);
lean_dec_ref(v_expr_791_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec_ref(v_ti2_782_);
v___x_853_ = lean_box(v___x_789_);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
return v___x_854_;
}
}
else
{
uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec_ref(v_ti2_782_);
lean_dec_ref(v_ti1_781_);
v___x_855_ = 0;
v___x_856_ = lean_box(v___x_855_);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isInstanceProjectionInfoFor___boxed(lean_object* v_kind_858_, lean_object* v_ti1_859_, lean_object* v_ti2_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
uint8_t v_kind_boxed_866_; lean_object* v_res_867_; 
v_kind_boxed_866_ = lean_unbox(v_kind_858_);
v_res_867_ = l_Lean_Server_isInstanceProjectionInfoFor(v_kind_boxed_866_, v_ti1_859_, v_ti2_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToM_run___redArg(lean_object* v_ctx_868_, lean_object* v_ci_869_, lean_object* v_lctx_870_, lean_object* v_act_871_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_apply_1(v_act_871_, v_ctx_868_);
v___x_874_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ci_869_, v_lctx_870_, v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToM_run___redArg___boxed(lean_object* v_ctx_875_, lean_object* v_ci_876_, lean_object* v_lctx_877_, lean_object* v_act_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_Server_GoToM_run___redArg(v_ctx_875_, v_ci_876_, v_lctx_877_, v_act_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToM_run(lean_object* v_00_u03b1_881_, lean_object* v_ctx_882_, lean_object* v_ci_883_, lean_object* v_lctx_884_, lean_object* v_act_885_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_Server_GoToM_run___redArg(v_ctx_882_, v_ci_883_, v_lctx_884_, v_act_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToM_run___boxed(lean_object* v_00_u03b1_888_, lean_object* v_ctx_889_, lean_object* v_ci_890_, lean_object* v_lctx_891_, lean_object* v_act_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_Server_GoToM_run(v_00_u03b1_888_, v_ctx_889_, v_ci_890_, v_lctx_891_, v_act_892_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v___x_901_; lean_object* v_env_902_; lean_object* v___x_903_; lean_object* v_mctx_904_; lean_object* v_lctx_905_; lean_object* v_options_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_901_ = lean_st_ref_get(v___y_899_);
v_env_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc_ref(v_env_902_);
lean_dec(v___x_901_);
v___x_903_ = lean_st_ref_get(v___y_897_);
v_mctx_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc_ref(v_mctx_904_);
lean_dec(v___x_903_);
v_lctx_905_ = lean_ctor_get(v___y_896_, 2);
v_options_906_ = lean_ctor_get(v___y_898_, 2);
lean_inc_ref(v_options_906_);
lean_inc_ref(v_lctx_905_);
v___x_907_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_907_, 0, v_env_902_);
lean_ctor_set(v___x_907_, 1, v_mctx_904_);
lean_ctor_set(v___x_907_, 2, v_lctx_905_);
lean_ctor_set(v___x_907_, 3, v_options_906_);
v___x_908_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v_msgData_895_);
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_ref_923_; lean_object* v___x_924_; lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_933_; 
v_ref_923_ = lean_ctor_get(v___y_920_, 5);
v___x_924_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_933_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_933_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_933_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_931_; 
lean_inc(v_ref_923_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v_ref_923_);
lean_ctor_set(v___x_929_, 1, v_a_925_);
if (v_isShared_928_ == 0)
{
lean_ctor_set_tag(v___x_927_, 1);
lean_ctor_set(v___x_927_, 0, v___x_929_);
v___x_931_ = v___x_927_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_941_, lean_object* v_msg_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_fileName_949_; lean_object* v_fileMap_950_; lean_object* v_options_951_; lean_object* v_currRecDepth_952_; lean_object* v_maxRecDepth_953_; lean_object* v_ref_954_; lean_object* v_currNamespace_955_; lean_object* v_openDecls_956_; lean_object* v_initHeartbeats_957_; lean_object* v_maxHeartbeats_958_; lean_object* v_quotContext_959_; lean_object* v_currMacroScope_960_; uint8_t v_diag_961_; lean_object* v_cancelTk_x3f_962_; uint8_t v_suppressElabErrors_963_; lean_object* v_inheritedTraceOptions_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_973_; 
v_fileName_949_ = lean_ctor_get(v___y_946_, 0);
v_fileMap_950_ = lean_ctor_get(v___y_946_, 1);
v_options_951_ = lean_ctor_get(v___y_946_, 2);
v_currRecDepth_952_ = lean_ctor_get(v___y_946_, 3);
v_maxRecDepth_953_ = lean_ctor_get(v___y_946_, 4);
v_ref_954_ = lean_ctor_get(v___y_946_, 5);
v_currNamespace_955_ = lean_ctor_get(v___y_946_, 6);
v_openDecls_956_ = lean_ctor_get(v___y_946_, 7);
v_initHeartbeats_957_ = lean_ctor_get(v___y_946_, 8);
v_maxHeartbeats_958_ = lean_ctor_get(v___y_946_, 9);
v_quotContext_959_ = lean_ctor_get(v___y_946_, 10);
v_currMacroScope_960_ = lean_ctor_get(v___y_946_, 11);
v_diag_961_ = lean_ctor_get_uint8(v___y_946_, sizeof(void*)*14);
v_cancelTk_x3f_962_ = lean_ctor_get(v___y_946_, 12);
v_suppressElabErrors_963_ = lean_ctor_get_uint8(v___y_946_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_964_ = lean_ctor_get(v___y_946_, 13);
v_isSharedCheck_973_ = !lean_is_exclusive(v___y_946_);
if (v_isSharedCheck_973_ == 0)
{
v___x_966_ = v___y_946_;
v_isShared_967_ = v_isSharedCheck_973_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_inheritedTraceOptions_964_);
lean_inc(v_cancelTk_x3f_962_);
lean_inc(v_currMacroScope_960_);
lean_inc(v_quotContext_959_);
lean_inc(v_maxHeartbeats_958_);
lean_inc(v_initHeartbeats_957_);
lean_inc(v_openDecls_956_);
lean_inc(v_currNamespace_955_);
lean_inc(v_ref_954_);
lean_inc(v_maxRecDepth_953_);
lean_inc(v_currRecDepth_952_);
lean_inc(v_options_951_);
lean_inc(v_fileMap_950_);
lean_inc(v_fileName_949_);
lean_dec(v___y_946_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_973_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v_ref_968_; lean_object* v___x_970_; 
v_ref_968_ = l_Lean_replaceRef(v_ref_941_, v_ref_954_);
lean_dec(v_ref_954_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 5, v_ref_968_);
v___x_970_ = v___x_966_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_fileName_949_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_fileMap_950_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_options_951_);
lean_ctor_set(v_reuseFailAlloc_972_, 3, v_currRecDepth_952_);
lean_ctor_set(v_reuseFailAlloc_972_, 4, v_maxRecDepth_953_);
lean_ctor_set(v_reuseFailAlloc_972_, 5, v_ref_968_);
lean_ctor_set(v_reuseFailAlloc_972_, 6, v_currNamespace_955_);
lean_ctor_set(v_reuseFailAlloc_972_, 7, v_openDecls_956_);
lean_ctor_set(v_reuseFailAlloc_972_, 8, v_initHeartbeats_957_);
lean_ctor_set(v_reuseFailAlloc_972_, 9, v_maxHeartbeats_958_);
lean_ctor_set(v_reuseFailAlloc_972_, 10, v_quotContext_959_);
lean_ctor_set(v_reuseFailAlloc_972_, 11, v_currMacroScope_960_);
lean_ctor_set(v_reuseFailAlloc_972_, 12, v_cancelTk_x3f_962_);
lean_ctor_set(v_reuseFailAlloc_972_, 13, v_inheritedTraceOptions_964_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*14, v_diag_961_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*14 + 1, v_suppressElabErrors_963_);
v___x_970_ = v_reuseFailAlloc_972_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_942_, v___y_944_, v___y_945_, v___x_970_, v___y_947_);
lean_dec_ref(v___x_970_);
return v___x_971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_974_, lean_object* v_msg_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_974_, v_msg_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v_ref_974_);
return v_res_982_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_983_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_986_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_987_ = lean_unsigned_to_nat(0u);
v___x_988_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
lean_ctor_set(v___x_988_, 2, v___x_987_);
lean_ctor_set(v___x_988_, 3, v___x_986_);
lean_ctor_set(v___x_988_, 4, v___x_986_);
lean_ctor_set(v___x_988_, 5, v___x_986_);
lean_ctor_set(v___x_988_, 6, v___x_986_);
lean_ctor_set(v___x_988_, 7, v___x_986_);
lean_ctor_set(v___x_988_, 8, v___x_986_);
return v___x_988_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_989_ = lean_unsigned_to_nat(32u);
v___x_990_ = lean_mk_empty_array_with_capacity(v___x_989_);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_992_ = ((size_t)5ULL);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_unsigned_to_nat(32u);
v___x_995_ = lean_mk_empty_array_with_capacity(v___x_994_);
v___x_996_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_997_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___x_995_);
lean_ctor_set(v___x_997_, 2, v___x_993_);
lean_ctor_set(v___x_997_, 3, v___x_993_);
lean_ctor_set_usize(v___x_997_, 4, v___x_992_);
return v___x_997_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_998_ = lean_box(1);
v___x_999_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_1000_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1001_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v___x_999_);
lean_ctor_set(v___x_1001_, 2, v___x_998_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1004_ = l_Lean_stringToMessageData(v___x_1003_);
return v___x_1004_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1007_ = l_Lean_stringToMessageData(v___x_1006_);
return v___x_1007_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1010_ = l_Lean_stringToMessageData(v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1013_ = l_Lean_stringToMessageData(v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_1019_ = l_Lean_stringToMessageData(v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1023_, lean_object* v_declHint_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; lean_object* v_env_1028_; uint8_t v___x_1029_; 
v___x_1027_ = lean_st_ref_get(v___y_1025_);
v_env_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc_ref(v_env_1028_);
lean_dec(v___x_1027_);
v___x_1029_ = l_Lean_Name_isAnonymous(v_declHint_1024_);
if (v___x_1029_ == 0)
{
uint8_t v_isExporting_1030_; 
v_isExporting_1030_ = lean_ctor_get_uint8(v_env_1028_, sizeof(void*)*8);
if (v_isExporting_1030_ == 0)
{
lean_object* v___x_1031_; 
lean_dec_ref(v_env_1028_);
lean_dec(v_declHint_1024_);
v___x_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1031_, 0, v_msg_1023_);
return v___x_1031_;
}
else
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
lean_inc_ref(v_env_1028_);
v___x_1032_ = l_Lean_Environment_setExporting(v_env_1028_, v___x_1029_);
lean_inc(v_declHint_1024_);
lean_inc_ref(v___x_1032_);
v___x_1033_ = l_Lean_Environment_contains(v___x_1032_, v_declHint_1024_, v_isExporting_1030_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; 
lean_dec_ref(v___x_1032_);
lean_dec_ref(v_env_1028_);
lean_dec(v_declHint_1024_);
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v_msg_1023_);
return v___x_1034_;
}
else
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v_c_1040_; lean_object* v___x_1041_; 
v___x_1035_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1036_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1037_ = l_Lean_Options_empty;
v___x_1038_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1032_);
lean_ctor_set(v___x_1038_, 1, v___x_1035_);
lean_ctor_set(v___x_1038_, 2, v___x_1036_);
lean_ctor_set(v___x_1038_, 3, v___x_1037_);
lean_inc(v_declHint_1024_);
v___x_1039_ = l_Lean_MessageData_ofConstName(v_declHint_1024_, v___x_1029_);
v_c_1040_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1040_, 0, v___x_1038_);
lean_ctor_set(v_c_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1028_, v_declHint_1024_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec_ref(v_env_1028_);
lean_dec(v_declHint_1024_);
v___x_1042_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v_c_1040_);
v___x_1044_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = l_Lean_MessageData_note(v___x_1045_);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v_msg_1023_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
return v___x_1048_;
}
else
{
lean_object* v_val_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1084_; 
v_val_1049_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1051_ = v___x_1041_;
v_isShared_1052_ = v_isSharedCheck_1084_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_val_1049_);
lean_dec(v___x_1041_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1084_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v_mod_1056_; uint8_t v___x_1057_; 
v___x_1053_ = lean_box(0);
v___x_1054_ = l_Lean_Environment_header(v_env_1028_);
lean_dec_ref(v_env_1028_);
v___x_1055_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1054_);
v_mod_1056_ = lean_array_get(v___x_1053_, v___x_1055_, v_val_1049_);
lean_dec(v_val_1049_);
lean_dec_ref(v___x_1055_);
v___x_1057_ = l_Lean_isPrivateName(v_declHint_1024_);
lean_dec(v_declHint_1024_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1058_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v_c_1040_);
v___x_1060_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = l_Lean_MessageData_ofName(v_mod_1056_);
v___x_1063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = l_Lean_MessageData_note(v___x_1065_);
v___x_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1067_, 0, v_msg_1023_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1067_);
v___x_1069_ = v___x_1051_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
else
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1071_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v_c_1040_);
v___x_1073_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = l_Lean_MessageData_ofName(v_mod_1056_);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = l_Lean_MessageData_note(v___x_1078_);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v_msg_1023_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1080_);
v___x_1082_ = v___x_1051_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1085_; 
lean_dec_ref(v_env_1028_);
lean_dec(v_declHint_1024_);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v_msg_1023_);
return v___x_1085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1086_, lean_object* v_declHint_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1086_, v_declHint_1087_, v___y_1088_);
lean_dec(v___y_1088_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1091_, lean_object* v_declHint_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___x_1099_; lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1109_; 
v___x_1099_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1091_, v_declHint_1092_, v___y_1097_);
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1109_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1109_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1104_ = l_Lean_unknownIdentifierMessageTag;
v___x_1105_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v_a_1100_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v___x_1105_);
v___x_1107_ = v___x_1102_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1110_, lean_object* v_declHint_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1110_, v_declHint_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec_ref(v___y_1112_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_1119_, lean_object* v_msg_1120_, lean_object* v_declHint_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; lean_object* v_a_1129_; lean_object* v___x_1130_; 
v___x_1128_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1120_, v_declHint_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref(v___x_1128_);
v___x_1130_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_1119_, v_a_1129_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1131_, lean_object* v_msg_1132_, lean_object* v_declHint_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_1131_, v_msg_1132_, v_declHint_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v_ref_1131_);
return v_res_1140_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1143_ = l_Lean_stringToMessageData(v___x_1142_);
return v___x_1143_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2));
v___x_1146_ = l_Lean_stringToMessageData(v___x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1147_, lean_object* v_constName_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1155_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1156_ = 0;
lean_inc(v_constName_1148_);
v___x_1157_ = l_Lean_MessageData_ofConstName(v_constName_1148_, v___x_1156_);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1155_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_1147_, v___x_1160_, v_constName_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1162_, lean_object* v_constName_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1162_, v_constName_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v_ref_1162_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_ref_1178_; lean_object* v___x_1179_; 
v_ref_1178_ = lean_ctor_get(v___y_1175_, 5);
lean_inc(v_ref_1178_);
v___x_1179_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1178_, v_constName_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
lean_dec(v_ref_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1185_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec_ref(v___y_1181_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(lean_object* v_constName_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1195_; lean_object* v_env_1196_; uint8_t v___x_1197_; lean_object* v___x_1198_; 
v___x_1195_ = lean_st_ref_get(v___y_1193_);
v_env_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc_ref(v_env_1196_);
lean_dec(v___x_1195_);
v___x_1197_ = 0;
lean_inc(v_constName_1188_);
v___x_1198_ = l_Lean_Environment_find_x3f(v_env_1196_, v_constName_1188_, v___x_1197_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
return v___x_1199_;
}
else
{
lean_object* v_val_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v___y_1192_);
lean_dec(v_constName_1188_);
v_val_1200_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1198_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_val_1200_);
lean_dec(v___x_1198_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
lean_ctor_set_tag(v___x_1202_, 0);
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_val_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0___boxed(lean_object* v_constName_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(v_constName_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(lean_object* v_declName_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; 
lean_inc(v_declName_1216_);
v___x_1223_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(v_declName_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1250_; 
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; 
v_unused_1251_ = lean_ctor_get(v___x_1223_, 0);
lean_dec(v_unused_1251_);
v___x_1225_ = v___x_1223_;
v_isShared_1226_ = v_isSharedCheck_1250_;
goto v_resetjp_1224_;
}
else
{
lean_dec(v___x_1223_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1250_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v_env_1228_; lean_object* v___x_1229_; 
v___x_1227_ = lean_st_ref_get(v___y_1221_);
v_env_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc_ref(v_env_1228_);
lean_dec(v___x_1227_);
v___x_1229_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1228_, v_declName_1216_);
lean_dec(v_declName_1216_);
lean_dec_ref(v_env_1228_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1230_ = lean_box(0);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1230_);
v___x_1232_ = v___x_1225_;
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
else
{
lean_object* v_val_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1249_; 
v_val_1234_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1236_ = v___x_1229_;
v_isShared_1237_ = v_isSharedCheck_1249_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_val_1234_);
lean_dec(v___x_1229_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1249_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v_env_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1238_ = lean_st_ref_get(v___y_1221_);
v_env_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc_ref(v_env_1239_);
lean_dec(v___x_1238_);
v___x_1240_ = lean_box(0);
v___x_1241_ = l_Lean_Environment_allImportedModuleNames(v_env_1239_);
lean_dec_ref(v_env_1239_);
v___x_1242_ = lean_array_get(v___x_1240_, v___x_1241_, v_val_1234_);
lean_dec(v_val_1234_);
lean_dec_ref(v___x_1241_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v___x_1242_);
v___x_1244_ = v___x_1236_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1246_; 
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1244_);
v___x_1246_ = v___x_1225_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec(v_declName_1216_);
v_a_1252_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1223_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1223_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0___boxed(lean_object* v_declName_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(v_declName_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec_ref(v___y_1261_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(lean_object* v_declName_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v___x_1275_; 
lean_inc_ref(v_a_1272_);
v___x_1275_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(v_declName_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1330_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1330_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1330_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
if (lean_obj_tag(v_a_1276_) == 0)
{
lean_object* v_doc_1280_; lean_object* v_uri_1281_; lean_object* v_mod_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
lean_dec_ref(v_a_1272_);
v_doc_1280_ = lean_ctor_get(v_a_1269_, 0);
v_uri_1281_ = lean_ctor_get(v_doc_1280_, 0);
v_mod_1282_ = lean_ctor_get(v_doc_1280_, 1);
lean_inc_ref(v_uri_1281_);
lean_inc(v_mod_1282_);
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v_mod_1282_);
lean_ctor_set(v___x_1283_, 1, v_uri_1281_);
v___x_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1284_);
v___x_1286_ = v___x_1278_;
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
else
{
lean_object* v_val_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1329_; 
lean_del_object(v___x_1278_);
v_val_1288_ = lean_ctor_get(v_a_1276_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_a_1276_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1290_ = v_a_1276_;
v_isShared_1291_ = v_isSharedCheck_1329_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_val_1288_);
lean_dec(v_a_1276_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1329_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; 
lean_inc(v_val_1288_);
v___x_1292_ = l_Lean_Server_documentUriFromModule_x3f(v_val_1288_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1313_; 
lean_del_object(v___x_1290_);
lean_dec_ref(v_a_1272_);
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1313_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1313_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
if (lean_obj_tag(v_a_1293_) == 1)
{
lean_object* v_val_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1308_; 
v_val_1297_ = lean_ctor_get(v_a_1293_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_a_1293_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1299_ = v_a_1293_;
v_isShared_1300_ = v_isSharedCheck_1308_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_val_1297_);
lean_dec(v_a_1293_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1308_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1301_, 0, v_val_1288_);
lean_ctor_set(v___x_1301_, 1, v_val_1297_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1301_);
v___x_1303_ = v___x_1299_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1305_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1303_);
v___x_1305_ = v___x_1295_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1311_; 
lean_dec(v_a_1293_);
lean_dec(v_val_1288_);
v___x_1309_ = lean_box(0);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1309_);
v___x_1311_ = v___x_1295_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1328_; 
lean_dec(v_val_1288_);
v_a_1314_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1316_ = v___x_1292_;
v_isShared_1317_ = v_isSharedCheck_1328_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1292_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1328_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v_ref_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
v_ref_1318_ = lean_ctor_get(v_a_1272_, 5);
lean_inc(v_ref_1318_);
lean_dec_ref(v_a_1272_);
v___x_1319_ = lean_io_error_to_string(v_a_1314_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set_tag(v___x_1290_, 3);
lean_ctor_set(v___x_1290_, 0, v___x_1319_);
v___x_1321_ = v___x_1290_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1322_ = l_Lean_MessageData_ofFormat(v___x_1321_);
v___x_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1323_, 0, v_ref_1318_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1323_);
v___x_1325_ = v___x_1316_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
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
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec_ref(v_a_1272_);
v_a_1331_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1275_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1275_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f___boxed(lean_object* v_declName_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(v_declName_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
lean_dec(v_a_1344_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec_ref(v_a_1340_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1347_, lean_object* v_constName_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1356_, lean_object* v_constName_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1(v_00_u03b1_1356_, v_constName_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec_ref(v___y_1358_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1365_, lean_object* v_ref_1366_, lean_object* v_constName_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1366_, v_constName_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1375_, lean_object* v_ref_1376_, lean_object* v_constName_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1375_, v_ref_1376_, v_constName_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v_ref_1376_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_1385_, lean_object* v_ref_1386_, lean_object* v_msg_1387_, lean_object* v_declHint_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_1386_, v_msg_1387_, v_declHint_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1396_, lean_object* v_ref_1397_, lean_object* v_msg_1398_, lean_object* v_declHint_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b1_1396_, v_ref_1397_, v_msg_1398_, v_declHint_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v_ref_1397_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1407_, lean_object* v_declHint_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1407_, v_declHint_1408_, v___y_1413_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1416_, lean_object* v_declHint_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1416_, v_declHint_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec_ref(v___y_1418_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1425_, lean_object* v_ref_1426_, lean_object* v_msg_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_1426_, v_msg_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1435_, lean_object* v_ref_1436_, lean_object* v_msg_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_1435_, v_ref_1436_, v_msg_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v_ref_1436_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1445_, lean_object* v_msg_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1446_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1454_, lean_object* v_msg_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1454_, v_msg_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec_ref(v___y_1456_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(lean_object* v_declName_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1466_; lean_object* v_env_1467_; uint8_t v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1466_ = lean_st_ref_get(v___y_1464_);
v_env_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc_ref(v_env_1467_);
lean_dec(v___x_1466_);
v___x_1468_ = l_Lean_isRecCore(v_env_1467_, v_declName_1463_);
v___x_1469_ = lean_box(v___x_1468_);
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_1471_, v___y_1472_);
lean_dec(v___y_1472_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(lean_object* v_declName_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v___x_1478_; lean_object* v_env_1479_; lean_object* v___x_1480_; lean_object* v_env_1481_; lean_object* v___x_1482_; lean_object* v_toEnvExtension_1483_; lean_object* v_asyncMode_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; lean_object* v___x_1487_; 
v___x_1478_ = lean_st_ref_get(v___y_1476_);
v_env_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc_ref(v_env_1479_);
lean_dec(v___x_1478_);
v___x_1480_ = lean_st_ref_get(v___y_1476_);
v_env_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc_ref(v_env_1481_);
lean_dec(v___x_1480_);
v___x_1482_ = l_Lean_declRangeExt;
v_toEnvExtension_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc_ref(v_toEnvExtension_1483_);
v_asyncMode_1484_ = lean_ctor_get(v_toEnvExtension_1483_, 2);
lean_inc(v_asyncMode_1484_);
lean_dec_ref(v_toEnvExtension_1483_);
v___x_1485_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1486_ = 0;
lean_inc(v_declName_1475_);
v___x_1487_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1485_, v___x_1482_, v_env_1479_, v_declName_1475_, v_asyncMode_1484_, v___x_1486_);
if (lean_obj_tag(v___x_1487_) == 0)
{
uint8_t v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1488_ = 1;
v___x_1489_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1485_, v___x_1482_, v_env_1481_, v_declName_1475_, v_asyncMode_1484_, v___x_1488_);
lean_dec(v_asyncMode_1484_);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
return v___x_1490_;
}
else
{
lean_object* v___x_1491_; 
lean_dec(v_asyncMode_1484_);
lean_dec_ref(v_env_1481_);
lean_dec(v_declName_1475_);
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1487_);
return v___x_1491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_1492_, v___y_1493_);
lean_dec(v___y_1493_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(lean_object* v_declName_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_ranges_1504_; lean_object* v___x_1510_; lean_object* v_env_1511_; lean_object* v___x_1512_; lean_object* v_a_1513_; uint8_t v___y_1519_; uint8_t v___x_1523_; 
v___x_1510_ = lean_st_ref_get(v___y_1501_);
v_env_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc_ref(v_env_1511_);
lean_dec(v___x_1510_);
lean_inc(v_declName_1496_);
v___x_1512_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_1496_, v___y_1501_);
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref(v___x_1512_);
lean_inc(v_declName_1496_);
lean_inc_ref(v_env_1511_);
v___x_1523_ = l_Lean_isAuxRecursor(v_env_1511_, v_declName_1496_);
if (v___x_1523_ == 0)
{
uint8_t v___x_1524_; 
lean_inc(v_declName_1496_);
v___x_1524_ = l_Lean_isNoConfusion(v_env_1511_, v_declName_1496_);
v___y_1519_ = v___x_1524_;
goto v___jp_1518_;
}
else
{
lean_dec_ref(v_env_1511_);
v___y_1519_ = v___x_1523_;
goto v___jp_1518_;
}
v___jp_1503_:
{
if (lean_obj_tag(v_ranges_1504_) == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1505_ = l_Lean_builtinDeclRanges;
v___x_1506_ = lean_st_ref_get(v___x_1505_);
v___x_1507_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1506_, v_declName_1496_);
lean_dec(v_declName_1496_);
lean_dec(v___x_1506_);
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
return v___x_1508_;
}
else
{
lean_object* v___x_1509_; 
lean_dec(v_declName_1496_);
v___x_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1509_, 0, v_ranges_1504_);
return v___x_1509_;
}
}
v___jp_1514_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v_a_1517_; 
v___x_1515_ = l_Lean_Name_getPrefix(v_declName_1496_);
v___x_1516_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v___x_1515_, v___y_1501_);
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref(v___x_1516_);
v_ranges_1504_ = v_a_1517_;
goto v___jp_1503_;
}
v___jp_1518_:
{
if (v___y_1519_ == 0)
{
uint8_t v___x_1520_; 
v___x_1520_ = lean_unbox(v_a_1513_);
lean_dec(v_a_1513_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; lean_object* v_a_1522_; 
lean_inc(v_declName_1496_);
v___x_1521_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_1496_, v___y_1501_);
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref(v___x_1521_);
v_ranges_1504_ = v_a_1522_;
goto v___jp_1503_;
}
else
{
goto v___jp_1514_;
}
}
else
{
lean_dec(v_a_1513_);
goto v___jp_1514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0___boxed(lean_object* v_declName_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(v_declName_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec_ref(v___y_1526_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl(lean_object* v_declName_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v___x_1542_; lean_object* v_env_1543_; uint8_t v___x_1544_; uint8_t v___x_1545_; 
v___x_1542_ = lean_st_ref_get(v_a_1540_);
v_env_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc_ref(v_env_1543_);
lean_dec(v___x_1542_);
v___x_1544_ = 1;
lean_inc(v_declName_1535_);
v___x_1545_ = l_Lean_Environment_contains(v_env_1543_, v_declName_1535_, v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
lean_dec_ref(v_a_1539_);
lean_dec_ref(v_a_1536_);
lean_dec(v_declName_1535_);
v___x_1546_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; 
lean_inc_ref(v_a_1539_);
lean_inc(v_declName_1535_);
v___x_1548_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(v_declName_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1625_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1551_ = v___x_1548_;
v_isShared_1552_ = v_isSharedCheck_1625_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1625_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
if (lean_obj_tag(v_a_1549_) == 1)
{
lean_object* v_val_1553_; lean_object* v_fst_1554_; lean_object* v_snd_1555_; lean_object* v___x_1556_; 
lean_del_object(v___x_1551_);
v_val_1553_ = lean_ctor_get(v_a_1549_, 0);
lean_inc(v_val_1553_);
lean_dec_ref(v_a_1549_);
v_fst_1554_ = lean_ctor_get(v_val_1553_, 0);
lean_inc(v_fst_1554_);
v_snd_1555_ = lean_ctor_get(v_val_1553_, 1);
lean_inc(v_snd_1555_);
lean_dec(v_val_1553_);
lean_inc(v_declName_1535_);
v___x_1556_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(v_declName_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
lean_dec_ref(v_a_1539_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1612_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1612_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1612_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
if (lean_obj_tag(v_a_1557_) == 1)
{
lean_object* v_val_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1607_; 
v_val_1561_ = lean_ctor_get(v_a_1557_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_a_1557_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1563_ = v_a_1557_;
v_isShared_1564_ = v_isSharedCheck_1607_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_val_1561_);
lean_dec(v_a_1557_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1607_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v_doc_1565_; lean_object* v_originInfo_x3f_1566_; uint8_t v___x_1567_; lean_object* v___y_1569_; 
v_doc_1565_ = lean_ctor_get(v_a_1536_, 0);
lean_inc_ref(v_doc_1565_);
v_originInfo_x3f_1566_ = lean_ctor_get(v_a_1536_, 2);
lean_inc(v_originInfo_x3f_1566_);
lean_dec_ref(v_a_1536_);
v___x_1567_ = 0;
if (lean_obj_tag(v_originInfo_x3f_1566_) == 0)
{
lean_object* v___x_1593_; 
lean_dec_ref(v_doc_1565_);
v___x_1593_ = lean_box(0);
v___y_1569_ = v___x_1593_;
goto v___jp_1568_;
}
else
{
lean_object* v_val_1594_; lean_object* v___x_1595_; 
v_val_1594_ = lean_ctor_get(v_originInfo_x3f_1566_, 0);
lean_inc(v_val_1594_);
lean_dec_ref(v_originInfo_x3f_1566_);
v___x_1595_ = l_Lean_Elab_Info_range_x3f(v_val_1594_);
lean_dec(v_val_1594_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v___x_1596_; 
lean_dec_ref(v_doc_1565_);
v___x_1596_ = lean_box(0);
v___y_1569_ = v___x_1596_;
goto v___jp_1568_;
}
else
{
lean_object* v_val_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1606_; 
v_val_1597_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1599_ = v___x_1595_;
v_isShared_1600_ = v_isSharedCheck_1606_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_val_1597_);
lean_dec(v___x_1595_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1606_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v_text_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; 
v_text_1601_ = lean_ctor_get(v_doc_1565_, 3);
lean_inc_ref(v_text_1601_);
lean_dec_ref(v_doc_1565_);
v___x_1602_ = l_Lean_Syntax_Range_toLspRange(v_text_1601_, v_val_1597_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1602_);
v___x_1604_ = v___x_1599_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
v___y_1569_ = v___x_1604_;
goto v___jp_1568_;
}
}
}
}
v___jp_1568_:
{
lean_object* v_range_1570_; lean_object* v_selectionRange_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1592_; 
v_range_1570_ = lean_ctor_get(v_val_1561_, 0);
v_selectionRange_1571_ = lean_ctor_get(v_val_1561_, 1);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_val_1561_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1573_ = v_val_1561_;
v_isShared_1574_ = v_isSharedCheck_1592_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_selectionRange_1571_);
lean_inc(v_range_1570_);
lean_dec(v_val_1561_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1592_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1575_ = l_Lean_DeclarationRange_toLspRange(v_range_1570_);
v___x_1576_ = l_Lean_DeclarationRange_toLspRange(v_selectionRange_1571_);
v___x_1577_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1577_, 0, v___y_1569_);
lean_ctor_set(v___x_1577_, 1, v_snd_1555_);
lean_ctor_set(v___x_1577_, 2, v___x_1575_);
lean_ctor_set(v___x_1577_, 3, v___x_1576_);
v___x_1578_ = lean_erase_macro_scopes(v_declName_1535_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 1, v___x_1578_);
lean_ctor_set(v___x_1573_, 0, v_fst_1554_);
v___x_1580_ = v___x_1573_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_fst_1554_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1582_; 
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v___x_1580_);
v___x_1582_ = v___x_1563_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1583_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1583_, 0, v___x_1577_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
lean_ctor_set_uint8(v___x_1583_, sizeof(void*)*2, v___x_1567_);
v___x_1584_ = lean_unsigned_to_nat(1u);
v___x_1585_ = lean_mk_empty_array_with_capacity(v___x_1584_);
v___x_1586_ = lean_array_push(v___x_1585_, v___x_1583_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1586_);
v___x_1588_ = v___x_1559_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1610_; 
lean_dec(v_a_1557_);
lean_dec(v_snd_1555_);
lean_dec(v_fst_1554_);
lean_dec_ref(v_a_1536_);
lean_dec(v_declName_1535_);
v___x_1608_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1608_);
v___x_1610_ = v___x_1559_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
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
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec(v_snd_1555_);
lean_dec(v_fst_1554_);
lean_dec_ref(v_a_1536_);
lean_dec(v_declName_1535_);
v_a_1613_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1556_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1556_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1623_; 
lean_dec(v_a_1549_);
lean_dec_ref(v_a_1539_);
lean_dec_ref(v_a_1536_);
lean_dec(v_declName_1535_);
v___x_1621_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1621_);
v___x_1623_ = v___x_1551_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_dec_ref(v_a_1539_);
lean_dec_ref(v_a_1536_);
lean_dec(v_declName_1535_);
v_a_1626_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1548_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1548_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl___boxed(lean_object* v_declName_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_Server_locationLinksFromDecl(v_declName_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
lean_dec(v_a_1639_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0(lean_object* v_declName_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_1642_, v___y_1647_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___boxed(lean_object* v_declName_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0(v_declName_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec_ref(v___y_1651_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1(lean_object* v_declName_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_1658_, v___y_1663_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___boxed(lean_object* v_declName_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1(v_declName_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec_ref(v___y_1667_);
return v_res_1673_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0(lean_object* v_id_1674_, lean_object* v_x_1675_){
_start:
{
if (lean_obj_tag(v_x_1675_) == 1)
{
lean_object* v_i_1676_; lean_object* v_expr_1677_; 
v_i_1676_ = lean_ctor_get(v_x_1675_, 0);
v_expr_1677_ = lean_ctor_get(v_i_1676_, 3);
if (lean_obj_tag(v_expr_1677_) == 1)
{
uint8_t v_isBinder_1678_; 
v_isBinder_1678_ = lean_ctor_get_uint8(v_i_1676_, sizeof(void*)*4);
if (v_isBinder_1678_ == 1)
{
lean_object* v_fvarId_1679_; uint8_t v___x_1680_; 
v_fvarId_1679_ = lean_ctor_get(v_expr_1677_, 0);
v___x_1680_ = l_Lean_instBEqFVarId_beq(v_fvarId_1679_, v_id_1674_);
return v___x_1680_;
}
else
{
uint8_t v___x_1681_; 
v___x_1681_ = 0;
return v___x_1681_;
}
}
else
{
uint8_t v___x_1682_; 
v___x_1682_ = 0;
return v___x_1682_;
}
}
else
{
uint8_t v___x_1683_; 
v___x_1683_ = 0;
return v___x_1683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0___boxed(lean_object* v_id_1684_, lean_object* v_x_1685_){
_start:
{
uint8_t v_res_1686_; lean_object* v_r_1687_; 
v_res_1686_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0(v_id_1684_, v_x_1685_);
lean_dec_ref(v_x_1685_);
lean_dec(v_id_1684_);
v_r_1687_ = lean_box(v_res_1686_);
return v_r_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(lean_object* v_id_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_infoTree_x3f_1691_; 
v_infoTree_x3f_1691_ = lean_ctor_get(v_a_1689_, 1);
lean_inc(v_infoTree_x3f_1691_);
lean_dec_ref(v_a_1689_);
if (lean_obj_tag(v_infoTree_x3f_1691_) == 1)
{
lean_object* v_val_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1701_; 
v_val_1692_ = lean_ctor_get(v_infoTree_x3f_1691_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_infoTree_x3f_1691_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1694_ = v_infoTree_x3f_1691_;
v_isShared_1695_ = v_isSharedCheck_1701_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_val_1692_);
lean_dec(v_infoTree_x3f_1691_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1701_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___f_1696_; lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___f_1696_ = lean_alloc_closure((void*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1696_, 0, v_id_1688_);
v___x_1697_ = l_Lean_Elab_InfoTree_findInfo_x3f(v___f_1696_, v_val_1692_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set_tag(v___x_1694_, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1697_);
v___x_1699_ = v___x_1694_;
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
else
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
lean_dec(v_infoTree_x3f_1691_);
lean_dec(v_id_1688_);
v___x_1702_ = lean_box(0);
v___x_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
return v___x_1703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___boxed(lean_object* v_id_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(v_id_1704_, v_a_1705_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f(lean_object* v_id_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(v_id_1708_, v_a_1709_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___boxed(lean_object* v_id_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f(v_id_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromBinder___redArg(lean_object* v_id_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_doc_1727_; lean_object* v_originInfo_x3f_1728_; lean_object* v___x_1729_; lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1773_; 
v_doc_1727_ = lean_ctor_get(v_a_1725_, 0);
lean_inc_ref(v_doc_1727_);
v_originInfo_x3f_1728_ = lean_ctor_get(v_a_1725_, 2);
lean_inc(v_originInfo_x3f_1728_);
v___x_1729_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(v_id_1724_, v_a_1725_);
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1732_ = v___x_1729_;
v_isShared_1733_ = v_isSharedCheck_1773_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1729_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1773_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
if (lean_obj_tag(v_a_1730_) == 1)
{
lean_object* v_val_1734_; lean_object* v___x_1735_; 
v_val_1734_ = lean_ctor_get(v_a_1730_, 0);
lean_inc(v_val_1734_);
lean_dec_ref(v_a_1730_);
v___x_1735_ = l_Lean_Elab_Info_range_x3f(v_val_1734_);
lean_dec(v_val_1734_);
if (lean_obj_tag(v___x_1735_) == 1)
{
lean_object* v_val_1736_; lean_object* v_uri_1737_; lean_object* v_text_1738_; lean_object* v___x_1739_; lean_object* v___y_1741_; 
v_val_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_val_1736_);
lean_dec_ref(v___x_1735_);
v_uri_1737_ = lean_ctor_get(v_doc_1727_, 0);
lean_inc_ref(v_uri_1737_);
v_text_1738_ = lean_ctor_get(v_doc_1727_, 3);
lean_inc_ref(v_text_1738_);
lean_dec_ref(v_doc_1727_);
lean_inc_ref(v_text_1738_);
v___x_1739_ = l_Lean_Syntax_Range_toLspRange(v_text_1738_, v_val_1736_);
if (lean_obj_tag(v_originInfo_x3f_1728_) == 0)
{
lean_object* v___x_1752_; 
lean_dec_ref(v_text_1738_);
v___x_1752_ = lean_box(0);
v___y_1741_ = v___x_1752_;
goto v___jp_1740_;
}
else
{
lean_object* v_val_1753_; lean_object* v___x_1754_; 
v_val_1753_ = lean_ctor_get(v_originInfo_x3f_1728_, 0);
lean_inc(v_val_1753_);
lean_dec_ref(v_originInfo_x3f_1728_);
v___x_1754_ = l_Lean_Elab_Info_range_x3f(v_val_1753_);
lean_dec(v_val_1753_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v___x_1755_; 
lean_dec_ref(v_text_1738_);
v___x_1755_ = lean_box(0);
v___y_1741_ = v___x_1755_;
goto v___jp_1740_;
}
else
{
lean_object* v_val_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1764_; 
v_val_1756_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1758_ = v___x_1754_;
v_isShared_1759_ = v_isSharedCheck_1764_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_val_1756_);
lean_dec(v___x_1754_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1764_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1760_ = l_Lean_Syntax_Range_toLspRange(v_text_1738_, v_val_1756_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1760_);
v___x_1762_ = v___x_1758_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
v___y_1741_ = v___x_1762_;
goto v___jp_1740_;
}
}
}
}
v___jp_1740_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1750_; 
lean_inc_ref(v___x_1739_);
v___x_1742_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1742_, 0, v___y_1741_);
lean_ctor_set(v___x_1742_, 1, v_uri_1737_);
lean_ctor_set(v___x_1742_, 2, v___x_1739_);
lean_ctor_set(v___x_1742_, 3, v___x_1739_);
v___x_1743_ = lean_box(0);
v___x_1744_ = 0;
v___x_1745_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1745_, 0, v___x_1742_);
lean_ctor_set(v___x_1745_, 1, v___x_1743_);
lean_ctor_set_uint8(v___x_1745_, sizeof(void*)*2, v___x_1744_);
v___x_1746_ = lean_unsigned_to_nat(1u);
v___x_1747_ = lean_mk_empty_array_with_capacity(v___x_1746_);
v___x_1748_ = lean_array_push(v___x_1747_, v___x_1745_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v___x_1748_);
v___x_1750_ = v___x_1732_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1767_; 
lean_dec(v___x_1735_);
lean_dec(v_originInfo_x3f_1728_);
lean_dec_ref(v_doc_1727_);
v___x_1765_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v___x_1765_);
v___x_1767_ = v___x_1732_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1771_; 
lean_dec(v_a_1730_);
lean_dec(v_originInfo_x3f_1728_);
lean_dec_ref(v_doc_1727_);
v___x_1769_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v___x_1769_);
v___x_1771_ = v___x_1732_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromBinder___redArg___boxed(lean_object* v_id_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_Server_locationLinksFromBinder___redArg(v_id_1774_, v_a_1775_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromBinder(lean_object* v_id_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_Server_locationLinksFromBinder___redArg(v_id_1778_, v_a_1779_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromBinder___boxed(lean_object* v_id_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_Server_locationLinksFromBinder(v_id_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
return v_res_1793_;
}
}
static lean_object* _init_l_Lean_Server_locationLinksFromImport___redArg___closed__6(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__5));
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromImport___redArg(lean_object* v_i_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v_stx_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1938_; 
v_stx_1841_ = lean_ctor_get(v_i_1825_, 1);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_i_1825_);
if (v_isSharedCheck_1938_ == 0)
{
lean_object* v_unused_1939_; 
v_unused_1939_ = lean_ctor_get(v_i_1825_, 0);
lean_dec(v_unused_1939_);
v___x_1843_ = v_i_1825_;
v_isShared_1844_ = v_isSharedCheck_1938_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_stx_1841_);
lean_dec(v_i_1825_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1938_;
goto v_resetjp_1842_;
}
v___jp_1829_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_inc_ref(v___y_1831_);
v___x_1833_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1833_, 0, v___y_1832_);
lean_ctor_set(v___x_1833_, 1, v___y_1830_);
lean_ctor_set(v___x_1833_, 2, v___y_1831_);
lean_ctor_set(v___x_1833_, 3, v___y_1831_);
v___x_1834_ = lean_box(0);
v___x_1835_ = 0;
v___x_1836_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1836_, 0, v___x_1833_);
lean_ctor_set(v___x_1836_, 1, v___x_1834_);
lean_ctor_set_uint8(v___x_1836_, sizeof(void*)*2, v___x_1835_);
v___x_1837_ = lean_unsigned_to_nat(1u);
v___x_1838_ = lean_mk_empty_array_with_capacity(v___x_1837_);
v___x_1839_ = lean_array_push(v___x_1838_, v___x_1836_);
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
return v___x_1840_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; uint8_t v___x_1846_; 
v___x_1845_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__4));
lean_inc(v_stx_1841_);
v___x_1846_ = l_Lean_Syntax_isOfKind(v_stx_1841_, v___x_1845_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_del_object(v___x_1843_);
lean_dec(v_stx_1841_);
lean_dec_ref(v_a_1826_);
v___x_1847_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
return v___x_1848_;
}
else
{
lean_object* v___x_1849_; lean_object* v___y_1851_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1915_; lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1849_ = lean_unsigned_to_nat(0u);
v___x_1927_ = l_Lean_Syntax_getArg(v_stx_1841_, v___x_1849_);
v___x_1928_ = l_Lean_Syntax_isNone(v___x_1927_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1929_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1927_);
v___x_1930_ = l_Lean_Syntax_matchesNull(v___x_1927_, v___x_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
lean_dec(v___x_1927_);
lean_del_object(v___x_1843_);
lean_dec(v_stx_1841_);
lean_dec_ref(v_a_1826_);
v___x_1931_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
return v___x_1932_;
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; 
v___x_1933_ = l_Lean_Syntax_getArg(v___x_1927_, v___x_1849_);
lean_dec(v___x_1927_);
v___x_1934_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__12));
v___x_1935_ = l_Lean_Syntax_isOfKind(v___x_1933_, v___x_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_del_object(v___x_1843_);
lean_dec(v_stx_1841_);
lean_dec_ref(v_a_1826_);
v___x_1936_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
return v___x_1937_;
}
else
{
v___y_1915_ = v_a_1827_;
goto v___jp_1914_;
}
}
}
else
{
lean_dec(v___x_1927_);
v___y_1915_ = v_a_1827_;
goto v___jp_1914_;
}
v___jp_1850_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1852_ = lean_unsigned_to_nat(5u);
v___x_1853_ = l_Lean_Syntax_getArg(v_stx_1841_, v___x_1852_);
v___x_1854_ = l_Lean_Syntax_matchesNull(v___x_1853_, v___x_1849_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_del_object(v___x_1843_);
lean_dec(v_stx_1841_);
lean_dec_ref(v_a_1826_);
v___x_1855_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1857_ = lean_unsigned_to_nat(4u);
v___x_1858_ = l_Lean_Syntax_getArg(v_stx_1841_, v___x_1857_);
lean_dec(v_stx_1841_);
v___x_1859_ = l_Lean_TSyntax_getId(v___x_1858_);
v___x_1860_ = l_Lean_Server_documentUriFromModule_x3f(v___x_1859_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1884_; 
lean_del_object(v___x_1843_);
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1884_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1884_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
if (lean_obj_tag(v_a_1861_) == 1)
{
lean_object* v_val_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
lean_del_object(v___x_1863_);
v_val_1865_ = lean_ctor_get(v_a_1861_, 0);
lean_inc(v_val_1865_);
lean_dec_ref(v_a_1861_);
v___x_1866_ = lean_obj_once(&l_Lean_Server_locationLinksFromImport___redArg___closed__6, &l_Lean_Server_locationLinksFromImport___redArg___closed__6_once, _init_l_Lean_Server_locationLinksFromImport___redArg___closed__6);
v___x_1867_ = l_Lean_Syntax_getRange_x3f(v___x_1858_, v___x_1846_);
lean_dec(v___x_1858_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v___x_1868_; 
lean_dec_ref(v_a_1826_);
v___x_1868_ = lean_box(0);
v___y_1830_ = v_val_1865_;
v___y_1831_ = v___x_1866_;
v___y_1832_ = v___x_1868_;
goto v___jp_1829_;
}
else
{
lean_object* v_doc_1869_; lean_object* v_val_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1879_; 
v_doc_1869_ = lean_ctor_get(v_a_1826_, 0);
lean_inc_ref(v_doc_1869_);
lean_dec_ref(v_a_1826_);
v_val_1870_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1872_ = v___x_1867_;
v_isShared_1873_ = v_isSharedCheck_1879_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_val_1870_);
lean_dec(v___x_1867_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1879_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v_text_1874_; lean_object* v___x_1875_; lean_object* v___x_1877_; 
v_text_1874_ = lean_ctor_get(v_doc_1869_, 3);
lean_inc_ref(v_text_1874_);
lean_dec_ref(v_doc_1869_);
v___x_1875_ = l_Lean_Syntax_Range_toLspRange(v_text_1874_, v_val_1870_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1875_);
v___x_1877_ = v___x_1872_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
v___y_1830_ = v_val_1865_;
v___y_1831_ = v___x_1866_;
v___y_1832_ = v___x_1877_;
goto v___jp_1829_;
}
}
}
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1882_; 
lean_dec(v_a_1861_);
lean_dec(v___x_1858_);
lean_dec_ref(v_a_1826_);
v___x_1880_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1880_);
v___x_1882_ = v___x_1863_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
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
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1899_; 
lean_dec(v___x_1858_);
lean_dec_ref(v_a_1826_);
v_a_1885_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1887_ = v___x_1860_;
v_isShared_1888_ = v_isSharedCheck_1899_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1860_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1899_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v_ref_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1894_; 
v_ref_1889_ = lean_ctor_get(v___y_1851_, 5);
v___x_1890_ = lean_io_error_to_string(v_a_1885_);
v___x_1891_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
v___x_1892_ = l_Lean_MessageData_ofFormat(v___x_1891_);
lean_inc(v_ref_1889_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 1, v___x_1892_);
lean_ctor_set(v___x_1843_, 0, v_ref_1889_);
v___x_1894_ = v___x_1843_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_ref_1889_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1896_; 
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v___x_1894_);
v___x_1896_ = v___x_1887_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
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
}
v___jp_1900_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1903_ = lean_unsigned_to_nat(3u);
v___x_1904_ = l_Lean_Syntax_getArg(v_stx_1841_, v___x_1903_);
v___x_1905_ = l_Lean_Syntax_isNone(v___x_1904_);
if (v___x_1905_ == 0)
{
uint8_t v___x_1906_; 
lean_inc(v___x_1904_);
v___x_1906_ = l_Lean_Syntax_matchesNull(v___x_1904_, v___y_1901_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
lean_dec(v___x_1904_);
lean_del_object(v___x_1843_);
lean_dec(v_stx_1841_);
lean_dec_ref(v_a_1826_);
v___x_1907_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v___x_1909_ = l_Lean_Syntax_getArg(v___x_1904_, v___x_1849_);
lean_dec(v___x_1904_);
v___x_1910_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__8));
v___x_1911_ = l_Lean_Syntax_isOfKind(v___x_1909_, v___x_1910_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
lean_del_object(v___x_1843_);
lean_dec(v_stx_1841_);
lean_dec_ref(v_a_1826_);
v___x_1912_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
return v___x_1913_;
}
else
{
v___y_1851_ = v___y_1902_;
goto v___jp_1850_;
}
}
}
else
{
lean_dec(v___x_1904_);
v___y_1851_ = v___y_1902_;
goto v___jp_1850_;
}
}
v___jp_1914_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; 
v___x_1916_ = lean_unsigned_to_nat(1u);
v___x_1917_ = l_Lean_Syntax_getArg(v_stx_1841_, v___x_1916_);
v___x_1918_ = l_Lean_Syntax_isNone(v___x_1917_);
if (v___x_1918_ == 0)
{
uint8_t v___x_1919_; 
lean_inc(v___x_1917_);
v___x_1919_ = l_Lean_Syntax_matchesNull(v___x_1917_, v___x_1916_);
if (v___x_1919_ == 0)
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec(v___x_1917_);
lean_del_object(v___x_1843_);
lean_dec(v_stx_1841_);
lean_dec_ref(v_a_1826_);
v___x_1920_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v___x_1922_ = l_Lean_Syntax_getArg(v___x_1917_, v___x_1849_);
lean_dec(v___x_1917_);
v___x_1923_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__10));
v___x_1924_ = l_Lean_Syntax_isOfKind(v___x_1922_, v___x_1923_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_del_object(v___x_1843_);
lean_dec(v_stx_1841_);
lean_dec_ref(v_a_1826_);
v___x_1925_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
else
{
v___y_1901_ = v___x_1916_;
v___y_1902_ = v___y_1915_;
goto v___jp_1900_;
}
}
}
else
{
lean_dec(v___x_1917_);
v___y_1901_ = v___x_1916_;
v___y_1902_ = v___y_1915_;
goto v___jp_1900_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromImport___redArg___boxed(lean_object* v_i_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Lean_Server_locationLinksFromImport___redArg(v_i_1940_, v_a_1941_, v_a_1942_);
lean_dec_ref(v_a_1942_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromImport(lean_object* v_i_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Lean_Server_locationLinksFromImport___redArg(v_i_1945_, v_a_1946_, v_a_1949_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromImport___boxed(lean_object* v_i_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_Server_locationLinksFromImport(v_i_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v___x_1983_; lean_object* v_originInfo_x3f_1987_; 
v___x_1983_ = lean_st_ref_get(v_a_1981_);
v_originInfo_x3f_1987_ = lean_ctor_get(v_a_1980_, 2);
lean_inc(v_originInfo_x3f_1987_);
if (lean_obj_tag(v_originInfo_x3f_1987_) == 1)
{
uint8_t v_kind_1988_; lean_object* v_val_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2037_; 
v_kind_1988_ = lean_ctor_get_uint8(v_a_1980_, sizeof(void*)*4);
lean_dec_ref(v_a_1980_);
v_val_1989_ = lean_ctor_get(v_originInfo_x3f_1987_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_originInfo_x3f_1987_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_1991_ = v_originInfo_x3f_1987_;
v_isShared_1992_ = v_isSharedCheck_2037_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_val_1989_);
lean_dec(v_originInfo_x3f_1987_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2037_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1993_; 
v___x_1993_ = l_Lean_Elab_Info_toElabInfo_x3f(v_val_1989_);
if (lean_obj_tag(v___x_1993_) == 1)
{
lean_object* v_val_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2032_; 
v_val_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2032_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_val_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2032_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v_elaborator_1998_; lean_object* v_stx_1999_; lean_object* v___y_2001_; uint8_t v___y_2002_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v_elaborator_1998_ = lean_ctor_get(v_val_1994_, 0);
lean_inc(v_elaborator_1998_);
v_stx_1999_ = lean_ctor_get(v_val_1994_, 1);
lean_inc(v_stx_1999_);
lean_dec(v_val_1994_);
v___x_2011_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__2));
v___x_2012_ = lean_name_eq(v_elaborator_1998_, v___x_2011_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; uint8_t v___x_2014_; 
lean_del_object(v___x_1991_);
v___x_2013_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6));
v___x_2014_ = lean_name_eq(v_elaborator_1998_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8));
v___x_2016_ = lean_name_eq(v_elaborator_1998_, v___x_2015_);
if (v___x_2016_ == 0)
{
lean_object* v_env_2017_; uint8_t v___x_2018_; lean_object* v_names_2020_; lean_object* v___x_2025_; uint8_t v___x_2026_; 
v_env_2017_ = lean_ctor_get(v___x_1983_, 0);
lean_inc_ref(v_env_2017_);
lean_dec(v___x_1983_);
v___x_2018_ = 1;
v___x_2025_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
lean_inc(v_elaborator_1998_);
lean_inc_ref(v_env_2017_);
v___x_2026_ = l_Lean_Environment_contains(v_env_2017_, v_elaborator_1998_, v___x_2018_);
if (v___x_2026_ == 0)
{
lean_dec(v_elaborator_1998_);
v_names_2020_ = v___x_2025_;
goto v___jp_2019_;
}
else
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_array_push(v___x_2025_, v_elaborator_1998_);
v_names_2020_ = v___x_2027_;
goto v___jp_2019_;
}
v___jp_2019_:
{
uint8_t v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = 0;
v___x_2022_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_1988_, v___x_2021_);
if (v___x_2022_ == 0)
{
lean_dec_ref(v_env_2017_);
v___y_2001_ = v_names_2020_;
v___y_2002_ = v___x_2022_;
goto v___jp_2000_;
}
else
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
lean_inc(v_stx_1999_);
v___x_2023_ = l_Lean_Syntax_getKind(v_stx_1999_);
v___x_2024_ = l_Lean_Environment_contains(v_env_2017_, v___x_2023_, v___x_2018_);
v___y_2001_ = v_names_2020_;
v___y_2002_ = v___x_2024_;
goto v___jp_2000_;
}
}
}
else
{
lean_dec(v_stx_1999_);
lean_dec(v_elaborator_1998_);
lean_del_object(v___x_1996_);
lean_dec(v___x_1983_);
goto v___jp_1984_;
}
}
else
{
lean_dec(v_stx_1999_);
lean_dec(v_elaborator_1998_);
lean_del_object(v___x_1996_);
lean_dec(v___x_1983_);
goto v___jp_1984_;
}
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
lean_dec(v_stx_1999_);
lean_dec(v_elaborator_1998_);
lean_del_object(v___x_1996_);
lean_dec(v___x_1983_);
v___x_2028_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
if (v_isShared_1992_ == 0)
{
lean_ctor_set_tag(v___x_1991_, 0);
lean_ctor_set(v___x_1991_, 0, v___x_2028_);
v___x_2030_ = v___x_1991_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
v___jp_2000_:
{
if (v___y_2002_ == 0)
{
lean_object* v___x_2004_; 
lean_dec(v_stx_1999_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set_tag(v___x_1996_, 0);
lean_ctor_set(v___x_1996_, 0, v___y_2001_);
v___x_2004_ = v___x_1996_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___y_2001_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
else
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2006_ = l_Lean_Syntax_getKind(v_stx_1999_);
v___x_2007_ = lean_array_push(v___y_2001_, v___x_2006_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set_tag(v___x_1996_, 0);
lean_ctor_set(v___x_1996_, 0, v___x_2007_);
v___x_2009_ = v___x_1996_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2035_; 
lean_dec(v___x_1993_);
lean_dec(v___x_1983_);
v___x_2033_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
if (v_isShared_1992_ == 0)
{
lean_ctor_set_tag(v___x_1991_, 0);
lean_ctor_set(v___x_1991_, 0, v___x_2033_);
v___x_2035_ = v___x_1991_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec(v_originInfo_x3f_1987_);
lean_dec(v___x_1983_);
lean_dec_ref(v_a_1980_);
v___x_2038_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
return v___x_2039_;
}
v___jp_1984_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
v___x_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
return v___x_1986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___boxed(lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(v_a_2040_, v_a_2041_);
lean_dec(v_a_2041_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames(lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(v_a_2044_, v_a_2048_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___boxed(lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames(v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(lean_object* v_as_2058_, size_t v_sz_2059_, size_t v_i_2060_, lean_object* v_b_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
uint8_t v___x_2068_; 
v___x_2068_ = lean_usize_dec_lt(v_i_2060_, v_sz_2059_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; 
lean_dec_ref(v___y_2065_);
lean_dec_ref(v___y_2062_);
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v_b_2061_);
return v___x_2069_;
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2071_; 
v_a_2070_ = lean_array_uget_borrowed(v_as_2058_, v_i_2060_);
lean_inc_ref(v___y_2065_);
lean_inc_ref(v___y_2062_);
lean_inc(v_a_2070_);
v___x_2071_ = l_Lean_Server_locationLinksFromDecl(v_a_2070_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2073_; size_t v___x_2074_; size_t v___x_2075_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref(v___x_2071_);
v___x_2073_ = l_Array_append___redArg(v_b_2061_, v_a_2072_);
lean_dec(v_a_2072_);
v___x_2074_ = ((size_t)1ULL);
v___x_2075_ = lean_usize_add(v_i_2060_, v___x_2074_);
v_i_2060_ = v___x_2075_;
v_b_2061_ = v___x_2073_;
goto _start;
}
else
{
lean_dec_ref(v___y_2065_);
lean_dec_ref(v___y_2062_);
lean_dec_ref(v_b_2061_);
return v___x_2071_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0___boxed(lean_object* v_as_2077_, lean_object* v_sz_2078_, lean_object* v_i_2079_, lean_object* v_b_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
size_t v_sz_boxed_2087_; size_t v_i_boxed_2088_; lean_object* v_res_2089_; 
v_sz_boxed_2087_ = lean_unbox_usize(v_sz_2078_);
lean_dec(v_sz_2078_);
v_i_boxed_2088_ = lean_unbox_usize(v_i_2079_);
lean_dec(v_i_2079_);
v_res_2089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_as_2077_, v_sz_boxed_2087_, v_i_boxed_2088_, v_b_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
lean_dec(v___y_2085_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec_ref(v_as_2077_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(size_t v_sz_2090_, size_t v_i_2091_, lean_object* v_bs_2092_){
_start:
{
uint8_t v___x_2093_; 
v___x_2093_ = lean_usize_dec_lt(v_i_2091_, v_sz_2090_);
if (v___x_2093_ == 0)
{
return v_bs_2092_;
}
else
{
lean_object* v_v_2094_; lean_object* v_toLocationLink_2095_; lean_object* v_ident_x3f_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2109_; 
v_v_2094_ = lean_array_uget(v_bs_2092_, v_i_2091_);
v_toLocationLink_2095_ = lean_ctor_get(v_v_2094_, 0);
v_ident_x3f_2096_ = lean_ctor_get(v_v_2094_, 1);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_v_2094_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2098_ = v_v_2094_;
v_isShared_2099_ = v_isSharedCheck_2109_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_ident_x3f_2096_);
lean_inc(v_toLocationLink_2095_);
lean_dec(v_v_2094_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2109_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2100_; lean_object* v_bs_x27_2101_; lean_object* v___x_2103_; 
v___x_2100_ = lean_unsigned_to_nat(0u);
v_bs_x27_2101_ = lean_array_uset(v_bs_2092_, v_i_2091_, v___x_2100_);
if (v_isShared_2099_ == 0)
{
v___x_2103_ = v___x_2098_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_toLocationLink_2095_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_ident_x3f_2096_);
v___x_2103_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
size_t v___x_2104_; size_t v___x_2105_; lean_object* v___x_2106_; 
lean_ctor_set_uint8(v___x_2103_, sizeof(void*)*2, v___x_2093_);
v___x_2104_ = ((size_t)1ULL);
v___x_2105_ = lean_usize_add(v_i_2091_, v___x_2104_);
v___x_2106_ = lean_array_uset(v_bs_x27_2101_, v_i_2091_, v___x_2103_);
v_i_2091_ = v___x_2105_;
v_bs_2092_ = v___x_2106_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1___boxed(lean_object* v_sz_2110_, lean_object* v_i_2111_, lean_object* v_bs_2112_){
_start:
{
size_t v_sz_boxed_2113_; size_t v_i_boxed_2114_; lean_object* v_res_2115_; 
v_sz_boxed_2113_ = lean_unbox_usize(v_sz_2110_);
lean_dec(v_sz_2110_);
v_i_boxed_2114_ = lean_unbox_usize(v_i_2111_);
lean_dec(v_i_2111_);
v_res_2115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(v_sz_boxed_2113_, v_i_boxed_2114_, v_bs_2112_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksDefault(lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v___x_2122_; lean_object* v_a_2123_; lean_object* v___x_2124_; size_t v_sz_2125_; size_t v___x_2126_; lean_object* v___x_2127_; 
lean_inc_ref(v_a_2116_);
v___x_2122_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(v_a_2116_, v_a_2120_);
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref(v___x_2122_);
v___x_2124_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v_sz_2125_ = lean_array_size(v_a_2123_);
v___x_2126_ = ((size_t)0ULL);
v___x_2127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_a_2123_, v_sz_2125_, v___x_2126_, v___x_2124_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
lean_dec(v_a_2123_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2137_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2130_ = v___x_2127_;
v_isShared_2131_ = v_isSharedCheck_2137_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2127_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2137_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
size_t v_sz_2132_; lean_object* v___x_2133_; lean_object* v___x_2135_; 
v_sz_2132_ = lean_array_size(v_a_2128_);
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(v_sz_2132_, v___x_2126_, v_a_2128_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v___x_2133_);
v___x_2135_ = v___x_2130_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
else
{
return v___x_2127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksDefault___boxed(lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_Server_locationLinksDefault(v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_);
lean_dec(v_a_2142_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(lean_object* v_name_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___x_2148_; lean_object* v_env_2149_; lean_object* v___x_2150_; lean_object* v_toEnvExtension_2151_; lean_object* v_asyncMode_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2148_ = lean_st_ref_get(v___y_2146_);
v_env_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc_ref(v_env_2149_);
lean_dec(v___x_2148_);
v___x_2150_ = l_Lean_errorExplanationExt;
v_toEnvExtension_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc_ref(v_toEnvExtension_2151_);
v_asyncMode_2152_ = lean_ctor_get(v_toEnvExtension_2151_, 2);
lean_inc(v_asyncMode_2152_);
lean_dec_ref(v_toEnvExtension_2151_);
v___x_2153_ = lean_box(1);
v___x_2154_ = lean_box(0);
v___x_2155_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2153_, v___x_2150_, v_env_2149_, v_asyncMode_2152_, v___x_2154_);
lean_dec(v_asyncMode_2152_);
v___x_2156_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2155_, v_name_2145_);
lean_dec(v___x_2155_);
v___x_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg___boxed(lean_object* v_name_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_name_2158_, v___y_2159_);
lean_dec(v___y_2159_);
lean_dec(v_name_2158_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0(lean_object* v_name_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_name_2162_, v___y_2167_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___boxed(lean_object* v_name_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0(v_name_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v_name_2170_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromErrorNameInfo(lean_object* v_eni_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_){
_start:
{
lean_object* v_stx_2185_; lean_object* v_errorName_2186_; lean_object* v___x_2187_; lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2268_; 
v_stx_2185_ = lean_ctor_get(v_eni_2178_, 0);
v_errorName_2186_ = lean_ctor_get(v_eni_2178_, 1);
v___x_2187_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_errorName_2186_, v_a_2183_);
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2190_ = v___x_2187_;
v_isShared_2191_ = v_isSharedCheck_2268_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2187_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2268_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
if (lean_obj_tag(v_a_2188_) == 1)
{
lean_object* v_val_2192_; lean_object* v_declLoc_x3f_2193_; 
v_val_2192_ = lean_ctor_get(v_a_2188_, 0);
lean_inc(v_val_2192_);
lean_dec_ref(v_a_2188_);
v_declLoc_x3f_2193_ = lean_ctor_get(v_val_2192_, 2);
lean_inc(v_declLoc_x3f_2193_);
lean_dec(v_val_2192_);
if (lean_obj_tag(v_declLoc_x3f_2193_) == 1)
{
lean_object* v_val_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2259_; 
lean_del_object(v___x_2190_);
v_val_2194_ = lean_ctor_get(v_declLoc_x3f_2193_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_declLoc_x3f_2193_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2196_ = v_declLoc_x3f_2193_;
v_isShared_2197_ = v_isSharedCheck_2259_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_val_2194_);
lean_dec(v_declLoc_x3f_2193_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2259_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v_module_2198_; lean_object* v_range_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2258_; 
v_module_2198_ = lean_ctor_get(v_val_2194_, 0);
v_range_2199_ = lean_ctor_get(v_val_2194_, 1);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_val_2194_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2201_ = v_val_2194_;
v_isShared_2202_ = v_isSharedCheck_2258_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_range_2199_);
lean_inc(v_module_2198_);
lean_dec(v_val_2194_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2258_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_Server_documentUriFromModule_x3f(v_module_2198_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2240_; 
lean_del_object(v___x_2201_);
lean_del_object(v___x_2196_);
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2240_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2240_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
if (lean_obj_tag(v_a_2204_) == 1)
{
lean_object* v_val_2208_; lean_object* v___x_2209_; lean_object* v___y_2211_; uint8_t v___x_2222_; lean_object* v___x_2223_; 
v_val_2208_ = lean_ctor_get(v_a_2204_, 0);
lean_inc(v_val_2208_);
lean_dec_ref(v_a_2204_);
v___x_2209_ = l_Lean_DeclarationRange_toLspRange(v_range_2199_);
v___x_2222_ = 1;
v___x_2223_ = l_Lean_Syntax_getRange_x3f(v_stx_2185_, v___x_2222_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v___x_2224_; 
lean_dec_ref(v_a_2179_);
v___x_2224_ = lean_box(0);
v___y_2211_ = v___x_2224_;
goto v___jp_2210_;
}
else
{
lean_object* v_doc_2225_; lean_object* v_val_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2235_; 
v_doc_2225_ = lean_ctor_get(v_a_2179_, 0);
lean_inc_ref(v_doc_2225_);
lean_dec_ref(v_a_2179_);
v_val_2226_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2228_ = v___x_2223_;
v_isShared_2229_ = v_isSharedCheck_2235_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_val_2226_);
lean_dec(v___x_2223_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2235_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v_text_2230_; lean_object* v___x_2231_; lean_object* v___x_2233_; 
v_text_2230_ = lean_ctor_get(v_doc_2225_, 3);
lean_inc_ref(v_text_2230_);
lean_dec_ref(v_doc_2225_);
v___x_2231_ = l_Lean_Syntax_Range_toLspRange(v_text_2230_, v_val_2226_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v___x_2231_);
v___x_2233_ = v___x_2228_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
v___y_2211_ = v___x_2233_;
goto v___jp_2210_;
}
}
}
v___jp_2210_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
lean_inc_ref(v___x_2209_);
v___x_2212_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2212_, 0, v___y_2211_);
lean_ctor_set(v___x_2212_, 1, v_val_2208_);
lean_ctor_set(v___x_2212_, 2, v___x_2209_);
lean_ctor_set(v___x_2212_, 3, v___x_2209_);
v___x_2213_ = lean_box(0);
v___x_2214_ = 0;
v___x_2215_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2215_, 0, v___x_2212_);
lean_ctor_set(v___x_2215_, 1, v___x_2213_);
lean_ctor_set_uint8(v___x_2215_, sizeof(void*)*2, v___x_2214_);
v___x_2216_ = lean_unsigned_to_nat(1u);
v___x_2217_ = lean_mk_empty_array_with_capacity(v___x_2216_);
v___x_2218_ = lean_array_push(v___x_2217_, v___x_2215_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2218_);
v___x_2220_ = v___x_2206_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v___x_2236_; lean_object* v___x_2238_; 
lean_dec(v_a_2204_);
lean_dec_ref(v_range_2199_);
lean_dec_ref(v_a_2179_);
v___x_2236_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2236_);
v___x_2238_ = v___x_2206_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2236_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2257_; 
lean_dec_ref(v_range_2199_);
lean_dec_ref(v_a_2179_);
v_a_2241_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2243_ = v___x_2203_;
v_isShared_2244_ = v_isSharedCheck_2257_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2203_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2257_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v_ref_2245_; lean_object* v___x_2246_; lean_object* v___x_2248_; 
v_ref_2245_ = lean_ctor_get(v_a_2182_, 5);
v___x_2246_ = lean_io_error_to_string(v_a_2241_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set_tag(v___x_2196_, 3);
lean_ctor_set(v___x_2196_, 0, v___x_2246_);
v___x_2248_ = v___x_2196_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2249_ = l_Lean_MessageData_ofFormat(v___x_2248_);
lean_inc(v_ref_2245_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 1, v___x_2249_);
lean_ctor_set(v___x_2201_, 0, v_ref_2245_);
v___x_2251_ = v___x_2201_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_ref_2245_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2253_; 
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v___x_2251_);
v___x_2253_ = v___x_2243_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
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
lean_object* v___x_2260_; lean_object* v___x_2262_; 
lean_dec(v_declLoc_x3f_2193_);
lean_dec_ref(v_a_2179_);
v___x_2260_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2260_);
v___x_2262_ = v___x_2190_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
else
{
lean_object* v___x_2264_; lean_object* v___x_2266_; 
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2179_);
v___x_2264_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2264_);
v___x_2266_ = v___x_2190_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromErrorNameInfo___boxed(lean_object* v_eni_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_Server_locationLinksFromErrorNameInfo(v_eni_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_);
lean_dec(v_a_2274_);
lean_dec_ref(v_a_2273_);
lean_dec(v_a_2272_);
lean_dec_ref(v_a_2271_);
lean_dec_ref(v_eni_2269_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(lean_object* v_e_2277_, lean_object* v_a_2278_){
_start:
{
switch(lean_obj_tag(v_e_2277_))
{
case 4:
{
lean_object* v_declName_2280_; lean_object* v___x_2281_; 
v_declName_2280_ = lean_ctor_get(v_e_2277_, 0);
lean_inc(v_declName_2280_);
lean_dec_ref(v_e_2277_);
v___x_2281_ = l_Lean_Meta_isInstance___redArg(v_declName_2280_, v_a_2278_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2297_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2284_ = v___x_2281_;
v_isShared_2285_ = v_isSharedCheck_2297_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2281_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2297_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
uint8_t v___x_2286_; 
v___x_2286_ = lean_unbox(v_a_2282_);
lean_dec(v_a_2282_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; lean_object* v___x_2289_; 
lean_dec(v_declName_2280_);
v___x_2287_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2287_);
v___x_2289_ = v___x_2284_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
else
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2295_; 
v___x_2291_ = lean_unsigned_to_nat(1u);
v___x_2292_ = lean_mk_empty_array_with_capacity(v___x_2291_);
v___x_2293_ = lean_array_push(v___x_2292_, v_declName_2280_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2293_);
v___x_2295_ = v___x_2284_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec(v_declName_2280_);
v_a_2298_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2281_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2281_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
case 5:
{
lean_object* v_fn_2306_; lean_object* v_arg_2307_; lean_object* v___x_2308_; 
v_fn_2306_ = lean_ctor_get(v_e_2277_, 0);
lean_inc_ref(v_fn_2306_);
v_arg_2307_ = lean_ctor_get(v_e_2277_, 1);
lean_inc_ref(v_arg_2307_);
lean_dec_ref(v_e_2277_);
v___x_2308_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_fn_2306_, v_a_2278_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2310_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref(v___x_2308_);
v___x_2310_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_arg_2307_, v_a_2278_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2319_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2313_ = v___x_2310_;
v_isShared_2314_ = v_isSharedCheck_2319_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2310_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2319_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2315_ = l_Array_append___redArg(v_a_2311_, v_a_2309_);
lean_dec(v_a_2309_);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 0, v___x_2315_);
v___x_2317_ = v___x_2313_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
else
{
lean_dec(v_a_2309_);
return v___x_2310_;
}
}
else
{
lean_dec_ref(v_arg_2307_);
return v___x_2308_;
}
}
case 10:
{
lean_object* v_expr_2320_; 
v_expr_2320_ = lean_ctor_get(v_e_2277_, 1);
lean_inc_ref(v_expr_2320_);
lean_dec_ref(v_e_2277_);
v_e_2277_ = v_expr_2320_;
goto _start;
}
default: 
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_dec_ref(v_e_2277_);
v___x_2322_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
return v___x_2323_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg___boxed(lean_object* v_e_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_e_2324_, v_a_2325_);
lean_dec(v_a_2325_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances(lean_object* v_e_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_e_2328_, v_a_2333_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___boxed(lean_object* v_e_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances(v_e_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
lean_dec(v_a_2341_);
lean_dec_ref(v_a_2340_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
lean_dec_ref(v_a_2337_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromInstanceProjection(lean_object* v_e_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = l_Lean_Expr_getAppFn(v_e_2344_);
v___x_2352_ = l_Lean_Expr_consumeMData(v___x_2351_);
lean_dec_ref(v___x_2351_);
if (lean_obj_tag(v___x_2352_) == 4)
{
lean_object* v_declName_2353_; lean_object* v___x_2354_; 
v_declName_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_declName_2353_);
lean_dec_ref(v___x_2352_);
lean_inc(v_a_2349_);
lean_inc_ref(v_a_2348_);
lean_inc(v_a_2347_);
lean_inc_ref(v_a_2346_);
v___x_2354_ = l_Lean_Server_getInstanceProjectionArg_x3f(v_e_2344_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2389_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2357_ = v___x_2354_;
v_isShared_2358_ = v_isSharedCheck_2389_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2354_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2389_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
if (lean_obj_tag(v_a_2355_) == 1)
{
lean_object* v_val_2359_; lean_object* v___x_2360_; 
lean_del_object(v___x_2357_);
v_val_2359_ = lean_ctor_get(v_a_2355_, 0);
lean_inc(v_val_2359_);
lean_dec_ref(v_a_2355_);
v___x_2360_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_val_2359_, v_a_2349_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2362_; size_t v_sz_2363_; size_t v___x_2364_; lean_object* v___x_2365_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref(v___x_2360_);
v___x_2362_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v_sz_2363_ = lean_array_size(v_a_2361_);
v___x_2364_ = ((size_t)0ULL);
lean_inc_ref(v_a_2348_);
lean_inc_ref(v_a_2345_);
v___x_2365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_a_2361_, v_sz_2363_, v___x_2364_, v___x_2362_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
lean_dec(v_a_2361_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; lean_object* v___x_2367_; 
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_a_2366_);
lean_dec_ref(v___x_2365_);
v___x_2367_ = l_Lean_Server_locationLinksFromDecl(v_declName_2353_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
lean_dec(v_a_2349_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2376_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2370_ = v___x_2367_;
v_isShared_2371_ = v_isSharedCheck_2376_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2367_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2376_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; lean_object* v___x_2374_; 
v___x_2372_ = l_Array_append___redArg(v_a_2366_, v_a_2368_);
lean_dec(v_a_2368_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 0, v___x_2372_);
v___x_2374_ = v___x_2370_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
else
{
lean_dec(v_a_2366_);
return v___x_2367_;
}
}
else
{
lean_dec(v_declName_2353_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec_ref(v_a_2345_);
return v___x_2365_;
}
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v_declName_2353_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec_ref(v_a_2345_);
v_a_2377_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2360_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2360_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
else
{
lean_object* v___x_2385_; lean_object* v___x_2387_; 
lean_dec(v_a_2355_);
lean_dec(v_declName_2353_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec_ref(v_a_2345_);
v___x_2385_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2385_);
v___x_2387_ = v___x_2357_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec(v_declName_2353_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec_ref(v_a_2345_);
v_a_2390_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2354_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2354_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
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
else
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
lean_dec_ref(v___x_2352_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec_ref(v_a_2345_);
lean_dec_ref(v_e_2344_);
v___x_2398_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
return v___x_2399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromInstanceProjection___boxed(lean_object* v_e_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lean_Server_locationLinksFromInstanceProjection(v_e_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(lean_object* v_as_2408_, size_t v_sz_2409_, size_t v_i_2410_, lean_object* v_b_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v_newLL_2419_; uint8_t v___x_2424_; 
v___x_2424_ = lean_usize_dec_lt(v_i_2410_, v_sz_2409_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; 
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec_ref(v___y_2412_);
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v_b_2411_);
return v___x_2425_;
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2427_; 
v_a_2426_ = lean_array_uget_borrowed(v_as_2408_, v_i_2410_);
v___x_2427_ = l_Lean_Expr_consumeMData(v_a_2426_);
switch(lean_obj_tag(v___x_2427_))
{
case 4:
{
lean_object* v_declName_2428_; lean_object* v___x_2429_; 
v_declName_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_declName_2428_);
lean_dec_ref(v___x_2427_);
lean_inc_ref(v___y_2415_);
lean_inc_ref(v___y_2412_);
v___x_2429_ = l_Lean_Server_locationLinksFromDecl(v_declName_2428_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref(v___x_2429_);
v_newLL_2419_ = v_a_2430_;
goto v___jp_2418_;
}
else
{
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec_ref(v_b_2411_);
return v___x_2429_;
}
}
case 1:
{
lean_object* v_fvarId_2431_; lean_object* v___x_2432_; 
v_fvarId_2431_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_fvarId_2431_);
lean_dec_ref(v___x_2427_);
lean_inc_ref(v___y_2412_);
v___x_2432_ = l_Lean_Server_locationLinksFromBinder___redArg(v_fvarId_2431_, v___y_2412_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref(v___x_2432_);
v_newLL_2419_ = v_a_2433_;
goto v___jp_2418_;
}
else
{
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec_ref(v_b_2411_);
return v___x_2432_;
}
}
default: 
{
lean_object* v___x_2434_; 
lean_dec_ref(v___x_2427_);
lean_inc(v___y_2416_);
lean_inc_ref(v___y_2415_);
lean_inc(v___y_2414_);
lean_inc_ref(v___y_2413_);
lean_inc_ref(v___y_2412_);
lean_inc(v_a_2426_);
v___x_2434_ = l_Lean_Server_locationLinksFromInstanceProjection(v_a_2426_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref(v___x_2434_);
v_newLL_2419_ = v_a_2435_;
goto v___jp_2418_;
}
else
{
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec_ref(v_b_2411_);
return v___x_2434_;
}
}
}
}
v___jp_2418_:
{
lean_object* v___x_2420_; size_t v___x_2421_; size_t v___x_2422_; 
v___x_2420_ = l_Array_append___redArg(v_b_2411_, v_newLL_2419_);
lean_dec_ref(v_newLL_2419_);
v___x_2421_ = ((size_t)1ULL);
v___x_2422_ = lean_usize_add(v_i_2410_, v___x_2421_);
v_i_2410_ = v___x_2422_;
v_b_2411_ = v___x_2420_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0___boxed(lean_object* v_as_2436_, lean_object* v_sz_2437_, lean_object* v_i_2438_, lean_object* v_b_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
size_t v_sz_boxed_2446_; size_t v_i_boxed_2447_; lean_object* v_res_2448_; 
v_sz_boxed_2446_ = lean_unbox_usize(v_sz_2437_);
lean_dec(v_sz_2437_);
v_i_boxed_2447_ = lean_unbox_usize(v_i_2438_);
lean_dec(v_i_2438_);
v_res_2448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(v_as_2436_, v_sz_boxed_2446_, v_i_boxed_2447_, v_b_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec_ref(v_as_2436_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromTermInfo(lean_object* v_ti_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
uint8_t v_kind_2456_; lean_object* v___x_2457_; 
v_kind_2456_ = lean_ctor_get_uint8(v_a_2450_, sizeof(void*)*4);
lean_inc(v_a_2454_);
lean_inc_ref(v_a_2453_);
lean_inc(v_a_2452_);
lean_inc_ref(v_a_2451_);
v___x_2457_ = l_Lean_Server_GoToKind_determineTargetExprs(v_kind_2456_, v_ti_2449_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2459_; size_t v_sz_2460_; size_t v___x_2461_; lean_object* v___x_2462_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref(v___x_2457_);
v___x_2459_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v_sz_2460_ = lean_array_size(v_a_2458_);
v___x_2461_ = ((size_t)0ULL);
v___x_2462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(v_a_2458_, v_sz_2460_, v___x_2461_, v___x_2459_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
lean_dec(v_a_2458_);
return v___x_2462_;
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec_ref(v_a_2450_);
v_a_2463_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2457_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2457_);
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
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromTermInfo___boxed(lean_object* v_ti_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lean_Server_locationLinksFromTermInfo(v_ti_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDelabTermInfo(lean_object* v_dti_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_){
_start:
{
lean_object* v_location_x3f_2486_; 
v_location_x3f_2486_ = lean_ctor_get(v_dti_2479_, 1);
lean_inc(v_location_x3f_2486_);
if (lean_obj_tag(v_location_x3f_2486_) == 1)
{
lean_object* v_val_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2556_; 
v_val_2487_ = lean_ctor_get(v_location_x3f_2486_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v_location_x3f_2486_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2489_ = v_location_x3f_2486_;
v_isShared_2490_ = v_isSharedCheck_2556_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_val_2487_);
lean_dec(v_location_x3f_2486_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2556_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v_toTermInfo_2491_; lean_object* v_module_2492_; lean_object* v_range_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2555_; 
v_toTermInfo_2491_ = lean_ctor_get(v_dti_2479_, 0);
v_module_2492_ = lean_ctor_get(v_val_2487_, 0);
v_range_2493_ = lean_ctor_get(v_val_2487_, 1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_val_2487_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2495_ = v_val_2487_;
v_isShared_2496_ = v_isSharedCheck_2555_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_range_2493_);
lean_inc(v_module_2492_);
lean_dec(v_val_2487_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2555_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_Server_documentUriFromModule_x3f(v_module_2492_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2537_; 
lean_del_object(v___x_2495_);
lean_del_object(v___x_2489_);
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2500_ = v___x_2497_;
v_isShared_2501_ = v_isSharedCheck_2537_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2537_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
if (lean_obj_tag(v_a_2498_) == 1)
{
lean_object* v_val_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2535_; 
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
v_val_2502_ = lean_ctor_get(v_a_2498_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v_a_2498_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2504_ = v_a_2498_;
v_isShared_2505_ = v_isSharedCheck_2535_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_val_2502_);
lean_dec(v_a_2498_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2535_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v___y_2508_; lean_object* v___x_2520_; 
v___x_2506_ = l_Lean_DeclarationRange_toLspRange(v_range_2493_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set_tag(v___x_2504_, 13);
lean_ctor_set(v___x_2504_, 0, v_dti_2479_);
v___x_2520_ = v___x_2504_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_dti_2479_);
v___x_2520_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2519_;
}
v___jp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2517_; 
lean_inc_ref(v___x_2506_);
v___x_2509_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2509_, 0, v___y_2508_);
lean_ctor_set(v___x_2509_, 1, v_val_2502_);
lean_ctor_set(v___x_2509_, 2, v___x_2506_);
lean_ctor_set(v___x_2509_, 3, v___x_2506_);
v___x_2510_ = lean_box(0);
v___x_2511_ = 0;
v___x_2512_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2512_, 0, v___x_2509_);
lean_ctor_set(v___x_2512_, 1, v___x_2510_);
lean_ctor_set_uint8(v___x_2512_, sizeof(void*)*2, v___x_2511_);
v___x_2513_ = lean_unsigned_to_nat(1u);
v___x_2514_ = lean_mk_empty_array_with_capacity(v___x_2513_);
v___x_2515_ = lean_array_push(v___x_2514_, v___x_2512_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2515_);
v___x_2517_ = v___x_2500_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
v_reusejp_2519_:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Lean_Elab_Info_range_x3f(v___x_2520_);
lean_dec_ref(v___x_2520_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v___x_2522_; 
lean_dec_ref(v_a_2480_);
v___x_2522_ = lean_box(0);
v___y_2508_ = v___x_2522_;
goto v___jp_2507_;
}
else
{
lean_object* v_doc_2523_; lean_object* v_val_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2533_; 
v_doc_2523_ = lean_ctor_get(v_a_2480_, 0);
lean_inc_ref(v_doc_2523_);
lean_dec_ref(v_a_2480_);
v_val_2524_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2526_ = v___x_2521_;
v_isShared_2527_ = v_isSharedCheck_2533_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_val_2524_);
lean_dec(v___x_2521_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2533_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v_text_2528_; lean_object* v___x_2529_; lean_object* v___x_2531_; 
v_text_2528_ = lean_ctor_get(v_doc_2523_, 3);
lean_inc_ref(v_text_2528_);
lean_dec_ref(v_doc_2523_);
v___x_2529_ = l_Lean_Syntax_Range_toLspRange(v_text_2528_, v_val_2524_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 0, v___x_2529_);
v___x_2531_ = v___x_2526_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2529_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
v___y_2508_ = v___x_2531_;
goto v___jp_2507_;
}
}
}
}
}
}
else
{
lean_object* v___x_2536_; 
lean_inc_ref(v_toTermInfo_2491_);
lean_del_object(v___x_2500_);
lean_dec(v_a_2498_);
lean_dec_ref(v_range_2493_);
lean_dec_ref(v_dti_2479_);
v___x_2536_ = l_Lean_Server_locationLinksFromTermInfo(v_toTermInfo_2491_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
return v___x_2536_;
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2554_; 
lean_dec_ref(v_range_2493_);
lean_dec(v_a_2484_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
lean_dec_ref(v_a_2480_);
lean_dec_ref(v_dti_2479_);
v_a_2538_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2540_ = v___x_2497_;
v_isShared_2541_ = v_isSharedCheck_2554_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2497_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2554_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v_ref_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
v_ref_2542_ = lean_ctor_get(v_a_2483_, 5);
lean_inc(v_ref_2542_);
lean_dec_ref(v_a_2483_);
v___x_2543_ = lean_io_error_to_string(v_a_2538_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set_tag(v___x_2489_, 3);
lean_ctor_set(v___x_2489_, 0, v___x_2543_);
v___x_2545_ = v___x_2489_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2543_);
v___x_2545_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2546_; lean_object* v___x_2548_; 
v___x_2546_ = l_Lean_MessageData_ofFormat(v___x_2545_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 1, v___x_2546_);
lean_ctor_set(v___x_2495_, 0, v_ref_2542_);
v___x_2548_ = v___x_2495_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_ref_2542_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v___x_2546_);
v___x_2548_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
lean_object* v___x_2550_; 
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v___x_2548_);
v___x_2550_ = v___x_2540_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2548_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
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
lean_object* v_toTermInfo_2557_; lean_object* v___x_2558_; 
lean_dec(v_location_x3f_2486_);
v_toTermInfo_2557_ = lean_ctor_get(v_dti_2479_, 0);
lean_inc_ref(v_toTermInfo_2557_);
lean_dec_ref(v_dti_2479_);
v___x_2558_ = l_Lean_Server_locationLinksFromTermInfo(v_toTermInfo_2557_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
return v___x_2558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDelabTermInfo___boxed(lean_object* v_dti_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_Server_locationLinksFromDelabTermInfo(v_dti_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(lean_object* v_e_2567_, lean_object* v___y_2568_){
_start:
{
uint8_t v___x_2570_; 
v___x_2570_ = l_Lean_Expr_hasMVar(v_e_2567_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; 
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v_e_2567_);
return v___x_2571_;
}
else
{
lean_object* v___x_2572_; lean_object* v_mctx_2573_; lean_object* v___x_2574_; lean_object* v_fst_2575_; lean_object* v_snd_2576_; lean_object* v___x_2577_; lean_object* v_cache_2578_; lean_object* v_zetaDeltaFVarIds_2579_; lean_object* v_postponed_2580_; lean_object* v_diag_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2590_; 
v___x_2572_ = lean_st_ref_get(v___y_2568_);
v_mctx_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc_ref(v_mctx_2573_);
lean_dec(v___x_2572_);
v___x_2574_ = l_Lean_instantiateMVarsCore(v_mctx_2573_, v_e_2567_);
v_fst_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_fst_2575_);
v_snd_2576_ = lean_ctor_get(v___x_2574_, 1);
lean_inc(v_snd_2576_);
lean_dec_ref(v___x_2574_);
v___x_2577_ = lean_st_ref_take(v___y_2568_);
v_cache_2578_ = lean_ctor_get(v___x_2577_, 1);
v_zetaDeltaFVarIds_2579_ = lean_ctor_get(v___x_2577_, 2);
v_postponed_2580_ = lean_ctor_get(v___x_2577_, 3);
v_diag_2581_ = lean_ctor_get(v___x_2577_, 4);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2590_ == 0)
{
lean_object* v_unused_2591_; 
v_unused_2591_ = lean_ctor_get(v___x_2577_, 0);
lean_dec(v_unused_2591_);
v___x_2583_ = v___x_2577_;
v_isShared_2584_ = v_isSharedCheck_2590_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_diag_2581_);
lean_inc(v_postponed_2580_);
lean_inc(v_zetaDeltaFVarIds_2579_);
lean_inc(v_cache_2578_);
lean_dec(v___x_2577_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2590_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v_snd_2576_);
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_snd_2576_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v_cache_2578_);
lean_ctor_set(v_reuseFailAlloc_2589_, 2, v_zetaDeltaFVarIds_2579_);
lean_ctor_set(v_reuseFailAlloc_2589_, 3, v_postponed_2580_);
lean_ctor_set(v_reuseFailAlloc_2589_, 4, v_diag_2581_);
v___x_2586_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2587_ = lean_st_ref_set(v___y_2568_, v___x_2586_);
v___x_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2588_, 0, v_fst_2575_);
return v___x_2588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg___boxed(lean_object* v_e_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(v_e_2592_, v___y_2593_);
lean_dec(v___y_2593_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0(lean_object* v_e_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(v_e_2596_, v___y_2599_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___boxed(lean_object* v_e_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0(v_e_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2605_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromFieldInfo(lean_object* v_fi_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_){
_start:
{
uint8_t v_kind_2619_; uint8_t v___x_2620_; uint8_t v___x_2621_; 
v_kind_2619_ = lean_ctor_get_uint8(v_a_2613_, sizeof(void*)*4);
v___x_2620_ = 2;
v___x_2621_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_2619_, v___x_2620_);
if (v___x_2621_ == 0)
{
lean_object* v_projName_2622_; lean_object* v___x_2623_; 
v_projName_2622_ = lean_ctor_get(v_fi_2612_, 0);
lean_inc(v_projName_2622_);
lean_dec_ref(v_fi_2612_);
v___x_2623_ = l_Lean_Server_locationLinksFromDecl(v_projName_2622_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_);
lean_dec(v_a_2617_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
return v___x_2623_;
}
else
{
lean_object* v_val_2624_; lean_object* v___x_2625_; 
v_val_2624_ = lean_ctor_get(v_fi_2612_, 3);
lean_inc_ref(v_val_2624_);
lean_dec_ref(v_fi_2612_);
lean_inc(v_a_2617_);
lean_inc_ref(v_a_2616_);
lean_inc(v_a_2615_);
lean_inc_ref(v_a_2614_);
v___x_2625_ = lean_infer_type(v_val_2624_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2627_; lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2640_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref(v___x_2625_);
v___x_2627_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(v_a_2626_, v_a_2615_);
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2630_ = v___x_2627_;
v_isShared_2631_ = v_isSharedCheck_2640_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2627_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2640_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2632_ = l_Lean_Expr_getAppFn(v_a_2628_);
lean_dec(v_a_2628_);
v___x_2633_ = l_Lean_Expr_constName_x3f(v___x_2632_);
lean_dec_ref(v___x_2632_);
if (lean_obj_tag(v___x_2633_) == 1)
{
lean_object* v_val_2634_; lean_object* v___x_2635_; 
lean_del_object(v___x_2630_);
v_val_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_val_2634_);
lean_dec_ref(v___x_2633_);
v___x_2635_ = l_Lean_Server_locationLinksFromDecl(v_val_2634_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_);
lean_dec(v_a_2617_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
return v___x_2635_;
}
else
{
lean_object* v___x_2636_; lean_object* v___x_2638_; 
lean_dec(v___x_2633_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
lean_dec_ref(v_a_2613_);
v___x_2636_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2636_);
v___x_2638_ = v___x_2630_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
lean_dec_ref(v_a_2613_);
v_a_2641_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2625_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2625_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromFieldInfo___boxed(lean_object* v_fi_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_Server_locationLinksFromFieldInfo(v_fi_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromOptionInfo(lean_object* v_i_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v_declName_2664_; lean_object* v___x_2665_; 
v_declName_2664_ = lean_ctor_get(v_i_2657_, 2);
lean_inc(v_declName_2664_);
lean_dec_ref(v_i_2657_);
v___x_2665_ = l_Lean_Server_locationLinksFromDecl(v_declName_2664_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromOptionInfo___boxed(lean_object* v_i_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_Server_locationLinksFromOptionInfo(v_i_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
lean_dec(v_a_2671_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromCommandInfo___redArg(lean_object* v_i_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_){
_start:
{
lean_object* v_elaborator_2681_; 
v_elaborator_2681_ = lean_ctor_get(v_i_2674_, 0);
if (lean_obj_tag(v_elaborator_2681_) == 1)
{
lean_object* v_pre_2682_; 
v_pre_2682_ = lean_ctor_get(v_elaborator_2681_, 0);
if (lean_obj_tag(v_pre_2682_) == 0)
{
lean_object* v_str_2683_; lean_object* v___x_2684_; uint8_t v___x_2685_; 
v_str_2683_ = lean_ctor_get(v_elaborator_2681_, 1);
v___x_2684_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__3));
v___x_2685_ = lean_string_dec_eq(v_str_2683_, v___x_2684_);
if (v___x_2685_ == 0)
{
lean_dec_ref(v_a_2675_);
lean_dec_ref(v_i_2674_);
goto v___jp_2678_;
}
else
{
uint8_t v_kind_2686_; uint8_t v___x_2687_; uint8_t v___x_2688_; 
v_kind_2686_ = lean_ctor_get_uint8(v_a_2675_, sizeof(void*)*4);
v___x_2687_ = 2;
v___x_2688_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_2686_, v___x_2687_);
if (v___x_2688_ == 0)
{
lean_object* v___x_2689_; 
v___x_2689_ = l_Lean_Server_locationLinksFromImport___redArg(v_i_2674_, v_a_2675_, v_a_2676_);
return v___x_2689_;
}
else
{
lean_dec_ref(v_a_2675_);
lean_dec_ref(v_i_2674_);
goto v___jp_2678_;
}
}
}
else
{
lean_dec_ref(v_a_2675_);
lean_dec_ref(v_i_2674_);
goto v___jp_2678_;
}
}
else
{
lean_dec_ref(v_a_2675_);
lean_dec_ref(v_i_2674_);
goto v___jp_2678_;
}
v___jp_2678_:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2679_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2679_);
return v___x_2680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromCommandInfo___redArg___boxed(lean_object* v_i_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Lean_Server_locationLinksFromCommandInfo___redArg(v_i_2690_, v_a_2691_, v_a_2692_);
lean_dec_ref(v_a_2692_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromCommandInfo(lean_object* v_i_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_Server_locationLinksFromCommandInfo___redArg(v_i_2695_, v_a_2696_, v_a_2699_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromCommandInfo___boxed(lean_object* v_i_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_Server_locationLinksFromCommandInfo(v_i_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___lam__0(uint8_t v_kind_2711_, lean_object* v_ll_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
uint8_t v___y_2720_; uint8_t v___x_2732_; uint8_t v___x_2733_; 
v___x_2732_ = 0;
v___x_2733_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_2711_, v___x_2732_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; lean_object* v___x_2735_; uint8_t v___x_2736_; 
v___x_2734_ = lean_array_get_size(v_ll_2712_);
v___x_2735_ = lean_unsigned_to_nat(0u);
v___x_2736_ = lean_nat_dec_eq(v___x_2734_, v___x_2735_);
v___y_2720_ = v___x_2736_;
goto v___jp_2719_;
}
else
{
v___y_2720_ = v___x_2733_;
goto v___jp_2719_;
}
v___jp_2719_:
{
if (v___y_2720_ == 0)
{
lean_object* v___x_2721_; 
lean_dec_ref(v___y_2716_);
lean_dec_ref(v___y_2713_);
v___x_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2721_, 0, v_ll_2712_);
return v___x_2721_;
}
else
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_Server_locationLinksDefault(v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2731_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2725_ = v___x_2722_;
v_isShared_2726_ = v_isSharedCheck_2731_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2731_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2727_; lean_object* v___x_2729_; 
v___x_2727_ = l_Array_append___redArg(v_ll_2712_, v_a_2723_);
lean_dec(v_a_2723_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 0, v___x_2727_);
v___x_2729_ = v___x_2725_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
else
{
lean_dec_ref(v_ll_2712_);
return v___x_2722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___lam__0___boxed(lean_object* v_kind_2737_, lean_object* v_ll_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
uint8_t v_kind_boxed_2745_; lean_object* v_res_2746_; 
v_kind_boxed_2745_ = lean_unbox(v_kind_2737_);
v_res_2746_ = l_Lean_Server_locationLinksOfInfo___lam__0(v_kind_boxed_2745_, v_ll_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
lean_dec(v___y_2743_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___lam__1(lean_object* v_info_2747_, lean_object* v___f_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
switch(lean_obj_tag(v_info_2747_))
{
case 1:
{
lean_object* v_i_2755_; lean_object* v___x_2756_; 
v_i_2755_ = lean_ctor_get(v_info_2747_, 0);
lean_inc_ref(v_i_2755_);
lean_dec_ref(v_info_2747_);
lean_inc(v___y_2753_);
lean_inc_ref(v___y_2752_);
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
lean_inc_ref(v___y_2749_);
v___x_2756_ = l_Lean_Server_locationLinksFromTermInfo(v_i_2755_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2758_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref(v___x_2756_);
v___x_2758_ = lean_apply_7(v___f_2748_, v_a_2757_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, lean_box(0));
return v___x_2758_;
}
else
{
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec_ref(v___f_2748_);
return v___x_2756_;
}
}
case 13:
{
lean_object* v_i_2759_; lean_object* v___x_2760_; 
v_i_2759_ = lean_ctor_get(v_info_2747_, 0);
lean_inc_ref(v_i_2759_);
lean_dec_ref(v_info_2747_);
lean_inc(v___y_2753_);
lean_inc_ref(v___y_2752_);
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
lean_inc_ref(v___y_2749_);
v___x_2760_ = l_Lean_Server_locationLinksFromDelabTermInfo(v_i_2759_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; lean_object* v___x_2762_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref(v___x_2760_);
v___x_2762_ = lean_apply_7(v___f_2748_, v_a_2761_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, lean_box(0));
return v___x_2762_;
}
else
{
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec_ref(v___f_2748_);
return v___x_2760_;
}
}
case 7:
{
lean_object* v_i_2763_; lean_object* v___x_2764_; 
v_i_2763_ = lean_ctor_get(v_info_2747_, 0);
lean_inc_ref(v_i_2763_);
lean_dec_ref(v_info_2747_);
lean_inc(v___y_2753_);
lean_inc_ref(v___y_2752_);
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
lean_inc_ref(v___y_2749_);
v___x_2764_ = l_Lean_Server_locationLinksFromFieldInfo(v_i_2763_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2766_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref(v___x_2764_);
v___x_2766_ = lean_apply_7(v___f_2748_, v_a_2765_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, lean_box(0));
return v___x_2766_;
}
else
{
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec_ref(v___f_2748_);
return v___x_2764_;
}
}
case 5:
{
lean_object* v_i_2767_; lean_object* v___x_2768_; 
v_i_2767_ = lean_ctor_get(v_info_2747_, 0);
lean_inc_ref(v_i_2767_);
lean_dec_ref(v_info_2747_);
lean_inc_ref(v___y_2752_);
lean_inc_ref(v___y_2749_);
v___x_2768_ = l_Lean_Server_locationLinksFromOptionInfo(v_i_2767_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2770_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2769_);
lean_dec_ref(v___x_2768_);
v___x_2770_ = lean_apply_7(v___f_2748_, v_a_2769_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, lean_box(0));
return v___x_2770_;
}
else
{
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec_ref(v___f_2748_);
return v___x_2768_;
}
}
case 3:
{
lean_object* v_i_2771_; lean_object* v___x_2772_; 
v_i_2771_ = lean_ctor_get(v_info_2747_, 0);
lean_inc_ref(v_i_2771_);
lean_dec_ref(v_info_2747_);
lean_inc_ref(v___y_2749_);
v___x_2772_ = l_Lean_Server_locationLinksFromCommandInfo___redArg(v_i_2771_, v___y_2749_, v___y_2752_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; lean_object* v___x_2774_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_a_2773_);
lean_dec_ref(v___x_2772_);
v___x_2774_ = lean_apply_7(v___f_2748_, v_a_2773_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, lean_box(0));
return v___x_2774_;
}
else
{
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec_ref(v___f_2748_);
return v___x_2772_;
}
}
case 6:
{
lean_object* v_i_2775_; lean_object* v___x_2776_; 
v_i_2775_ = lean_ctor_get(v_info_2747_, 0);
lean_inc_ref(v_i_2775_);
lean_dec_ref(v_info_2747_);
lean_inc_ref(v___y_2749_);
v___x_2776_ = l_Lean_Server_locationLinksFromErrorNameInfo(v_i_2775_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
lean_dec_ref(v_i_2775_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2778_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref(v___x_2776_);
v___x_2778_ = lean_apply_7(v___f_2748_, v_a_2777_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, lean_box(0));
return v___x_2778_;
}
else
{
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec_ref(v___f_2748_);
return v___x_2776_;
}
}
case 16:
{
lean_object* v_i_2779_; lean_object* v_name_2780_; lean_object* v___x_2781_; 
v_i_2779_ = lean_ctor_get(v_info_2747_, 0);
lean_inc_ref(v_i_2779_);
lean_dec_ref(v_info_2747_);
v_name_2780_ = lean_ctor_get(v_i_2779_, 1);
lean_inc(v_name_2780_);
lean_dec_ref(v_i_2779_);
lean_inc_ref(v___y_2752_);
lean_inc_ref(v___y_2749_);
v___x_2781_ = l_Lean_Server_locationLinksFromDecl(v_name_2780_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2783_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref(v___x_2781_);
v___x_2783_ = lean_apply_7(v___f_2748_, v_a_2782_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, lean_box(0));
return v___x_2783_;
}
else
{
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec_ref(v___f_2748_);
return v___x_2781_;
}
}
default: 
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
lean_dec_ref(v_info_2747_);
v___x_2784_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_2785_ = lean_apply_7(v___f_2748_, v___x_2784_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, lean_box(0));
return v___x_2785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___lam__1___boxed(lean_object* v_info_2786_, lean_object* v___f_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Lean_Server_locationLinksOfInfo___lam__1(v_info_2786_, v___f_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo(lean_object* v_doc_2795_, uint8_t v_kind_2796_, lean_object* v_ictx_2797_, lean_object* v_infoTree_x3f_2798_){
_start:
{
lean_object* v_ctx_2800_; lean_object* v_info_2801_; lean_object* v_children_2802_; lean_object* v___x_2803_; lean_object* v___f_2804_; lean_object* v___y_2805_; lean_object* v___x_2806_; lean_object* v_ctx_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v_ctx_2800_ = lean_ctor_get(v_ictx_2797_, 0);
lean_inc_ref(v_ctx_2800_);
v_info_2801_ = lean_ctor_get(v_ictx_2797_, 1);
lean_inc_ref(v_info_2801_);
v_children_2802_ = lean_ctor_get(v_ictx_2797_, 2);
lean_inc_ref(v_children_2802_);
lean_dec_ref(v_ictx_2797_);
v___x_2803_ = lean_box(v_kind_2796_);
v___f_2804_ = lean_alloc_closure((void*)(l_Lean_Server_locationLinksOfInfo___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2804_, 0, v___x_2803_);
lean_inc_ref(v_info_2801_);
v___y_2805_ = lean_alloc_closure((void*)(l_Lean_Server_locationLinksOfInfo___lam__1___boxed), 8, 2);
lean_closure_set(v___y_2805_, 0, v_info_2801_);
lean_closure_set(v___y_2805_, 1, v___f_2804_);
lean_inc_ref(v_info_2801_);
v___x_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2806_, 0, v_info_2801_);
v_ctx_2807_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_ctx_2807_, 0, v_doc_2795_);
lean_ctor_set(v_ctx_2807_, 1, v_infoTree_x3f_2798_);
lean_ctor_set(v_ctx_2807_, 2, v___x_2806_);
lean_ctor_set(v_ctx_2807_, 3, v_children_2802_);
lean_ctor_set_uint8(v_ctx_2807_, sizeof(void*)*4, v_kind_2796_);
v___x_2808_ = l_Lean_Elab_Info_lctx(v_info_2801_);
lean_dec_ref(v_info_2801_);
v___x_2809_ = l_Lean_Server_GoToM_run___redArg(v_ctx_2807_, v_ctx_2800_, v___x_2808_, v___y_2805_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___boxed(lean_object* v_doc_2810_, lean_object* v_kind_2811_, lean_object* v_ictx_2812_, lean_object* v_infoTree_x3f_2813_, lean_object* v_a_2814_){
_start:
{
uint8_t v_kind_boxed_2815_; lean_object* v_res_2816_; 
v_kind_boxed_2815_ = lean_unbox(v_kind_2811_);
v_res_2816_ = l_Lean_Server_locationLinksOfInfo(v_doc_2810_, v_kind_boxed_2815_, v_ictx_2812_, v_infoTree_x3f_2813_);
return v_res_2816_;
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
