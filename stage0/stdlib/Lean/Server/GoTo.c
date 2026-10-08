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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* l_Lean_Server_documentUriFromModule_x3f(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
extern lean_object* l_Lean_builtinDeclRanges;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
extern lean_object* l_Lean_instInhabitedDeclarationRanges_default;
extern lean_object* l_Lean_declRangeExt;
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_isInstance___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_Elab_Info_lctx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorIdx___impl___boxed(lean_object*);
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
static const lean_closure_object l_Lean_Server_GoToKind_determineTargetExprs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_GoToKind_determineTargetExprs___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_GoToKind_determineTargetExprs___closed__0 = (const lean_object*)&l_Lean_Server_GoToKind_determineTargetExprs___closed__0_value;
static lean_once_cell_t l_Lean_Server_GoToKind_determineTargetExprs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_GoToKind_determineTargetExprs___closed__1;
static lean_once_cell_t l_Lean_Server_GoToKind_determineTargetExprs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_GoToKind_determineTargetExprs___closed__2;
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
static lean_object* l_Lean_Server_getInstanceProjectionArg_x3f___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Server_GoToKind_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Server_GoToKind_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Server_GoToKind_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_declaration_elim___redArg(lean_object* v_declaration_22_){
_start:
{
lean_inc(v_declaration_22_);
return v_declaration_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_declaration_elim___redArg___boxed(lean_object* v_declaration_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Server_GoToKind_declaration_elim___redArg(v_declaration_23_);
lean_dec(v_declaration_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_declaration_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_declaration_28_){
_start:
{
lean_inc(v_declaration_28_);
return v_declaration_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_declaration_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_declaration_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Server_GoToKind_declaration_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_declaration_32_);
lean_dec(v_declaration_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_definition_elim___redArg(lean_object* v_definition_35_){
_start:
{
lean_inc(v_definition_35_);
return v_definition_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_definition_elim___redArg___boxed(lean_object* v_definition_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Server_GoToKind_definition_elim___redArg(v_definition_36_);
lean_dec(v_definition_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_definition_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_definition_41_){
_start:
{
lean_inc(v_definition_41_);
return v_definition_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_definition_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_definition_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Server_GoToKind_definition_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_definition_45_);
lean_dec(v_definition_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_type_elim___redArg(lean_object* v_type_48_){
_start:
{
lean_inc(v_type_48_);
return v_type_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_type_elim___redArg___boxed(lean_object* v_type_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Server_GoToKind_type_elim___redArg(v_type_49_);
lean_dec(v_type_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_type_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_type_54_){
_start:
{
lean_inc(v_type_54_);
return v_type_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_type_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_type_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Server_GoToKind_type_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_type_58_);
lean_dec(v_type_58_);
return v_res_60_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_instBEqGoToKind_beq(uint8_t v_x_61_, uint8_t v_y_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_63_ = lean_box(v_x_61_);
v___x_64_ = lean_obj_tag_nat(v___x_63_);
lean_dec(v___x_63_);
v___x_65_ = lean_box(v_y_62_);
v___x_66_ = lean_obj_tag_nat(v___x_65_);
lean_dec(v___x_65_);
v___x_67_ = lean_nat_dec_eq(v___x_64_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instBEqGoToKind_beq___boxed(lean_object* v_x_68_, lean_object* v_y_69_){
_start:
{
uint8_t v_x_24__boxed_70_; uint8_t v_y_25__boxed_71_; uint8_t v_res_72_; lean_object* v_r_73_; 
v_x_24__boxed_70_ = lean_unbox(v_x_68_);
v_y_25__boxed_71_ = lean_unbox(v_y_69_);
v_res_72_ = l_Lean_Server_instBEqGoToKind_beq(v_x_24__boxed_70_, v_y_25__boxed_71_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instToJsonGoToKind_toJson(uint8_t v_x_85_){
_start:
{
switch(v_x_85_)
{
case 0:
{
lean_object* v___x_86_; 
v___x_86_ = ((lean_object*)(l_Lean_Server_instToJsonGoToKind_toJson___closed__1));
return v___x_86_;
}
case 1:
{
lean_object* v___x_87_; 
v___x_87_ = ((lean_object*)(l_Lean_Server_instToJsonGoToKind_toJson___closed__3));
return v___x_87_;
}
default: 
{
lean_object* v___x_88_; 
v___x_88_ = ((lean_object*)(l_Lean_Server_instToJsonGoToKind_toJson___closed__5));
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instToJsonGoToKind_toJson___boxed(lean_object* v_x_89_){
_start:
{
uint8_t v_x_67__boxed_90_; lean_object* v_res_91_; 
v_x_67__boxed_90_ = lean_unbox(v_x_89_);
v_res_91_ = l_Lean_Server_instToJsonGoToKind_toJson(v_x_67__boxed_90_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instFromJsonGoToKind_fromJson(lean_object* v_json_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Json_getTag_x3f(v_json_109_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v___x_111_; 
v___x_111_ = ((lean_object*)(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__1));
return v___x_111_;
}
else
{
lean_object* v_val_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v_val_112_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_val_112_);
lean_dec_ref_known(v___x_110_, 1);
v___x_113_ = ((lean_object*)(l_Lean_Server_instToJsonGoToKind_toJson___closed__4));
v___x_114_ = lean_string_dec_eq(v_val_112_, v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = ((lean_object*)(l_Lean_Server_instToJsonGoToKind_toJson___closed__0));
v___x_116_ = lean_string_dec_eq(v_val_112_, v___x_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = ((lean_object*)(l_Lean_Server_instToJsonGoToKind_toJson___closed__2));
v___x_118_ = lean_string_dec_eq(v_val_112_, v___x_117_);
lean_dec(v_val_112_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; 
v___x_119_ = ((lean_object*)(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__3));
return v___x_119_;
}
else
{
lean_object* v___x_120_; 
v___x_120_ = ((lean_object*)(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__4));
return v___x_120_;
}
}
else
{
lean_object* v___x_121_; 
lean_dec(v_val_112_);
v___x_121_ = ((lean_object*)(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__5));
return v___x_121_;
}
}
else
{
lean_object* v___x_122_; 
lean_dec(v_val_112_);
v___x_122_ = ((lean_object*)(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__6));
return v___x_122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(lean_object* v_e_125_, lean_object* v___y_126_){
_start:
{
uint8_t v___x_128_; 
v___x_128_ = l_Lean_Expr_hasMVar(v_e_125_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
v___x_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_129_, 0, v_e_125_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; lean_object* v_mctx_131_; lean_object* v___x_132_; lean_object* v_fst_133_; lean_object* v_snd_134_; lean_object* v___x_135_; lean_object* v_cache_136_; lean_object* v_zetaDeltaFVarIds_137_; lean_object* v_postponed_138_; lean_object* v_diag_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_148_; 
v___x_130_ = lean_st_ref_get(v___y_126_);
v_mctx_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc_ref(v_mctx_131_);
lean_dec(v___x_130_);
v___x_132_ = l_Lean_instantiateMVarsCore(v_mctx_131_, v_e_125_);
v_fst_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_fst_133_);
v_snd_134_ = lean_ctor_get(v___x_132_, 1);
lean_inc(v_snd_134_);
lean_dec_ref(v___x_132_);
v___x_135_ = lean_st_ref_take(v___y_126_);
v_cache_136_ = lean_ctor_get(v___x_135_, 1);
v_zetaDeltaFVarIds_137_ = lean_ctor_get(v___x_135_, 2);
v_postponed_138_ = lean_ctor_get(v___x_135_, 3);
v_diag_139_ = lean_ctor_get(v___x_135_, 4);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_148_ == 0)
{
lean_object* v_unused_149_; 
v_unused_149_ = lean_ctor_get(v___x_135_, 0);
lean_dec(v_unused_149_);
v___x_141_ = v___x_135_;
v_isShared_142_ = v_isSharedCheck_148_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_diag_139_);
lean_inc(v_postponed_138_);
lean_inc(v_zetaDeltaFVarIds_137_);
lean_inc(v_cache_136_);
lean_dec(v___x_135_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_148_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v_snd_134_);
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_snd_134_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_cache_136_);
lean_ctor_set(v_reuseFailAlloc_147_, 2, v_zetaDeltaFVarIds_137_);
lean_ctor_set(v_reuseFailAlloc_147_, 3, v_postponed_138_);
lean_ctor_set(v_reuseFailAlloc_147_, 4, v_diag_139_);
v___x_144_ = v_reuseFailAlloc_147_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_st_ref_put(v___y_126_, v___x_144_);
v___x_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_146_, 0, v_fst_133_);
return v___x_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg___boxed(lean_object* v_e_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_e_150_, v___y_151_);
lean_dec(v___y_151_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0(lean_object* v_e_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_e_154_, v___y_156_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___boxed(lean_object* v_e_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0(v_e_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_determineTargetExprs___lam__0(lean_object* v_e_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_snd_176_; 
switch(lean_obj_tag(v_e_168_))
{
case 1:
{
lean_object* v___x_181_; 
v___x_181_ = lean_array_push(v___y_169_, v_e_168_);
v_snd_176_ = v___x_181_;
goto v___jp_175_;
}
case 4:
{
lean_object* v___x_182_; 
v___x_182_ = lean_array_push(v___y_169_, v_e_168_);
v_snd_176_ = v___x_182_;
goto v___jp_175_;
}
default: 
{
lean_dec_ref(v_e_168_);
v_snd_176_ = v___y_169_;
goto v___jp_175_;
}
}
v___jp_175_:
{
uint8_t v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_177_ = 1;
v___x_178_ = lean_box(v___x_177_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v_snd_176_);
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_determineTargetExprs___lam__0___boxed(lean_object* v_e_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Server_GoToKind_determineTargetExprs___lam__0(v_e_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(lean_object* v_a_191_, lean_object* v_b_192_, lean_object* v_x_193_){
_start:
{
if (lean_obj_tag(v_x_193_) == 0)
{
lean_dec(v_b_192_);
lean_dec_ref(v_a_191_);
return v_x_193_;
}
else
{
lean_object* v_key_194_; lean_object* v_value_195_; lean_object* v_tail_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_208_; 
v_key_194_ = lean_ctor_get(v_x_193_, 0);
v_value_195_ = lean_ctor_get(v_x_193_, 1);
v_tail_196_ = lean_ctor_get(v_x_193_, 2);
v_isSharedCheck_208_ = !lean_is_exclusive(v_x_193_);
if (v_isSharedCheck_208_ == 0)
{
v___x_198_ = v_x_193_;
v_isShared_199_ = v_isSharedCheck_208_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_tail_196_);
lean_inc(v_value_195_);
lean_inc(v_key_194_);
lean_dec(v_x_193_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_208_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
uint8_t v___x_200_; 
v___x_200_ = lean_expr_eqv(v_key_194_, v_a_191_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_201_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(v_a_191_, v_b_192_, v_tail_196_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 2, v___x_201_);
v___x_203_ = v___x_198_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_key_194_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_value_195_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
else
{
lean_object* v___x_206_; 
lean_dec(v_value_195_);
lean_dec(v_key_194_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 1, v_b_192_);
lean_ctor_set(v___x_198_, 0, v_a_191_);
v___x_206_ = v___x_198_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_191_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_b_192_);
lean_ctor_set(v_reuseFailAlloc_207_, 2, v_tail_196_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(lean_object* v_a_209_, lean_object* v_x_210_){
_start:
{
if (lean_obj_tag(v_x_210_) == 0)
{
uint8_t v___x_211_; 
v___x_211_ = 0;
return v___x_211_;
}
else
{
lean_object* v_key_212_; lean_object* v_tail_213_; uint8_t v___x_214_; 
v_key_212_ = lean_ctor_get(v_x_210_, 0);
v_tail_213_ = lean_ctor_get(v_x_210_, 2);
v___x_214_ = lean_expr_eqv(v_key_212_, v_a_209_);
if (v___x_214_ == 0)
{
v_x_210_ = v_tail_213_;
goto _start;
}
else
{
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_216_, lean_object* v_x_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(v_a_216_, v_x_217_);
lean_dec(v_x_217_);
lean_dec_ref(v_a_216_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(lean_object* v_x_220_, lean_object* v_x_221_){
_start:
{
if (lean_obj_tag(v_x_221_) == 0)
{
return v_x_220_;
}
else
{
lean_object* v_key_222_; lean_object* v_value_223_; lean_object* v_tail_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_247_; 
v_key_222_ = lean_ctor_get(v_x_221_, 0);
v_value_223_ = lean_ctor_get(v_x_221_, 1);
v_tail_224_ = lean_ctor_get(v_x_221_, 2);
v_isSharedCheck_247_ = !lean_is_exclusive(v_x_221_);
if (v_isSharedCheck_247_ == 0)
{
v___x_226_ = v_x_221_;
v_isShared_227_ = v_isSharedCheck_247_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_tail_224_);
lean_inc(v_value_223_);
lean_inc(v_key_222_);
lean_dec(v_x_221_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_247_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; uint64_t v___x_229_; uint64_t v___x_230_; uint64_t v___x_231_; uint64_t v_fold_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; size_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_228_ = lean_array_get_size(v_x_220_);
v___x_229_ = l_Lean_Expr_hash(v_key_222_);
v___x_230_ = 32ULL;
v___x_231_ = lean_uint64_shift_right(v___x_229_, v___x_230_);
v_fold_232_ = lean_uint64_xor(v___x_229_, v___x_231_);
v___x_233_ = 16ULL;
v___x_234_ = lean_uint64_shift_right(v_fold_232_, v___x_233_);
v___x_235_ = lean_uint64_xor(v_fold_232_, v___x_234_);
v___x_236_ = lean_uint64_to_usize(v___x_235_);
v___x_237_ = lean_usize_of_nat(v___x_228_);
v___x_238_ = ((size_t)1ULL);
v___x_239_ = lean_usize_sub(v___x_237_, v___x_238_);
v___x_240_ = lean_usize_land(v___x_236_, v___x_239_);
v___x_241_ = lean_array_uget_borrowed(v_x_220_, v___x_240_);
lean_inc(v___x_241_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 2, v___x_241_);
v___x_243_ = v___x_226_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_key_222_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_value_223_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v___x_241_);
v___x_243_ = v_reuseFailAlloc_246_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; 
v___x_244_ = lean_array_uset(v_x_220_, v___x_240_, v___x_243_);
v_x_220_ = v___x_244_;
v_x_221_ = v_tail_224_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6___redArg(lean_object* v_i_248_, lean_object* v_source_249_, lean_object* v_target_250_){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = lean_array_get_size(v_source_249_);
v___x_252_ = lean_nat_dec_lt(v_i_248_, v___x_251_);
if (v___x_252_ == 0)
{
lean_dec_ref(v_source_249_);
lean_dec(v_i_248_);
return v_target_250_;
}
else
{
lean_object* v_es_253_; lean_object* v___x_254_; lean_object* v_source_255_; lean_object* v_target_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_es_253_ = lean_array_fget(v_source_249_, v_i_248_);
v___x_254_ = lean_box(0);
v_source_255_ = lean_array_fset(v_source_249_, v_i_248_, v___x_254_);
v_target_256_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(v_target_250_, v_es_253_);
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_nat_add(v_i_248_, v___x_257_);
lean_dec(v_i_248_);
v_i_248_ = v___x_258_;
v_source_249_ = v_source_255_;
v_target_250_ = v_target_256_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5___redArg(lean_object* v_data_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v_nbuckets_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_261_ = lean_array_get_size(v_data_260_);
v___x_262_ = lean_unsigned_to_nat(2u);
v_nbuckets_263_ = lean_nat_mul(v___x_261_, v___x_262_);
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_box(0);
v___x_266_ = lean_mk_array(v_nbuckets_263_, v___x_265_);
v___x_267_ = lean_array_propagate_mark(v_data_260_, v___x_266_);
v___x_268_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6___redArg(v___x_264_, v_data_260_, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2___redArg(lean_object* v_m_269_, lean_object* v_a_270_, lean_object* v_b_271_){
_start:
{
lean_object* v_size_272_; lean_object* v_buckets_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_316_; 
v_size_272_ = lean_ctor_get(v_m_269_, 0);
v_buckets_273_ = lean_ctor_get(v_m_269_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v_m_269_);
if (v_isSharedCheck_316_ == 0)
{
v___x_275_ = v_m_269_;
v_isShared_276_ = v_isSharedCheck_316_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_buckets_273_);
lean_inc(v_size_272_);
lean_dec(v_m_269_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_316_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; uint64_t v___x_278_; uint64_t v___x_279_; uint64_t v___x_280_; uint64_t v_fold_281_; uint64_t v___x_282_; uint64_t v___x_283_; uint64_t v___x_284_; size_t v___x_285_; size_t v___x_286_; size_t v___x_287_; size_t v___x_288_; size_t v___x_289_; lean_object* v_bkt_290_; uint8_t v___x_291_; 
v___x_277_ = lean_array_get_size(v_buckets_273_);
v___x_278_ = l_Lean_Expr_hash(v_a_270_);
v___x_279_ = 32ULL;
v___x_280_ = lean_uint64_shift_right(v___x_278_, v___x_279_);
v_fold_281_ = lean_uint64_xor(v___x_278_, v___x_280_);
v___x_282_ = 16ULL;
v___x_283_ = lean_uint64_shift_right(v_fold_281_, v___x_282_);
v___x_284_ = lean_uint64_xor(v_fold_281_, v___x_283_);
v___x_285_ = lean_uint64_to_usize(v___x_284_);
v___x_286_ = lean_usize_of_nat(v___x_277_);
v___x_287_ = ((size_t)1ULL);
v___x_288_ = lean_usize_sub(v___x_286_, v___x_287_);
v___x_289_ = lean_usize_land(v___x_285_, v___x_288_);
v_bkt_290_ = lean_array_uget_borrowed(v_buckets_273_, v___x_289_);
v___x_291_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(v_a_270_, v_bkt_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v_size_x27_293_; lean_object* v___x_294_; lean_object* v_buckets_x27_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_292_ = lean_unsigned_to_nat(1u);
v_size_x27_293_ = lean_nat_add(v_size_272_, v___x_292_);
lean_dec(v_size_272_);
lean_inc(v_bkt_290_);
v___x_294_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_294_, 0, v_a_270_);
lean_ctor_set(v___x_294_, 1, v_b_271_);
lean_ctor_set(v___x_294_, 2, v_bkt_290_);
v_buckets_x27_295_ = lean_array_uset(v_buckets_273_, v___x_289_, v___x_294_);
v___x_296_ = lean_unsigned_to_nat(4u);
v___x_297_ = lean_nat_mul(v_size_x27_293_, v___x_296_);
v___x_298_ = lean_unsigned_to_nat(3u);
v___x_299_ = lean_nat_div(v___x_297_, v___x_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_array_get_size(v_buckets_x27_295_);
v___x_301_ = lean_nat_dec_le(v___x_299_, v___x_300_);
lean_dec(v___x_299_);
if (v___x_301_ == 0)
{
lean_object* v_val_302_; lean_object* v___x_304_; 
v_val_302_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5___redArg(v_buckets_x27_295_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v_val_302_);
lean_ctor_set(v___x_275_, 0, v_size_x27_293_);
v___x_304_ = v___x_275_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_size_x27_293_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_val_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
else
{
lean_object* v___x_307_; 
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v_buckets_x27_295_);
lean_ctor_set(v___x_275_, 0, v_size_x27_293_);
v___x_307_ = v___x_275_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_size_x27_293_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_buckets_x27_295_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
else
{
lean_object* v___x_309_; lean_object* v_buckets_x27_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; 
lean_inc(v_bkt_290_);
v___x_309_ = lean_box(0);
v_buckets_x27_310_ = lean_array_uset(v_buckets_273_, v___x_289_, v___x_309_);
v___x_311_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(v_a_270_, v_b_271_, v_bkt_290_);
v___x_312_ = lean_array_uset(v_buckets_x27_310_, v___x_289_, v___x_311_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v___x_312_);
v___x_314_ = v___x_275_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_size_272_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(lean_object* v_a_317_, lean_object* v_x_318_){
_start:
{
if (lean_obj_tag(v_x_318_) == 0)
{
lean_object* v___x_319_; 
v___x_319_ = lean_box(0);
return v___x_319_;
}
else
{
lean_object* v_key_320_; lean_object* v_value_321_; lean_object* v_tail_322_; uint8_t v___x_323_; 
v_key_320_ = lean_ctor_get(v_x_318_, 0);
v_value_321_ = lean_ctor_get(v_x_318_, 1);
v_tail_322_ = lean_ctor_get(v_x_318_, 2);
v___x_323_ = lean_expr_eqv(v_key_320_, v_a_317_);
if (v___x_323_ == 0)
{
v_x_318_ = v_tail_322_;
goto _start;
}
else
{
lean_object* v___x_325_; 
lean_inc(v_value_321_);
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v_value_321_);
return v___x_325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_a_326_, lean_object* v_x_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(v_a_326_, v_x_327_);
lean_dec(v_x_327_);
lean_dec_ref(v_a_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(lean_object* v_m_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_buckets_331_; lean_object* v___x_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v_fold_336_; uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_buckets_331_ = lean_ctor_get(v_m_329_, 1);
v___x_332_ = lean_array_get_size(v_buckets_331_);
v___x_333_ = l_Lean_Expr_hash(v_a_330_);
v___x_334_ = 32ULL;
v___x_335_ = lean_uint64_shift_right(v___x_333_, v___x_334_);
v_fold_336_ = lean_uint64_xor(v___x_333_, v___x_335_);
v___x_337_ = 16ULL;
v___x_338_ = lean_uint64_shift_right(v_fold_336_, v___x_337_);
v___x_339_ = lean_uint64_xor(v_fold_336_, v___x_338_);
v___x_340_ = lean_uint64_to_usize(v___x_339_);
v___x_341_ = lean_usize_of_nat(v___x_332_);
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_sub(v___x_341_, v___x_342_);
v___x_344_ = lean_usize_land(v___x_340_, v___x_343_);
v___x_345_ = lean_array_uget_borrowed(v_buckets_331_, v___x_344_);
v___x_346_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(v_a_330_, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg___boxed(lean_object* v_m_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(v_m_347_, v_a_348_);
lean_dec_ref(v_a_348_);
lean_dec_ref(v_m_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(lean_object* v_g_350_, lean_object* v_e_351_, lean_object* v_a_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_a_360_; lean_object* v_fst_361_; lean_object* v___y_367_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_st_ref_get(v_a_352_);
v___x_371_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(v___x_370_, v_e_351_);
lean_dec(v___x_370_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v___x_372_; 
lean_inc_ref(v_g_350_);
lean_inc(v___y_357_);
lean_inc_ref(v___y_356_);
lean_inc(v___y_355_);
lean_inc_ref(v___y_354_);
lean_inc_ref(v_e_351_);
v___x_372_ = lean_apply_7(v_g_350_, v_e_351_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, lean_box(0));
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v_fst_374_; lean_object* v_snd_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_420_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_373_);
lean_dec_ref_known(v___x_372_, 1);
v_fst_374_ = lean_ctor_get(v_a_373_, 0);
v_snd_375_ = lean_ctor_get(v_a_373_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v_a_373_);
if (v_isSharedCheck_420_ == 0)
{
v___x_377_ = v_a_373_;
v_isShared_378_ = v_isSharedCheck_420_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_snd_375_);
lean_inc(v_fst_374_);
lean_dec(v_a_373_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_420_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v_d_380_; lean_object* v_b_381_; lean_object* v___y_382_; uint8_t v___x_387_; 
v___x_387_ = lean_unbox(v_fst_374_);
lean_dec(v_fst_374_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_390_; 
lean_dec_ref(v_g_350_);
v___x_388_ = lean_box(0);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_388_);
v___x_390_ = v___x_377_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_snd_375_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
v_a_360_ = v___x_390_;
v_fst_361_ = v___x_388_;
goto v___jp_359_;
}
}
else
{
switch(lean_obj_tag(v_e_351_))
{
case 7:
{
lean_object* v_binderType_392_; lean_object* v_body_393_; 
lean_del_object(v___x_377_);
v_binderType_392_ = lean_ctor_get(v_e_351_, 1);
v_body_393_ = lean_ctor_get(v_e_351_, 2);
lean_inc_ref(v_body_393_);
lean_inc_ref(v_binderType_392_);
v_d_380_ = v_binderType_392_;
v_b_381_ = v_body_393_;
v___y_382_ = v_a_352_;
goto v___jp_379_;
}
case 6:
{
lean_object* v_binderType_394_; lean_object* v_body_395_; 
lean_del_object(v___x_377_);
v_binderType_394_ = lean_ctor_get(v_e_351_, 1);
v_body_395_ = lean_ctor_get(v_e_351_, 2);
lean_inc_ref(v_body_395_);
lean_inc_ref(v_binderType_394_);
v_d_380_ = v_binderType_394_;
v_b_381_ = v_body_395_;
v___y_382_ = v_a_352_;
goto v___jp_379_;
}
case 8:
{
lean_object* v_type_396_; lean_object* v_value_397_; lean_object* v_body_398_; lean_object* v___x_399_; 
lean_del_object(v___x_377_);
v_type_396_ = lean_ctor_get(v_e_351_, 1);
v_value_397_ = lean_ctor_get(v_e_351_, 2);
v_body_398_ = lean_ctor_get(v_e_351_, 3);
lean_inc_ref(v_type_396_);
lean_inc_ref(v_g_350_);
v___x_399_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_350_, v_type_396_, v_a_352_, v_snd_375_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v_snd_401_; lean_object* v___x_402_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref_known(v___x_399_, 1);
v_snd_401_ = lean_ctor_get(v_a_400_, 1);
lean_inc(v_snd_401_);
lean_dec(v_a_400_);
lean_inc_ref(v_value_397_);
lean_inc_ref(v_g_350_);
v___x_402_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_350_, v_value_397_, v_a_352_, v_snd_401_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v_snd_404_; lean_object* v___x_405_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v___x_402_, 1);
v_snd_404_ = lean_ctor_get(v_a_403_, 1);
lean_inc(v_snd_404_);
lean_dec(v_a_403_);
lean_inc_ref(v_body_398_);
v___x_405_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_350_, v_body_398_, v_a_352_, v_snd_404_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
v___y_367_ = v___x_405_;
goto v___jp_366_;
}
else
{
lean_dec_ref(v_g_350_);
v___y_367_ = v___x_402_;
goto v___jp_366_;
}
}
else
{
lean_dec_ref(v_g_350_);
v___y_367_ = v___x_399_;
goto v___jp_366_;
}
}
case 5:
{
lean_object* v_fn_406_; lean_object* v_arg_407_; lean_object* v___x_408_; 
lean_del_object(v___x_377_);
v_fn_406_ = lean_ctor_get(v_e_351_, 0);
v_arg_407_ = lean_ctor_get(v_e_351_, 1);
lean_inc_ref(v_fn_406_);
lean_inc_ref(v_g_350_);
v___x_408_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_350_, v_fn_406_, v_a_352_, v_snd_375_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v_snd_410_; lean_object* v___x_411_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_408_, 1);
v_snd_410_ = lean_ctor_get(v_a_409_, 1);
lean_inc(v_snd_410_);
lean_dec(v_a_409_);
lean_inc_ref(v_arg_407_);
v___x_411_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_350_, v_arg_407_, v_a_352_, v_snd_410_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
v___y_367_ = v___x_411_;
goto v___jp_366_;
}
else
{
lean_dec_ref(v_g_350_);
v___y_367_ = v___x_408_;
goto v___jp_366_;
}
}
case 10:
{
lean_object* v_expr_412_; lean_object* v___x_413_; 
lean_del_object(v___x_377_);
v_expr_412_ = lean_ctor_get(v_e_351_, 1);
lean_inc_ref(v_expr_412_);
v___x_413_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_350_, v_expr_412_, v_a_352_, v_snd_375_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
v___y_367_ = v___x_413_;
goto v___jp_366_;
}
case 11:
{
lean_object* v_struct_414_; lean_object* v___x_415_; 
lean_del_object(v___x_377_);
v_struct_414_ = lean_ctor_get(v_e_351_, 2);
lean_inc_ref(v_struct_414_);
v___x_415_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_350_, v_struct_414_, v_a_352_, v_snd_375_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
v___y_367_ = v___x_415_;
goto v___jp_366_;
}
default: 
{
lean_object* v___x_416_; lean_object* v___x_418_; 
lean_dec_ref(v_g_350_);
v___x_416_ = lean_box(0);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_416_);
v___x_418_ = v___x_377_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_snd_375_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
v_a_360_ = v___x_418_;
v_fst_361_ = v___x_416_;
goto v___jp_359_;
}
}
}
}
v___jp_379_:
{
lean_object* v___x_383_; 
lean_inc_ref(v_g_350_);
v___x_383_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_350_, v_d_380_, v___y_382_, v_snd_375_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v_snd_385_; lean_object* v___x_386_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref_known(v___x_383_, 1);
v_snd_385_ = lean_ctor_get(v_a_384_, 1);
lean_inc(v_snd_385_);
lean_dec(v_a_384_);
v___x_386_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_350_, v_b_381_, v___y_382_, v_snd_385_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
v___y_367_ = v___x_386_;
goto v___jp_366_;
}
else
{
lean_dec_ref(v_b_381_);
lean_dec_ref(v_g_350_);
v___y_367_ = v___x_383_;
goto v___jp_366_;
}
}
}
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
lean_dec_ref(v_e_351_);
lean_dec_ref(v_g_350_);
v_a_421_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_372_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_372_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
else
{
lean_object* v_val_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_437_; 
lean_dec_ref(v_e_351_);
lean_dec_ref(v_g_350_);
v_val_429_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_437_ == 0)
{
v___x_431_ = v___x_371_;
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_val_429_);
lean_dec(v___x_371_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v_val_429_);
lean_ctor_set(v___x_433_, 1, v___y_353_);
if (v_isShared_432_ == 0)
{
lean_ctor_set_tag(v___x_431_, 0);
lean_ctor_set(v___x_431_, 0, v___x_433_);
v___x_435_ = v___x_431_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
v___jp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_362_ = lean_st_ref_take(v_a_352_);
v___x_363_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2___redArg(v___x_362_, v_e_351_, v_fst_361_);
v___x_364_ = lean_st_ref_put(v_a_352_, v___x_363_);
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v_a_360_);
return v___x_365_;
}
v___jp_366_:
{
if (lean_obj_tag(v___y_367_) == 0)
{
lean_object* v_a_368_; lean_object* v_fst_369_; 
v_a_368_ = lean_ctor_get(v___y_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v___y_367_, 1);
v_fst_369_ = lean_ctor_get(v_a_368_, 0);
lean_inc(v_fst_369_);
v_a_360_ = v_a_368_;
v_fst_361_ = v_fst_369_;
goto v___jp_359_;
}
else
{
lean_dec_ref(v_e_351_);
return v___y_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1___boxed(lean_object* v_g_438_, lean_object* v_e_439_, lean_object* v_a_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_438_, v_e_439_, v_a_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v_a_440_);
return v_res_447_;
}
}
static lean_object* _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__1(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_449_ = lean_box(0);
v___x_450_ = lean_unsigned_to_nat(16u);
v___x_451_ = lean_mk_array(v___x_450_, v___x_449_);
return v___x_451_;
}
}
static lean_object* _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__2(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_obj_once(&l_Lean_Server_GoToKind_determineTargetExprs___closed__1, &l_Lean_Server_GoToKind_determineTargetExprs___closed__1_once, _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__1);
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v___x_452_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_determineTargetExprs(uint8_t v_kind_457_, lean_object* v_ti_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
if (v_kind_457_ == 2)
{
lean_object* v_expr_464_; lean_object* v___f_465_; lean_object* v___x_466_; 
v_expr_464_ = lean_ctor_get(v_ti_458_, 3);
lean_inc_ref(v_expr_464_);
lean_dec_ref(v_ti_458_);
v___f_465_ = ((lean_object*)(l_Lean_Server_GoToKind_determineTargetExprs___closed__0));
lean_inc(v_a_462_);
lean_inc_ref(v_a_461_);
lean_inc(v_a_460_);
lean_inc_ref(v_a_459_);
v___x_466_ = lean_infer_type(v_expr_464_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_468_; lean_object* v_a_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
lean_dec_ref_known(v___x_466_, 1);
v___x_468_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_a_467_, v_a_460_);
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref(v___x_468_);
v___x_470_ = lean_obj_once(&l_Lean_Server_GoToKind_determineTargetExprs___closed__2, &l_Lean_Server_GoToKind_determineTargetExprs___closed__2_once, _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__2);
v___x_471_ = ((lean_object*)(l_Lean_Server_GoToKind_determineTargetExprs___closed__3));
v___x_472_ = lean_st_mk_ref(v___x_470_);
v___x_473_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v___f_465_, v_a_469_, v___x_472_, v___x_471_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_483_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_483_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_483_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_483_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v_snd_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v_snd_478_ = lean_ctor_get(v_a_474_, 1);
lean_inc(v_snd_478_);
lean_dec(v_a_474_);
v___x_479_ = lean_st_ref_get(v___x_472_);
lean_dec(v___x_472_);
lean_dec(v___x_479_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v_snd_478_);
v___x_481_ = v___x_476_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_snd_478_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec(v___x_472_);
v_a_484_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_473_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_473_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
v_a_492_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_466_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_466_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
else
{
lean_object* v_expr_500_; lean_object* v___x_501_; lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_512_; 
v_expr_500_ = lean_ctor_get(v_ti_458_, 3);
lean_inc_ref(v_expr_500_);
lean_dec_ref(v_ti_458_);
v___x_501_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_expr_500_, v_a_460_);
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_512_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_512_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_512_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_mk_empty_array_with_capacity(v___x_506_);
v___x_508_ = lean_array_push(v___x_507_, v_a_502_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_508_);
v___x_510_ = v___x_504_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_determineTargetExprs___boxed(lean_object* v_kind_513_, lean_object* v_ti_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
uint8_t v_kind_boxed_520_; lean_object* v_res_521_; 
v_kind_boxed_520_ = lean_unbox(v_kind_513_);
v_res_521_ = l_Lean_Server_GoToKind_determineTargetExprs(v_kind_boxed_520_, v_ti_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1(lean_object* v_00_u03b2_522_, lean_object* v_m_523_, lean_object* v_a_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(v_m_523_, v_a_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___boxed(lean_object* v_00_u03b2_526_, lean_object* v_m_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1(v_00_u03b2_526_, v_m_527_, v_a_528_);
lean_dec_ref(v_a_528_);
lean_dec_ref(v_m_527_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2(lean_object* v_00_u03b2_530_, lean_object* v_m_531_, lean_object* v_a_532_, lean_object* v_b_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2___redArg(v_m_531_, v_a_532_, v_b_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_535_, lean_object* v_a_536_, lean_object* v_x_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(v_a_536_, v_x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_539_, lean_object* v_a_540_, lean_object* v_x_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2(v_00_u03b2_539_, v_a_540_, v_x_541_);
lean_dec(v_x_541_);
lean_dec_ref(v_a_540_);
return v_res_542_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_543_, lean_object* v_a_544_, lean_object* v_x_545_){
_start:
{
uint8_t v___x_546_; 
v___x_546_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(v_a_544_, v_x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_547_, lean_object* v_a_548_, lean_object* v_x_549_){
_start:
{
uint8_t v_res_550_; lean_object* v_r_551_; 
v_res_550_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4(v_00_u03b2_547_, v_a_548_, v_x_549_);
lean_dec(v_x_549_);
lean_dec_ref(v_a_548_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_552_, lean_object* v_data_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5___redArg(v_data_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_555_, lean_object* v_a_556_, lean_object* v_b_557_, lean_object* v_x_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(v_a_556_, v_b_557_, v_x_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_560_, lean_object* v_i_561_, lean_object* v_source_562_, lean_object* v_target_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6___redArg(v_i_561_, v_source_562_, v_target_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_565_, lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(v_x_566_, v_x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(lean_object* v_e_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_st_ref_get(v_a_573_);
v___x_576_ = l_Lean_Expr_getAppFn_x27(v_e_569_);
if (lean_obj_tag(v___x_576_) == 4)
{
lean_object* v_declName_577_; lean_object* v_env_578_; lean_object* v___x_579_; 
v_declName_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_declName_577_);
lean_dec_ref_known(v___x_576_, 2);
v_env_578_ = lean_ctor_get(v___x_575_, 0);
lean_inc_ref(v_env_578_);
lean_dec(v___x_575_);
v___x_579_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_578_, v_declName_577_);
if (lean_obj_tag(v___x_579_) == 1)
{
lean_object* v_val_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_589_; 
v_val_580_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_589_ == 0)
{
v___x_582_ = v___x_579_;
v_isShared_583_ = v_isSharedCheck_589_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_val_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_589_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v_e_569_);
lean_ctor_set(v___x_584_, 1, v_val_580_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_584_);
v___x_586_ = v___x_582_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_588_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; 
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
}
else
{
uint8_t v___x_590_; lean_object* v___x_591_; 
lean_dec(v___x_579_);
v___x_590_ = 0;
v___x_591_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_569_, v___x_590_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_602_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_602_ == 0)
{
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_602_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_602_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
if (lean_obj_tag(v_a_592_) == 1)
{
lean_object* v_val_596_; 
lean_del_object(v___x_594_);
v_val_596_ = lean_ctor_get(v_a_592_, 0);
lean_inc(v_val_596_);
lean_dec_ref_known(v_a_592_, 1);
v_e_569_ = v_val_596_;
goto _start;
}
else
{
lean_object* v___x_598_; lean_object* v___x_600_; 
lean_dec(v_a_592_);
v___x_598_ = lean_box(0);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_598_);
v___x_600_ = v___x_594_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
v_a_603_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_591_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_591_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; 
lean_dec_ref(v___x_576_);
lean_dec(v___x_575_);
lean_dec_ref(v_e_569_);
v___x_611_ = lean_box(0);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f___boxed(lean_object* v_e_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(v_e_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
return v_res_619_;
}
}
static lean_object* _init_l_Lean_Server_getInstanceProjectionArg_x3f___closed__0(void){
_start:
{
lean_object* v___x_620_; lean_object* v_dummy_621_; 
v___x_620_ = lean_box(0);
v_dummy_621_ = l_Lean_Expr_sort___override(v___x_620_);
return v_dummy_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_getInstanceProjectionArg_x3f(lean_object* v_e_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v___y_629_; lean_object* v___x_674_; uint8_t v_transparency_675_; uint8_t v___x_676_; uint8_t v___x_677_; 
v___x_674_ = l_Lean_Meta_Context_config(v_a_623_);
v_transparency_675_ = lean_ctor_get_uint8(v___x_674_, 9);
lean_dec_ref(v___x_674_);
v___x_676_ = 2;
v___x_677_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_675_, v___x_676_);
if (v___x_677_ == 0)
{
lean_object* v_keyedConfig_678_; uint8_t v_trackZetaDelta_679_; lean_object* v_zetaDeltaSet_680_; lean_object* v_lctx_681_; lean_object* v_localInstances_682_; lean_object* v_defEqCtx_x3f_683_; lean_object* v_synthPendingDepth_684_; lean_object* v_customCanUnfoldPredicate_x3f_685_; uint8_t v_univApprox_686_; uint8_t v_inTypeClassResolution_687_; uint8_t v_cacheInferType_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_keyedConfig_678_ = lean_ctor_get(v_a_623_, 0);
v_trackZetaDelta_679_ = lean_ctor_get_uint8(v_a_623_, sizeof(void*)*7);
v_zetaDeltaSet_680_ = lean_ctor_get(v_a_623_, 1);
v_lctx_681_ = lean_ctor_get(v_a_623_, 2);
v_localInstances_682_ = lean_ctor_get(v_a_623_, 3);
v_defEqCtx_x3f_683_ = lean_ctor_get(v_a_623_, 4);
v_synthPendingDepth_684_ = lean_ctor_get(v_a_623_, 5);
v_customCanUnfoldPredicate_x3f_685_ = lean_ctor_get(v_a_623_, 6);
v_univApprox_686_ = lean_ctor_get_uint8(v_a_623_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_687_ = lean_ctor_get_uint8(v_a_623_, sizeof(void*)*7 + 2);
v_cacheInferType_688_ = lean_ctor_get_uint8(v_a_623_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_678_);
v___x_689_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_676_, v_keyedConfig_678_);
lean_inc(v_customCanUnfoldPredicate_x3f_685_);
lean_inc(v_synthPendingDepth_684_);
lean_inc(v_defEqCtx_x3f_683_);
lean_inc_ref(v_localInstances_682_);
lean_inc_ref(v_lctx_681_);
lean_inc(v_zetaDeltaSet_680_);
v___x_690_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v_zetaDeltaSet_680_);
lean_ctor_set(v___x_690_, 2, v_lctx_681_);
lean_ctor_set(v___x_690_, 3, v_localInstances_682_);
lean_ctor_set(v___x_690_, 4, v_defEqCtx_x3f_683_);
lean_ctor_set(v___x_690_, 5, v_synthPendingDepth_684_);
lean_ctor_set(v___x_690_, 6, v_customCanUnfoldPredicate_x3f_685_);
lean_ctor_set_uint8(v___x_690_, sizeof(void*)*7, v_trackZetaDelta_679_);
lean_ctor_set_uint8(v___x_690_, sizeof(void*)*7 + 1, v_univApprox_686_);
lean_ctor_set_uint8(v___x_690_, sizeof(void*)*7 + 2, v_inTypeClassResolution_687_);
lean_ctor_set_uint8(v___x_690_, sizeof(void*)*7 + 3, v_cacheInferType_688_);
v___x_691_ = l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(v_e_622_, v___x_690_, v_a_624_, v_a_625_, v_a_626_);
lean_dec_ref_known(v___x_690_, 7);
v___y_629_ = v___x_691_;
goto v___jp_628_;
}
else
{
lean_object* v___x_692_; 
v___x_692_ = l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(v_e_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
v___y_629_ = v___x_692_;
goto v___jp_628_;
}
v___jp_628_:
{
if (lean_obj_tag(v___y_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_665_; 
v_a_630_ = lean_ctor_get(v___y_629_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___y_629_);
if (v_isSharedCheck_665_ == 0)
{
v___x_632_ = v___y_629_;
v_isShared_633_ = v_isSharedCheck_665_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___y_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_665_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
if (lean_obj_tag(v_a_630_) == 1)
{
lean_object* v_val_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_660_; 
v_val_634_ = lean_ctor_get(v_a_630_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v_a_630_);
if (v_isSharedCheck_660_ == 0)
{
v___x_636_ = v_a_630_;
v_isShared_637_ = v_isSharedCheck_660_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_val_634_);
lean_dec(v_a_630_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_660_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v_snd_638_; lean_object* v_fst_639_; lean_object* v_numParams_640_; lean_object* v_dummy_641_; lean_object* v_nargs_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v_snd_638_ = lean_ctor_get(v_val_634_, 1);
lean_inc(v_snd_638_);
v_fst_639_ = lean_ctor_get(v_val_634_, 0);
lean_inc(v_fst_639_);
lean_dec(v_val_634_);
v_numParams_640_ = lean_ctor_get(v_snd_638_, 1);
lean_inc(v_numParams_640_);
lean_dec(v_snd_638_);
v_dummy_641_ = lean_obj_once(&l_Lean_Server_getInstanceProjectionArg_x3f___closed__0, &l_Lean_Server_getInstanceProjectionArg_x3f___closed__0_once, _init_l_Lean_Server_getInstanceProjectionArg_x3f___closed__0);
v_nargs_642_ = l_Lean_Expr_getAppNumArgs(v_fst_639_);
lean_inc(v_nargs_642_);
v___x_643_ = lean_mk_array(v_nargs_642_, v_dummy_641_);
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_nat_sub(v_nargs_642_, v___x_644_);
lean_dec(v_nargs_642_);
v___x_646_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_639_, v___x_643_, v___x_645_);
v___x_647_ = lean_array_get_size(v___x_646_);
v___x_648_ = lean_nat_dec_lt(v_numParams_640_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_651_; 
lean_dec_ref(v___x_646_);
lean_dec(v_numParams_640_);
lean_del_object(v___x_636_);
v___x_649_ = lean_box(0);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_649_);
v___x_651_ = v___x_632_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
else
{
lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_653_ = lean_array_fget(v___x_646_, v_numParams_640_);
lean_dec(v_numParams_640_);
lean_dec_ref(v___x_646_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_653_);
v___x_655_ = v___x_636_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_653_);
v___x_655_ = v_reuseFailAlloc_659_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_657_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_655_);
v___x_657_ = v___x_632_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
else
{
lean_object* v___x_661_; lean_object* v___x_663_; 
lean_dec(v_a_630_);
v___x_661_ = lean_box(0);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_661_);
v___x_663_ = v___x_632_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
v_a_666_ = lean_ctor_get(v___y_629_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___y_629_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___y_629_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___y_629_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_getInstanceProjectionArg_x3f___boxed(lean_object* v_e_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_Server_getInstanceProjectionArg_x3f(v_e_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isInstanceProjection(lean_object* v_e_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Lean_Server_getInstanceProjectionArg_x3f(v_e_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_721_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_721_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_721_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_721_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
if (lean_obj_tag(v_a_707_) == 0)
{
uint8_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_711_ = 0;
v___x_712_ = lean_box(v___x_711_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_712_);
v___x_714_ = v___x_709_;
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
else
{
uint8_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_719_; 
lean_dec_ref_known(v_a_707_, 1);
v___x_716_ = 1;
v___x_717_ = lean_box(v___x_716_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_717_);
v___x_719_ = v___x_709_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
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
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
v_a_722_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_706_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_706_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isInstanceProjection___boxed(lean_object* v_e_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Server_isInstanceProjection(v_e_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isInstanceProjectionInfoFor(uint8_t v_kind_737_, lean_object* v_ti1_738_, lean_object* v_ti2_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
uint8_t v___x_745_; uint8_t v___x_746_; 
v___x_745_ = 2;
v___x_746_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_737_, v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v_toElabInfo_747_; lean_object* v_expr_748_; lean_object* v_stx_749_; uint8_t v___x_750_; lean_object* v___x_751_; 
v_toElabInfo_747_ = lean_ctor_get(v_ti1_738_, 0);
lean_inc_ref(v_toElabInfo_747_);
v_expr_748_ = lean_ctor_get(v_ti1_738_, 3);
lean_inc_ref(v_expr_748_);
lean_dec_ref(v_ti1_738_);
v_stx_749_ = lean_ctor_get(v_toElabInfo_747_, 1);
lean_inc(v_stx_749_);
lean_dec_ref(v_toElabInfo_747_);
v___x_750_ = 1;
v___x_751_ = l_Lean_Syntax_getPos_x3f(v_stx_749_, v___x_750_);
lean_dec(v_stx_749_);
if (lean_obj_tag(v___x_751_) == 1)
{
lean_object* v_toElabInfo_752_; lean_object* v_val_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_821_; 
v_toElabInfo_752_ = lean_ctor_get(v_ti2_739_, 0);
lean_inc_ref(v_toElabInfo_752_);
v_val_753_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_821_ == 0)
{
v___x_755_ = v___x_751_;
v_isShared_756_ = v_isSharedCheck_821_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_val_753_);
lean_dec(v___x_751_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_821_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v_expr_757_; lean_object* v_stx_758_; lean_object* v___x_759_; 
v_expr_757_ = lean_ctor_get(v_ti2_739_, 3);
lean_inc_ref(v_expr_757_);
lean_dec_ref(v_ti2_739_);
v_stx_758_ = lean_ctor_get(v_toElabInfo_752_, 1);
lean_inc(v_stx_758_);
lean_dec_ref(v_toElabInfo_752_);
v___x_759_ = l_Lean_Syntax_getPos_x3f(v_stx_758_, v___x_750_);
lean_dec(v_stx_758_);
if (lean_obj_tag(v___x_759_) == 1)
{
lean_object* v_val_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_816_; 
lean_del_object(v___x_755_);
v_val_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_816_ == 0)
{
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_816_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_val_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_816_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
uint8_t v_decide_764_; 
v_decide_764_ = lean_nat_dec_eq(v_val_753_, v_val_760_);
lean_dec(v_val_760_);
lean_dec(v_val_753_);
if (v_decide_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_767_; 
lean_dec_ref(v_expr_757_);
lean_dec_ref(v_expr_748_);
v___x_765_ = lean_box(v___x_746_);
if (v_isShared_763_ == 0)
{
lean_ctor_set_tag(v___x_762_, 0);
lean_ctor_set(v___x_762_, 0, v___x_765_);
v___x_767_ = v___x_762_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
else
{
if (v___x_746_ == 0)
{
lean_object* v___x_769_; lean_object* v_a_770_; lean_object* v___x_771_; lean_object* v_a_772_; lean_object* v___x_773_; 
lean_del_object(v___x_762_);
v___x_769_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_expr_748_, v_a_741_);
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc_n(v_a_770_, 2);
lean_dec_ref(v___x_769_);
v___x_771_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_expr_757_, v_a_741_);
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref(v___x_771_);
v___x_773_ = l_Lean_Server_isInstanceProjection(v_a_770_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_775_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_773_, 1);
lean_inc(v_a_772_);
v___x_775_ = l_Lean_Server_isInstanceProjection(v_a_772_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
if (lean_obj_tag(v___x_775_) == 0)
{
uint8_t v___x_776_; 
v___x_776_ = lean_unbox(v_a_774_);
lean_dec(v_a_774_);
if (v___x_776_ == 0)
{
lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_784_; 
lean_dec(v_a_772_);
lean_dec(v_a_770_);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; 
v_unused_785_ = lean_ctor_get(v___x_775_, 0);
lean_dec(v_unused_785_);
v___x_778_ = v___x_775_;
v_isShared_779_ = v_isSharedCheck_784_;
goto v_resetjp_777_;
}
else
{
lean_dec(v___x_775_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_784_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_780_ = lean_box(v___x_746_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_780_);
v___x_782_ = v___x_778_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
else
{
if (v___x_746_ == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_802_; 
v_a_786_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_802_ == 0)
{
v___x_788_ = v___x_775_;
v_isShared_789_ = v_isSharedCheck_802_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_775_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_802_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
uint8_t v___x_790_; 
v___x_790_ = lean_unbox(v_a_786_);
lean_dec(v_a_786_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_791_ = l_Lean_Expr_getAppFn_x27(v_a_770_);
lean_dec(v_a_770_);
v___x_792_ = l_Lean_Expr_getAppFn_x27(v_a_772_);
lean_dec(v_a_772_);
v___x_793_ = lean_expr_eqv(v___x_791_, v___x_792_);
lean_dec_ref(v___x_792_);
lean_dec_ref(v___x_791_);
v___x_794_ = lean_box(v___x_793_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_794_);
v___x_796_ = v___x_788_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
else
{
lean_object* v___x_798_; lean_object* v___x_800_; 
lean_dec(v_a_772_);
lean_dec(v_a_770_);
v___x_798_ = lean_box(v___x_746_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_798_);
v___x_800_ = v___x_788_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
else
{
lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_810_; 
lean_dec(v_a_772_);
lean_dec(v_a_770_);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v___x_775_, 0);
lean_dec(v_unused_811_);
v___x_804_ = v___x_775_;
v_isShared_805_ = v_isSharedCheck_810_;
goto v_resetjp_803_;
}
else
{
lean_dec(v___x_775_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_810_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_806_ = lean_box(v___x_746_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_806_);
v___x_808_ = v___x_804_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
else
{
lean_dec(v_a_774_);
lean_dec(v_a_772_);
lean_dec(v_a_770_);
return v___x_775_;
}
}
else
{
lean_dec(v_a_772_);
lean_dec(v_a_770_);
return v___x_773_;
}
}
else
{
lean_object* v___x_812_; lean_object* v___x_814_; 
lean_dec_ref(v_expr_757_);
lean_dec_ref(v_expr_748_);
v___x_812_ = lean_box(v___x_746_);
if (v_isShared_763_ == 0)
{
lean_ctor_set_tag(v___x_762_, 0);
lean_ctor_set(v___x_762_, 0, v___x_812_);
v___x_814_ = v___x_762_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
else
{
lean_object* v___x_817_; lean_object* v___x_819_; 
lean_dec(v___x_759_);
lean_dec_ref(v_expr_757_);
lean_dec(v_val_753_);
lean_dec_ref(v_expr_748_);
v___x_817_ = lean_box(v___x_746_);
if (v_isShared_756_ == 0)
{
lean_ctor_set_tag(v___x_755_, 0);
lean_ctor_set(v___x_755_, 0, v___x_817_);
v___x_819_ = v___x_755_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; 
lean_dec(v___x_751_);
lean_dec_ref(v_expr_748_);
lean_dec_ref(v_ti2_739_);
v___x_822_ = lean_box(v___x_746_);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
}
else
{
uint8_t v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec_ref(v_ti2_739_);
lean_dec_ref(v_ti1_738_);
v___x_824_ = 0;
v___x_825_ = lean_box(v___x_824_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isInstanceProjectionInfoFor___boxed(lean_object* v_kind_827_, lean_object* v_ti1_828_, lean_object* v_ti2_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
uint8_t v_kind_boxed_835_; lean_object* v_res_836_; 
v_kind_boxed_835_ = lean_unbox(v_kind_827_);
v_res_836_ = l_Lean_Server_isInstanceProjectionInfoFor(v_kind_boxed_835_, v_ti1_828_, v_ti2_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToM_run___redArg(lean_object* v_ctx_837_, lean_object* v_ci_838_, lean_object* v_lctx_839_, lean_object* v_act_840_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = lean_apply_1(v_act_840_, v_ctx_837_);
v___x_843_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ci_838_, v_lctx_839_, v___x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToM_run___redArg___boxed(lean_object* v_ctx_844_, lean_object* v_ci_845_, lean_object* v_lctx_846_, lean_object* v_act_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_Server_GoToM_run___redArg(v_ctx_844_, v_ci_845_, v_lctx_846_, v_act_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToM_run(lean_object* v_00_u03b1_850_, lean_object* v_ctx_851_, lean_object* v_ci_852_, lean_object* v_lctx_853_, lean_object* v_act_854_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_Server_GoToM_run___redArg(v_ctx_851_, v_ci_852_, v_lctx_853_, v_act_854_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToM_run___boxed(lean_object* v_00_u03b1_857_, lean_object* v_ctx_858_, lean_object* v_ci_859_, lean_object* v_lctx_860_, lean_object* v_act_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_Server_GoToM_run(v_00_u03b1_857_, v_ctx_858_, v_ci_859_, v_lctx_860_, v_act_861_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; lean_object* v_env_871_; uint8_t v___x_872_; lean_object* v_env_873_; lean_object* v___x_874_; lean_object* v_toCold_875_; lean_object* v_mctx_876_; lean_object* v_lctx_877_; lean_object* v_options_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_870_ = lean_st_ref_get(v___y_868_);
v_env_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc_ref(v_env_871_);
lean_dec(v___x_870_);
v___x_872_ = 0;
v_env_873_ = l_Lean_Environment_setRecordingDeps(v_env_871_, v___x_872_);
v___x_874_ = lean_st_ref_get(v___y_866_);
v_toCold_875_ = lean_ctor_get(v___y_867_, 0);
v_mctx_876_ = lean_ctor_get(v___x_874_, 0);
lean_inc_ref(v_mctx_876_);
lean_dec(v___x_874_);
v_lctx_877_ = lean_ctor_get(v___y_865_, 2);
v_options_878_ = lean_ctor_get(v_toCold_875_, 2);
lean_inc_ref(v_options_878_);
lean_inc_ref(v_lctx_877_);
v___x_879_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_879_, 0, v_env_873_);
lean_ctor_set(v___x_879_, 1, v_mctx_876_);
lean_ctor_set(v___x_879_, 2, v_lctx_877_);
lean_ctor_set(v___x_879_, 3, v_options_878_);
v___x_880_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v_msgData_864_);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v_ref_895_; lean_object* v___x_896_; lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_905_; 
v_ref_895_ = lean_ctor_get(v___y_892_, 2);
v___x_896_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_905_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_903_; 
lean_inc(v_ref_895_);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v_ref_895_);
lean_ctor_set(v___x_901_, 1, v_a_897_);
if (v_isShared_900_ == 0)
{
lean_ctor_set_tag(v___x_899_, 1);
lean_ctor_set(v___x_899_, 0, v___x_901_);
v___x_903_ = v___x_899_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_913_, lean_object* v_msg_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_toCold_921_; lean_object* v_currRecDepth_922_; lean_object* v_ref_923_; uint16_t v_optionFlags_924_; uint8_t v_suppressElabErrors_925_; uint8_t v_isRecordingDeps_926_; lean_object* v_ref_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_toCold_921_ = lean_ctor_get(v___y_918_, 0);
v_currRecDepth_922_ = lean_ctor_get(v___y_918_, 1);
v_ref_923_ = lean_ctor_get(v___y_918_, 2);
v_optionFlags_924_ = lean_ctor_get_uint16(v___y_918_, sizeof(void*)*3);
v_suppressElabErrors_925_ = lean_ctor_get_uint8(v___y_918_, sizeof(void*)*3 + 2);
v_isRecordingDeps_926_ = lean_ctor_get_uint8(v___y_918_, sizeof(void*)*3 + 3);
v_ref_927_ = l_Lean_replaceRef(v_ref_913_, v_ref_923_);
lean_inc(v_currRecDepth_922_);
lean_inc_ref(v_toCold_921_);
v___x_928_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_928_, 0, v_toCold_921_);
lean_ctor_set(v___x_928_, 1, v_currRecDepth_922_);
lean_ctor_set(v___x_928_, 2, v_ref_927_);
lean_ctor_set_uint16(v___x_928_, sizeof(void*)*3, v_optionFlags_924_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*3 + 2, v_suppressElabErrors_925_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*3 + 3, v_isRecordingDeps_926_);
v___x_929_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_914_, v___y_916_, v___y_917_, v___x_928_, v___y_919_);
lean_dec_ref_known(v___x_928_, 3);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_930_, lean_object* v_msg_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_930_, v_msg_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v_ref_930_);
return v_res_938_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_939_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_942_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_943_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
lean_ctor_set(v___x_945_, 2, v___x_944_);
lean_ctor_set(v___x_945_, 3, v___x_944_);
lean_ctor_set(v___x_945_, 4, v___x_943_);
lean_ctor_set(v___x_945_, 5, v___x_943_);
lean_ctor_set(v___x_945_, 6, v___x_943_);
lean_ctor_set(v___x_945_, 7, v___x_943_);
lean_ctor_set(v___x_945_, 8, v___x_943_);
lean_ctor_set(v___x_945_, 9, v___x_943_);
lean_ctor_set(v___x_945_, 10, v___x_943_);
lean_ctor_set(v___x_945_, 11, v___x_942_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_946_ = lean_unsigned_to_nat(32u);
v___x_947_ = lean_mk_empty_array_with_capacity(v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
return v___x_948_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_949_ = ((size_t)5ULL);
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = lean_unsigned_to_nat(32u);
v___x_952_ = lean_mk_empty_array_with_capacity(v___x_951_);
v___x_953_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_954_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_954_, 0, v___x_953_);
lean_ctor_set(v___x_954_, 1, v___x_952_);
lean_ctor_set(v___x_954_, 2, v___x_950_);
lean_ctor_set(v___x_954_, 3, v___x_950_);
lean_ctor_set_usize(v___x_954_, 4, v___x_949_);
return v___x_954_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_955_ = lean_box(1);
v___x_956_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_957_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_958_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v___x_956_);
lean_ctor_set(v___x_958_, 2, v___x_955_);
return v___x_958_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_961_ = l_Lean_stringToMessageData(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_964_ = l_Lean_stringToMessageData(v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_967_ = l_Lean_stringToMessageData(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_970_ = l_Lean_stringToMessageData(v___x_969_);
return v___x_970_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_973_ = l_Lean_stringToMessageData(v___x_972_);
return v___x_973_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_976_ = l_Lean_stringToMessageData(v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_979_ = l_Lean_stringToMessageData(v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_980_, lean_object* v_declHint_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v_env_986_; uint8_t v___x_987_; 
v___x_984_ = lean_box(0);
v___x_985_ = lean_st_ref_get(v___y_982_);
v_env_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc_ref(v_env_986_);
lean_dec(v___x_985_);
v___x_987_ = l_Lean_Name_isAnonymous(v_declHint_981_);
if (v___x_987_ == 0)
{
uint8_t v_isExporting_988_; 
v_isExporting_988_ = lean_ctor_get_uint8(v_env_986_, sizeof(void*)*13);
if (v_isExporting_988_ == 0)
{
lean_object* v___x_989_; 
lean_dec_ref(v_env_986_);
lean_dec(v_declHint_981_);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v_msg_980_);
return v___x_989_;
}
else
{
lean_object* v___x_990_; uint8_t v___x_991_; 
lean_inc_ref(v_env_986_);
v___x_990_ = l_Lean_Environment_setExporting(v_env_986_, v___x_987_);
lean_inc(v_declHint_981_);
lean_inc_ref(v___x_990_);
v___x_991_ = l_Lean_Environment_contains(v___x_990_, v_declHint_981_, v_isExporting_988_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
lean_dec_ref(v___x_990_);
lean_dec_ref(v_env_986_);
lean_dec(v_declHint_981_);
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v_msg_980_);
return v___x_992_;
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v_c_998_; lean_object* v___x_999_; 
v___x_993_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_994_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_995_ = l_Lean_Options_empty;
v___x_996_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_996_, 0, v___x_990_);
lean_ctor_set(v___x_996_, 1, v___x_993_);
lean_ctor_set(v___x_996_, 2, v___x_994_);
lean_ctor_set(v___x_996_, 3, v___x_995_);
lean_inc(v_declHint_981_);
v___x_997_ = l_Lean_MessageData_ofConstName(v_declHint_981_, v___x_987_);
v_c_998_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_998_, 0, v___x_996_);
lean_ctor_set(v_c_998_, 1, v___x_997_);
v___x_999_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_986_, v_declHint_981_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_dec_ref(v_env_986_);
lean_dec(v_declHint_981_);
v___x_1000_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v_c_998_);
v___x_1002_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = l_Lean_MessageData_note(v___x_1003_);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v_msg_980_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
else
{
lean_object* v_val_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1041_; 
v_val_1007_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1009_ = v___x_999_;
v_isShared_1010_ = v_isSharedCheck_1041_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_val_1007_);
lean_dec(v___x_999_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1041_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v_moduleNames_1012_; lean_object* v_mod_1013_; uint8_t v___x_1014_; 
v___x_1011_ = l_Lean_Environment_header(v_env_986_);
lean_dec_ref(v_env_986_);
v_moduleNames_1012_ = lean_ctor_get(v___x_1011_, 4);
lean_inc_ref(v_moduleNames_1012_);
lean_dec_ref(v___x_1011_);
v_mod_1013_ = lean_array_get(v___x_984_, v_moduleNames_1012_, v_val_1007_);
lean_dec(v_val_1007_);
lean_dec_ref(v_moduleNames_1012_);
v___x_1014_ = l_Lean_isPrivateName(v_declHint_981_);
lean_dec(v_declHint_981_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1015_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v_c_998_);
v___x_1017_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = l_Lean_MessageData_ofName(v_mod_1013_);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = l_Lean_MessageData_note(v___x_1022_);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v_msg_980_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set_tag(v___x_1009_, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1024_);
v___x_1026_ = v___x_1009_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1028_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v_c_998_);
v___x_1030_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = l_Lean_MessageData_ofName(v_mod_1013_);
v___x_1033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = l_Lean_MessageData_note(v___x_1035_);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v_msg_980_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set_tag(v___x_1009_, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1037_);
v___x_1039_ = v___x_1009_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
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
}
}
else
{
lean_object* v___x_1042_; 
lean_dec_ref(v_env_986_);
lean_dec(v_declHint_981_);
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v_msg_980_);
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1043_, lean_object* v_declHint_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1043_, v_declHint_1044_, v___y_1045_);
lean_dec(v___y_1045_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1048_, lean_object* v_declHint_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___x_1056_; lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1066_; 
v___x_1056_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1048_, v_declHint_1049_, v___y_1054_);
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1059_ = v___x_1056_;
v_isShared_1060_ = v_isSharedCheck_1066_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1066_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1061_ = l_Lean_unknownIdentifierMessageTag;
v___x_1062_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v_a_1057_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v___x_1062_);
v___x_1064_ = v___x_1059_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1067_, lean_object* v_declHint_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1067_, v_declHint_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec_ref(v___y_1069_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_1076_, lean_object* v_msg_1077_, lean_object* v_declHint_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v___x_1085_; lean_object* v_a_1086_; lean_object* v___x_1087_; 
v___x_1085_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1077_, v_declHint_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref(v___x_1085_);
v___x_1087_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_1076_, v_a_1086_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1088_, lean_object* v_msg_1089_, lean_object* v_declHint_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_1088_, v_msg_1089_, v_declHint_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v_ref_1088_);
return v_res_1097_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1100_ = l_Lean_stringToMessageData(v___x_1099_);
return v___x_1100_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2));
v___x_1103_ = l_Lean_stringToMessageData(v___x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1104_, lean_object* v_constName_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v___x_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1112_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1113_ = 0;
lean_inc(v_constName_1105_);
v___x_1114_ = l_Lean_MessageData_ofConstName(v_constName_1105_, v___x_1113_);
v___x_1115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1112_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___x_1116_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1115_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_1104_, v___x_1117_, v_constName_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1119_, lean_object* v_constName_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1119_, v_constName_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v_ref_1119_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_ref_1135_; lean_object* v___x_1136_; 
v_ref_1135_ = lean_ctor_get(v___y_1132_, 2);
v___x_1136_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1135_, v_constName_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(lean_object* v_constName_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; lean_object* v_env_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; 
v___x_1152_ = lean_st_ref_get(v___y_1150_);
v_env_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc_ref(v_env_1153_);
lean_dec(v___x_1152_);
v___x_1154_ = 0;
lean_inc(v_constName_1145_);
v___x_1155_ = l_Lean_Environment_find_x3f(v_env_1153_, v_constName_1145_, v___x_1154_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
return v___x_1156_;
}
else
{
lean_object* v_val_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec(v_constName_1145_);
v_val_1157_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1155_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_val_1157_);
lean_dec(v___x_1155_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set_tag(v___x_1159_, 0);
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_val_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0___boxed(lean_object* v_constName_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(v_constName_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec_ref(v___y_1166_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(lean_object* v_declName_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_box(0);
lean_inc(v_declName_1173_);
v___x_1181_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(v_declName_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1207_; 
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; 
v_unused_1208_ = lean_ctor_get(v___x_1181_, 0);
lean_dec(v_unused_1208_);
v___x_1183_ = v___x_1181_;
v_isShared_1184_ = v_isSharedCheck_1207_;
goto v_resetjp_1182_;
}
else
{
lean_dec(v___x_1181_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1207_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; lean_object* v_env_1186_; lean_object* v___x_1187_; 
v___x_1185_ = lean_st_ref_get(v___y_1178_);
v_env_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc_ref(v_env_1186_);
lean_dec(v___x_1185_);
v___x_1187_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1186_, v_declName_1173_);
lean_dec(v_declName_1173_);
lean_dec_ref(v_env_1186_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1188_ = lean_box(0);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1188_);
v___x_1190_ = v___x_1183_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
else
{
lean_object* v_val_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1206_; 
v_val_1192_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1194_ = v___x_1187_;
v_isShared_1195_ = v_isSharedCheck_1206_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_val_1192_);
lean_dec(v___x_1187_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1206_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v_env_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1196_ = lean_st_ref_get(v___y_1178_);
v_env_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc_ref(v_env_1197_);
lean_dec(v___x_1196_);
v___x_1198_ = l_Lean_Environment_allImportedModuleNames(v_env_1197_);
lean_dec_ref(v_env_1197_);
v___x_1199_ = lean_array_get(v___x_1180_, v___x_1198_, v_val_1192_);
lean_dec(v_val_1192_);
lean_dec_ref(v___x_1198_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1199_);
v___x_1201_ = v___x_1194_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1203_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1201_);
v___x_1203_ = v___x_1183_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec(v_declName_1173_);
v_a_1209_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1181_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1181_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0___boxed(lean_object* v_declName_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(v_declName_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1218_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(lean_object* v_declName_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(v_declName_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1287_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1287_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1287_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
if (lean_obj_tag(v_a_1233_) == 0)
{
lean_object* v_doc_1237_; lean_object* v_uri_1238_; lean_object* v_mod_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; 
v_doc_1237_ = lean_ctor_get(v_a_1226_, 0);
v_uri_1238_ = lean_ctor_get(v_doc_1237_, 0);
v_mod_1239_ = lean_ctor_get(v_doc_1237_, 1);
lean_inc_ref(v_uri_1238_);
lean_inc(v_mod_1239_);
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v_mod_1239_);
lean_ctor_set(v___x_1240_, 1, v_uri_1238_);
v___x_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1241_);
v___x_1243_ = v___x_1235_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
else
{
lean_object* v_val_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1286_; 
lean_del_object(v___x_1235_);
v_val_1245_ = lean_ctor_get(v_a_1233_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_a_1233_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1247_ = v_a_1233_;
v_isShared_1248_ = v_isSharedCheck_1286_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_val_1245_);
lean_dec(v_a_1233_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1286_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v_ref_1249_; lean_object* v___x_1250_; 
v_ref_1249_ = lean_ctor_get(v_a_1229_, 2);
lean_inc(v_val_1245_);
v___x_1250_ = l_Lean_Server_documentUriFromModule_x3f(v_val_1245_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1271_; 
lean_del_object(v___x_1247_);
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1271_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1271_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
if (lean_obj_tag(v_a_1251_) == 1)
{
lean_object* v_val_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1266_; 
v_val_1255_ = lean_ctor_get(v_a_1251_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_a_1251_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1257_ = v_a_1251_;
v_isShared_1258_ = v_isSharedCheck_1266_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_val_1255_);
lean_dec(v_a_1251_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1266_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1259_, 0, v_val_1245_);
lean_ctor_set(v___x_1259_, 1, v_val_1255_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1259_);
v___x_1261_ = v___x_1257_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1263_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1261_);
v___x_1263_ = v___x_1253_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
lean_dec(v_a_1251_);
lean_dec(v_val_1245_);
v___x_1267_ = lean_box(0);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1267_);
v___x_1269_ = v___x_1253_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1285_; 
lean_dec(v_val_1245_);
v_a_1272_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1274_ = v___x_1250_;
v_isShared_1275_ = v_isSharedCheck_1285_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1250_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1285_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1276_ = lean_io_error_to_string(v_a_1272_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set_tag(v___x_1247_, 3);
lean_ctor_set(v___x_1247_, 0, v___x_1276_);
v___x_1278_ = v___x_1247_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1279_ = l_Lean_MessageData_ofFormat(v___x_1278_);
lean_inc(v_ref_1249_);
v___x_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1280_, 0, v_ref_1249_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1280_);
v___x_1282_ = v___x_1274_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
v_a_1288_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1232_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1232_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f___boxed(lean_object* v_declName_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(v_declName_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec_ref(v_a_1297_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1304_, lean_object* v_constName_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1313_, lean_object* v_constName_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1(v_00_u03b1_1313_, v_constName_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec_ref(v___y_1315_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1322_, lean_object* v_ref_1323_, lean_object* v_constName_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1323_, v_constName_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1332_, lean_object* v_ref_1333_, lean_object* v_constName_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1332_, v_ref_1333_, v_constName_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v_ref_1333_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_1342_, lean_object* v_ref_1343_, lean_object* v_msg_1344_, lean_object* v_declHint_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_1343_, v_msg_1344_, v_declHint_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1353_, lean_object* v_ref_1354_, lean_object* v_msg_1355_, lean_object* v_declHint_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b1_1353_, v_ref_1354_, v_msg_1355_, v_declHint_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v_ref_1354_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1364_, lean_object* v_declHint_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1364_, v_declHint_1365_, v___y_1370_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1373_, lean_object* v_declHint_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1373_, v_declHint_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec_ref(v___y_1375_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1382_, lean_object* v_ref_1383_, lean_object* v_msg_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_1383_, v_msg_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1392_, lean_object* v_ref_1393_, lean_object* v_msg_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_1392_, v_ref_1393_, v_msg_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v_ref_1393_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1402_, lean_object* v_msg_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1403_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1411_, lean_object* v_msg_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1411_, v_msg_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(lean_object* v_declName_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; lean_object* v_env_1424_; uint8_t v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1423_ = lean_st_ref_get(v___y_1421_);
v_env_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc_ref(v_env_1424_);
lean_dec(v___x_1423_);
v___x_1425_ = l_Lean_isRecCore(v_env_1424_, v_declName_1420_);
v___x_1426_ = lean_box(v___x_1425_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_1428_, v___y_1429_);
lean_dec(v___y_1429_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(lean_object* v_declName_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v_env_1437_; lean_object* v___x_1438_; lean_object* v_env_1439_; lean_object* v___x_1440_; lean_object* v_toEnvExtension_1441_; lean_object* v_asyncMode_1442_; uint8_t v___x_1443_; lean_object* v___x_1444_; 
v___x_1435_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1436_ = lean_st_ref_get(v___y_1433_);
v_env_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc_ref(v_env_1437_);
lean_dec(v___x_1436_);
v___x_1438_ = lean_st_ref_get(v___y_1433_);
v_env_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc_ref(v_env_1439_);
lean_dec(v___x_1438_);
v___x_1440_ = l_Lean_declRangeExt;
v_toEnvExtension_1441_ = lean_ctor_get(v___x_1440_, 0);
v_asyncMode_1442_ = lean_ctor_get(v_toEnvExtension_1441_, 2);
v___x_1443_ = 0;
lean_inc(v_declName_1432_);
v___x_1444_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1435_, v___x_1440_, v_env_1437_, v_declName_1432_, v_asyncMode_1442_, v___x_1443_);
if (lean_obj_tag(v___x_1444_) == 0)
{
uint8_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1445_ = 1;
v___x_1446_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1435_, v___x_1440_, v_env_1439_, v_declName_1432_, v_asyncMode_1442_, v___x_1445_);
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
return v___x_1447_;
}
else
{
lean_object* v___x_1448_; 
lean_dec_ref(v_env_1439_);
lean_dec(v_declName_1432_);
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1444_);
return v___x_1448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_1449_, v___y_1450_);
lean_dec(v___y_1450_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(lean_object* v_declName_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_ranges_1461_; lean_object* v___x_1467_; lean_object* v_env_1468_; lean_object* v___x_1469_; lean_object* v_a_1470_; uint8_t v___y_1476_; uint8_t v___x_1480_; 
v___x_1467_ = lean_st_ref_get(v___y_1458_);
v_env_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc_ref_n(v_env_1468_, 2);
lean_dec(v___x_1467_);
lean_inc_n(v_declName_1453_, 2);
v___x_1469_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_1453_, v___y_1458_);
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref(v___x_1469_);
v___x_1480_ = l_Lean_isAuxRecursor(v_env_1468_, v_declName_1453_);
if (v___x_1480_ == 0)
{
uint8_t v___x_1481_; 
lean_inc(v_declName_1453_);
v___x_1481_ = l_Lean_isNoConfusion(v_env_1468_, v_declName_1453_);
v___y_1476_ = v___x_1481_;
goto v___jp_1475_;
}
else
{
lean_dec_ref(v_env_1468_);
v___y_1476_ = v___x_1480_;
goto v___jp_1475_;
}
v___jp_1460_:
{
if (lean_obj_tag(v_ranges_1461_) == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1462_ = l_Lean_builtinDeclRanges;
v___x_1463_ = lean_st_ref_get(v___x_1462_);
v___x_1464_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1463_, v_declName_1453_);
lean_dec(v_declName_1453_);
lean_dec(v___x_1463_);
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
return v___x_1465_;
}
else
{
lean_object* v___x_1466_; 
lean_dec(v_declName_1453_);
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v_ranges_1461_);
return v___x_1466_;
}
}
v___jp_1471_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v_a_1474_; 
v___x_1472_ = l_Lean_Name_getPrefix(v_declName_1453_);
v___x_1473_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v___x_1472_, v___y_1458_);
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref(v___x_1473_);
v_ranges_1461_ = v_a_1474_;
goto v___jp_1460_;
}
v___jp_1475_:
{
if (v___y_1476_ == 0)
{
uint8_t v___x_1477_; 
v___x_1477_ = lean_unbox(v_a_1470_);
lean_dec(v_a_1470_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; lean_object* v_a_1479_; 
lean_inc(v_declName_1453_);
v___x_1478_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_1453_, v___y_1458_);
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref(v___x_1478_);
v_ranges_1461_ = v_a_1479_;
goto v___jp_1460_;
}
else
{
goto v___jp_1471_;
}
}
else
{
lean_dec(v_a_1470_);
goto v___jp_1471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0___boxed(lean_object* v_declName_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(v_declName_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec_ref(v___y_1483_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl(lean_object* v_declName_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v___x_1499_; lean_object* v_env_1500_; uint8_t v___x_1501_; uint8_t v___x_1502_; 
v___x_1499_ = lean_st_ref_get(v_a_1497_);
v_env_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc_ref(v_env_1500_);
lean_dec(v___x_1499_);
v___x_1501_ = 1;
lean_inc(v_declName_1492_);
v___x_1502_ = l_Lean_Environment_contains(v_env_1500_, v_declName_1492_, v___x_1501_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec(v_declName_1492_);
v___x_1503_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
return v___x_1504_;
}
else
{
uint8_t v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = 0;
lean_inc(v_declName_1492_);
v___x_1506_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(v_declName_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1582_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1509_ = v___x_1506_;
v_isShared_1510_ = v_isSharedCheck_1582_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1506_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1582_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
if (lean_obj_tag(v_a_1507_) == 1)
{
lean_object* v_val_1511_; lean_object* v_fst_1512_; lean_object* v_snd_1513_; lean_object* v___x_1514_; 
lean_del_object(v___x_1509_);
v_val_1511_ = lean_ctor_get(v_a_1507_, 0);
lean_inc(v_val_1511_);
lean_dec_ref_known(v_a_1507_, 1);
v_fst_1512_ = lean_ctor_get(v_val_1511_, 0);
lean_inc(v_fst_1512_);
v_snd_1513_ = lean_ctor_get(v_val_1511_, 1);
lean_inc(v_snd_1513_);
lean_dec(v_val_1511_);
lean_inc(v_declName_1492_);
v___x_1514_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(v_declName_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1569_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1569_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1569_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
if (lean_obj_tag(v_a_1515_) == 1)
{
lean_object* v_val_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1564_; 
v_val_1519_ = lean_ctor_get(v_a_1515_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_a_1515_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1521_ = v_a_1515_;
v_isShared_1522_ = v_isSharedCheck_1564_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_val_1519_);
lean_dec(v_a_1515_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1564_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___y_1524_; lean_object* v_originInfo_x3f_1548_; 
v_originInfo_x3f_1548_ = lean_ctor_get(v_a_1493_, 2);
if (lean_obj_tag(v_originInfo_x3f_1548_) == 0)
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_box(0);
v___y_1524_ = v___x_1549_;
goto v___jp_1523_;
}
else
{
lean_object* v_doc_1550_; lean_object* v_val_1551_; lean_object* v___x_1552_; 
v_doc_1550_ = lean_ctor_get(v_a_1493_, 0);
v_val_1551_ = lean_ctor_get(v_originInfo_x3f_1548_, 0);
v___x_1552_ = l_Lean_Elab_Info_range_x3f(v_val_1551_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_box(0);
v___y_1524_ = v___x_1553_;
goto v___jp_1523_;
}
else
{
lean_object* v_val_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1563_; 
v_val_1554_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1556_ = v___x_1552_;
v_isShared_1557_ = v_isSharedCheck_1563_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_val_1554_);
lean_dec(v___x_1552_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1563_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v_text_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
v_text_1558_ = lean_ctor_get(v_doc_1550_, 3);
lean_inc_ref(v_text_1558_);
v___x_1559_ = l_Lean_Syntax_Range_toLspRange(v_text_1558_, v_val_1554_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1559_);
v___x_1561_ = v___x_1556_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
v___y_1524_ = v___x_1561_;
goto v___jp_1523_;
}
}
}
}
v___jp_1523_:
{
lean_object* v_range_1525_; lean_object* v_selectionRange_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1547_; 
v_range_1525_ = lean_ctor_get(v_val_1519_, 0);
v_selectionRange_1526_ = lean_ctor_get(v_val_1519_, 1);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_val_1519_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1528_ = v_val_1519_;
v_isShared_1529_ = v_isSharedCheck_1547_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_selectionRange_1526_);
lean_inc(v_range_1525_);
lean_dec(v_val_1519_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1547_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1530_ = l_Lean_DeclarationRange_toLspRange(v_range_1525_);
v___x_1531_ = l_Lean_DeclarationRange_toLspRange(v_selectionRange_1526_);
v___x_1532_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1532_, 0, v___y_1524_);
lean_ctor_set(v___x_1532_, 1, v_snd_1513_);
lean_ctor_set(v___x_1532_, 2, v___x_1530_);
lean_ctor_set(v___x_1532_, 3, v___x_1531_);
v___x_1533_ = l_Lean_Name_eraseMacroScopes(v_declName_1492_);
lean_dec(v_declName_1492_);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 1, v___x_1533_);
lean_ctor_set(v___x_1528_, 0, v_fst_1512_);
v___x_1535_ = v___x_1528_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_fst_1512_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1537_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v___x_1535_);
v___x_1537_ = v___x_1521_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1538_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1538_, 0, v___x_1532_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
lean_ctor_set_uint8(v___x_1538_, sizeof(void*)*2, v___x_1505_);
v___x_1539_ = lean_unsigned_to_nat(1u);
v___x_1540_ = lean_mk_empty_array_with_capacity(v___x_1539_);
v___x_1541_ = lean_array_push(v___x_1540_, v___x_1538_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1541_);
v___x_1543_ = v___x_1517_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1567_; 
lean_dec(v_a_1515_);
lean_dec(v_snd_1513_);
lean_dec(v_fst_1512_);
lean_dec(v_declName_1492_);
v___x_1565_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1565_);
v___x_1567_ = v___x_1517_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
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
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec(v_snd_1513_);
lean_dec(v_fst_1512_);
lean_dec(v_declName_1492_);
v_a_1570_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1514_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1514_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
else
{
lean_object* v___x_1578_; lean_object* v___x_1580_; 
lean_dec(v_a_1507_);
lean_dec(v_declName_1492_);
v___x_1578_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1578_);
v___x_1580_ = v___x_1509_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec(v_declName_1492_);
v_a_1583_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1506_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1506_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
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
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl___boxed(lean_object* v_declName_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_Server_locationLinksFromDecl(v_declName_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec_ref(v_a_1592_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0(lean_object* v_declName_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_1599_, v___y_1604_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___boxed(lean_object* v_declName_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0(v_declName_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec_ref(v___y_1608_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1(lean_object* v_declName_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_1615_, v___y_1620_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___boxed(lean_object* v_declName_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1(v_declName_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec_ref(v___y_1624_);
return v_res_1630_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0(lean_object* v_id_1631_, lean_object* v_x_1632_){
_start:
{
if (lean_obj_tag(v_x_1632_) == 1)
{
lean_object* v_i_1633_; lean_object* v_expr_1634_; 
v_i_1633_ = lean_ctor_get(v_x_1632_, 0);
v_expr_1634_ = lean_ctor_get(v_i_1633_, 3);
if (lean_obj_tag(v_expr_1634_) == 1)
{
uint8_t v_isBinder_1635_; 
v_isBinder_1635_ = lean_ctor_get_uint8(v_i_1633_, sizeof(void*)*4);
if (v_isBinder_1635_ == 1)
{
lean_object* v_fvarId_1636_; uint8_t v___x_1637_; 
v_fvarId_1636_ = lean_ctor_get(v_expr_1634_, 0);
v___x_1637_ = l_Lean_instBEqFVarId_beq(v_fvarId_1636_, v_id_1631_);
return v___x_1637_;
}
else
{
uint8_t v___x_1638_; 
v___x_1638_ = 0;
return v___x_1638_;
}
}
else
{
uint8_t v___x_1639_; 
v___x_1639_ = 0;
return v___x_1639_;
}
}
else
{
uint8_t v___x_1640_; 
v___x_1640_ = 0;
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0___boxed(lean_object* v_id_1641_, lean_object* v_x_1642_){
_start:
{
uint8_t v_res_1643_; lean_object* v_r_1644_; 
v_res_1643_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0(v_id_1641_, v_x_1642_);
lean_dec_ref(v_x_1642_);
lean_dec(v_id_1641_);
v_r_1644_ = lean_box(v_res_1643_);
return v_r_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(lean_object* v_id_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_infoTree_x3f_1648_; 
v_infoTree_x3f_1648_ = lean_ctor_get(v_a_1646_, 1);
if (lean_obj_tag(v_infoTree_x3f_1648_) == 1)
{
lean_object* v_val_1649_; lean_object* v___f_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v_val_1649_ = lean_ctor_get(v_infoTree_x3f_1648_, 0);
v___f_1650_ = lean_alloc_closure((void*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1650_, 0, v_id_1645_);
lean_inc(v_val_1649_);
v___x_1651_ = l_Lean_Elab_InfoTree_findInfo_x3f(v___f_1650_, v_val_1649_);
v___x_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
return v___x_1652_;
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_dec(v_id_1645_);
v___x_1653_ = lean_box(0);
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___boxed(lean_object* v_id_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(v_id_1655_, v_a_1656_);
lean_dec_ref(v_a_1656_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f(lean_object* v_id_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(v_id_1659_, v_a_1660_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___boxed(lean_object* v_id_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f(v_id_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec_ref(v_a_1668_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromBinder___redArg(lean_object* v_id_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v_doc_1678_; lean_object* v_originInfo_x3f_1679_; lean_object* v___x_1680_; lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1724_; 
v_doc_1678_ = lean_ctor_get(v_a_1676_, 0);
v_originInfo_x3f_1679_ = lean_ctor_get(v_a_1676_, 2);
v___x_1680_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(v_id_1675_, v_a_1676_);
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1724_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1724_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
if (lean_obj_tag(v_a_1681_) == 1)
{
lean_object* v_val_1685_; lean_object* v___x_1686_; 
v_val_1685_ = lean_ctor_get(v_a_1681_, 0);
lean_inc(v_val_1685_);
lean_dec_ref_known(v_a_1681_, 1);
v___x_1686_ = l_Lean_Elab_Info_range_x3f(v_val_1685_);
lean_dec(v_val_1685_);
if (lean_obj_tag(v___x_1686_) == 1)
{
lean_object* v_val_1687_; lean_object* v_uri_1688_; lean_object* v_text_1689_; lean_object* v___x_1690_; lean_object* v___y_1692_; 
v_val_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_val_1687_);
lean_dec_ref_known(v___x_1686_, 1);
v_uri_1688_ = lean_ctor_get(v_doc_1678_, 0);
v_text_1689_ = lean_ctor_get(v_doc_1678_, 3);
lean_inc_ref(v_text_1689_);
v___x_1690_ = l_Lean_Syntax_Range_toLspRange(v_text_1689_, v_val_1687_);
if (lean_obj_tag(v_originInfo_x3f_1679_) == 0)
{
lean_object* v___x_1703_; 
v___x_1703_ = lean_box(0);
v___y_1692_ = v___x_1703_;
goto v___jp_1691_;
}
else
{
lean_object* v_val_1704_; lean_object* v___x_1705_; 
v_val_1704_ = lean_ctor_get(v_originInfo_x3f_1679_, 0);
v___x_1705_ = l_Lean_Elab_Info_range_x3f(v_val_1704_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_box(0);
v___y_1692_ = v___x_1706_;
goto v___jp_1691_;
}
else
{
lean_object* v_val_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1715_; 
v_val_1707_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1709_ = v___x_1705_;
v_isShared_1710_ = v_isSharedCheck_1715_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_val_1707_);
lean_dec(v___x_1705_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1715_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; lean_object* v___x_1713_; 
lean_inc_ref(v_text_1689_);
v___x_1711_ = l_Lean_Syntax_Range_toLspRange(v_text_1689_, v_val_1707_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1711_);
v___x_1713_ = v___x_1709_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
v___y_1692_ = v___x_1713_;
goto v___jp_1691_;
}
}
}
}
v___jp_1691_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1701_; 
lean_inc_ref(v___x_1690_);
lean_inc_ref(v_uri_1688_);
v___x_1693_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1693_, 0, v___y_1692_);
lean_ctor_set(v___x_1693_, 1, v_uri_1688_);
lean_ctor_set(v___x_1693_, 2, v___x_1690_);
lean_ctor_set(v___x_1693_, 3, v___x_1690_);
v___x_1694_ = lean_box(0);
v___x_1695_ = 0;
v___x_1696_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1696_, 0, v___x_1693_);
lean_ctor_set(v___x_1696_, 1, v___x_1694_);
lean_ctor_set_uint8(v___x_1696_, sizeof(void*)*2, v___x_1695_);
v___x_1697_ = lean_unsigned_to_nat(1u);
v___x_1698_ = lean_mk_empty_array_with_capacity(v___x_1697_);
v___x_1699_ = lean_array_push(v___x_1698_, v___x_1696_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1699_);
v___x_1701_ = v___x_1683_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
lean_dec(v___x_1686_);
v___x_1716_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1716_);
v___x_1718_ = v___x_1683_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1722_; 
lean_dec(v_a_1681_);
v___x_1720_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1720_);
v___x_1722_ = v___x_1683_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromBinder___redArg___boxed(lean_object* v_id_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lean_Server_locationLinksFromBinder___redArg(v_id_1725_, v_a_1726_);
lean_dec_ref(v_a_1726_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromBinder(lean_object* v_id_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Lean_Server_locationLinksFromBinder___redArg(v_id_1729_, v_a_1730_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromBinder___boxed(lean_object* v_id_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_Server_locationLinksFromBinder(v_id_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec_ref(v_a_1738_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromImport___redArg(lean_object* v_i_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v_stx_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1889_; 
v_stx_1792_ = lean_ctor_get(v_i_1776_, 1);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_i_1776_);
if (v_isSharedCheck_1889_ == 0)
{
lean_object* v_unused_1890_; 
v_unused_1890_ = lean_ctor_get(v_i_1776_, 0);
lean_dec(v_unused_1890_);
v___x_1794_ = v_i_1776_;
v_isShared_1795_ = v_isSharedCheck_1889_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_stx_1792_);
lean_dec(v_i_1776_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1889_;
goto v_resetjp_1793_;
}
v___jp_1780_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
lean_inc_ref_n(v___y_1782_, 2);
v___x_1784_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1784_, 0, v___y_1783_);
lean_ctor_set(v___x_1784_, 1, v___y_1781_);
lean_ctor_set(v___x_1784_, 2, v___y_1782_);
lean_ctor_set(v___x_1784_, 3, v___y_1782_);
v___x_1785_ = lean_box(0);
v___x_1786_ = 0;
v___x_1787_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1787_, 0, v___x_1784_);
lean_ctor_set(v___x_1787_, 1, v___x_1785_);
lean_ctor_set_uint8(v___x_1787_, sizeof(void*)*2, v___x_1786_);
v___x_1788_ = lean_unsigned_to_nat(1u);
v___x_1789_ = lean_mk_empty_array_with_capacity(v___x_1788_);
v___x_1790_ = lean_array_push(v___x_1789_, v___x_1787_);
v___x_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
return v___x_1791_;
}
v_resetjp_1793_:
{
lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1796_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__4));
lean_inc(v_stx_1792_);
v___x_1797_ = l_Lean_Syntax_isOfKind(v_stx_1792_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_del_object(v___x_1794_);
lean_dec(v_stx_1792_);
v___x_1798_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
return v___x_1799_;
}
else
{
lean_object* v___x_1800_; lean_object* v___y_1802_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1866_; lean_object* v___x_1878_; uint8_t v___x_1879_; 
v___x_1800_ = lean_unsigned_to_nat(0u);
v___x_1878_ = l_Lean_Syntax_getArg(v_stx_1792_, v___x_1800_);
v___x_1879_ = l_Lean_Syntax_isNone(v___x_1878_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; uint8_t v___x_1881_; 
v___x_1880_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1878_);
v___x_1881_ = l_Lean_Syntax_matchesNull(v___x_1878_, v___x_1880_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_dec(v___x_1878_);
lean_del_object(v___x_1794_);
lean_dec(v_stx_1792_);
v___x_1882_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1884_ = l_Lean_Syntax_getArg(v___x_1878_, v___x_1800_);
lean_dec(v___x_1878_);
v___x_1885_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__12));
v___x_1886_ = l_Lean_Syntax_isOfKind(v___x_1884_, v___x_1885_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_del_object(v___x_1794_);
lean_dec(v_stx_1792_);
v___x_1887_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
return v___x_1888_;
}
else
{
v___y_1866_ = v_a_1778_;
goto v___jp_1865_;
}
}
}
else
{
lean_dec(v___x_1878_);
v___y_1866_ = v_a_1778_;
goto v___jp_1865_;
}
v___jp_1801_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1803_ = lean_unsigned_to_nat(5u);
v___x_1804_ = l_Lean_Syntax_getArg(v_stx_1792_, v___x_1803_);
v___x_1805_ = l_Lean_Syntax_matchesNull(v___x_1804_, v___x_1800_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_del_object(v___x_1794_);
lean_dec(v_stx_1792_);
v___x_1806_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
return v___x_1807_;
}
else
{
lean_object* v_ref_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v_ref_1808_ = lean_ctor_get(v___y_1802_, 2);
v___x_1809_ = lean_unsigned_to_nat(4u);
v___x_1810_ = l_Lean_Syntax_getArg(v_stx_1792_, v___x_1809_);
lean_dec(v_stx_1792_);
v___x_1811_ = l_Lean_TSyntax_getId(v___x_1810_);
v___x_1812_ = l_Lean_Server_documentUriFromModule_x3f(v___x_1811_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1836_; 
lean_del_object(v___x_1794_);
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1836_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1836_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
if (lean_obj_tag(v_a_1813_) == 1)
{
lean_object* v_val_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_del_object(v___x_1815_);
v_val_1817_ = lean_ctor_get(v_a_1813_, 0);
lean_inc(v_val_1817_);
lean_dec_ref_known(v_a_1813_, 1);
v___x_1818_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__6));
v___x_1819_ = l_Lean_Syntax_getRange_x3f(v___x_1810_, v___x_1797_);
lean_dec(v___x_1810_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v___x_1820_; 
v___x_1820_ = lean_box(0);
v___y_1781_ = v_val_1817_;
v___y_1782_ = v___x_1818_;
v___y_1783_ = v___x_1820_;
goto v___jp_1780_;
}
else
{
lean_object* v_doc_1821_; lean_object* v_val_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1831_; 
v_doc_1821_ = lean_ctor_get(v_a_1777_, 0);
v_val_1822_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1824_ = v___x_1819_;
v_isShared_1825_ = v_isSharedCheck_1831_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_val_1822_);
lean_dec(v___x_1819_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1831_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v_text_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
v_text_1826_ = lean_ctor_get(v_doc_1821_, 3);
lean_inc_ref(v_text_1826_);
v___x_1827_ = l_Lean_Syntax_Range_toLspRange(v_text_1826_, v_val_1822_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1827_);
v___x_1829_ = v___x_1824_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
v___y_1781_ = v_val_1817_;
v___y_1782_ = v___x_1818_;
v___y_1783_ = v___x_1829_;
goto v___jp_1780_;
}
}
}
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1834_; 
lean_dec(v_a_1813_);
lean_dec(v___x_1810_);
v___x_1832_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1832_);
v___x_1834_ = v___x_1815_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1850_; 
lean_dec(v___x_1810_);
v_a_1837_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1839_ = v___x_1812_;
v_isShared_1840_ = v_isSharedCheck_1850_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1812_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1850_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1841_ = lean_io_error_to_string(v_a_1837_);
v___x_1842_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
v___x_1843_ = l_Lean_MessageData_ofFormat(v___x_1842_);
lean_inc(v_ref_1808_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 1, v___x_1843_);
lean_ctor_set(v___x_1794_, 0, v_ref_1808_);
v___x_1845_ = v___x_1794_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_ref_1808_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1847_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1845_);
v___x_1847_ = v___x_1839_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
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
v___jp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1854_ = lean_unsigned_to_nat(3u);
v___x_1855_ = l_Lean_Syntax_getArg(v_stx_1792_, v___x_1854_);
v___x_1856_ = l_Lean_Syntax_isNone(v___x_1855_);
if (v___x_1856_ == 0)
{
uint8_t v___x_1857_; 
lean_inc(v___x_1855_);
v___x_1857_ = l_Lean_Syntax_matchesNull(v___x_1855_, v___y_1852_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
lean_dec(v___x_1855_);
lean_del_object(v___x_1794_);
lean_dec(v_stx_1792_);
v___x_1858_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
return v___x_1859_;
}
else
{
lean_object* v___x_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1860_ = l_Lean_Syntax_getArg(v___x_1855_, v___x_1800_);
lean_dec(v___x_1855_);
v___x_1861_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__8));
v___x_1862_ = l_Lean_Syntax_isOfKind(v___x_1860_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_del_object(v___x_1794_);
lean_dec(v_stx_1792_);
v___x_1863_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
return v___x_1864_;
}
else
{
v___y_1802_ = v___y_1853_;
goto v___jp_1801_;
}
}
}
else
{
lean_dec(v___x_1855_);
v___y_1802_ = v___y_1853_;
goto v___jp_1801_;
}
}
v___jp_1865_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; uint8_t v___x_1869_; 
v___x_1867_ = lean_unsigned_to_nat(1u);
v___x_1868_ = l_Lean_Syntax_getArg(v_stx_1792_, v___x_1867_);
v___x_1869_ = l_Lean_Syntax_isNone(v___x_1868_);
if (v___x_1869_ == 0)
{
uint8_t v___x_1870_; 
lean_inc(v___x_1868_);
v___x_1870_ = l_Lean_Syntax_matchesNull(v___x_1868_, v___x_1867_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
lean_dec(v___x_1868_);
lean_del_object(v___x_1794_);
lean_dec(v_stx_1792_);
v___x_1871_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
return v___x_1872_;
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; 
v___x_1873_ = l_Lean_Syntax_getArg(v___x_1868_, v___x_1800_);
lean_dec(v___x_1868_);
v___x_1874_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__10));
v___x_1875_ = l_Lean_Syntax_isOfKind(v___x_1873_, v___x_1874_);
if (v___x_1875_ == 0)
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_del_object(v___x_1794_);
lean_dec(v_stx_1792_);
v___x_1876_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
else
{
v___y_1852_ = v___x_1867_;
v___y_1853_ = v___y_1866_;
goto v___jp_1851_;
}
}
}
else
{
lean_dec(v___x_1868_);
v___y_1852_ = v___x_1867_;
v___y_1853_ = v___y_1866_;
goto v___jp_1851_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromImport___redArg___boxed(lean_object* v_i_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_Server_locationLinksFromImport___redArg(v_i_1891_, v_a_1892_, v_a_1893_);
lean_dec_ref(v_a_1893_);
lean_dec_ref(v_a_1892_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromImport(lean_object* v_i_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_Server_locationLinksFromImport___redArg(v_i_1896_, v_a_1897_, v_a_1900_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromImport___boxed(lean_object* v_i_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_Server_locationLinksFromImport(v_i_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec_ref(v_a_1905_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v___x_1934_; lean_object* v_originInfo_x3f_1938_; 
v___x_1934_ = lean_st_ref_get(v_a_1932_);
v_originInfo_x3f_1938_ = lean_ctor_get(v_a_1931_, 2);
if (lean_obj_tag(v_originInfo_x3f_1938_) == 1)
{
uint8_t v_kind_1939_; lean_object* v_val_1940_; lean_object* v___x_1941_; 
v_kind_1939_ = lean_ctor_get_uint8(v_a_1931_, sizeof(void*)*4);
v_val_1940_ = lean_ctor_get(v_originInfo_x3f_1938_, 0);
lean_inc(v_val_1940_);
v___x_1941_ = l_Lean_Elab_Info_toElabInfo_x3f(v_val_1940_);
if (lean_obj_tag(v___x_1941_) == 1)
{
lean_object* v_val_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1979_; 
v_val_1942_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1944_ = v___x_1941_;
v_isShared_1945_ = v_isSharedCheck_1979_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_val_1942_);
lean_dec(v___x_1941_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1979_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v_elaborator_1946_; lean_object* v_stx_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; 
v_elaborator_1946_ = lean_ctor_get(v_val_1942_, 0);
lean_inc(v_elaborator_1946_);
v_stx_1947_ = lean_ctor_get(v_val_1942_, 1);
lean_inc(v_stx_1947_);
lean_dec(v_val_1942_);
v___x_1948_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__2));
v___x_1949_ = lean_name_eq(v_elaborator_1946_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1950_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6));
v___x_1951_ = lean_name_eq(v_elaborator_1946_, v___x_1950_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; uint8_t v___x_1953_; 
v___x_1952_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8));
v___x_1953_ = lean_name_eq(v_elaborator_1946_, v___x_1952_);
if (v___x_1953_ == 0)
{
lean_object* v_env_1954_; uint8_t v___x_1955_; lean_object* v_names_1957_; lean_object* v___x_1972_; uint8_t v___x_1973_; 
v_env_1954_ = lean_ctor_get(v___x_1934_, 0);
lean_inc_ref_n(v_env_1954_, 2);
lean_dec(v___x_1934_);
v___x_1955_ = 1;
v___x_1972_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
lean_inc(v_elaborator_1946_);
v___x_1973_ = l_Lean_Environment_contains(v_env_1954_, v_elaborator_1946_, v___x_1955_);
if (v___x_1973_ == 0)
{
lean_dec(v_elaborator_1946_);
v_names_1957_ = v___x_1972_;
goto v___jp_1956_;
}
else
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_array_push(v___x_1972_, v_elaborator_1946_);
v_names_1957_ = v___x_1974_;
goto v___jp_1956_;
}
v___jp_1956_:
{
uint8_t v___x_1958_; uint8_t v___x_1959_; 
v___x_1958_ = 0;
v___x_1959_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_1939_, v___x_1958_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1961_; 
lean_dec_ref(v_env_1954_);
lean_dec(v_stx_1947_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set_tag(v___x_1944_, 0);
lean_ctor_set(v___x_1944_, 0, v_names_1957_);
v___x_1961_ = v___x_1944_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_names_1957_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
else
{
lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1963_ = l_Lean_Syntax_getKind(v_stx_1947_);
lean_inc(v___x_1963_);
v___x_1964_ = l_Lean_Environment_contains(v_env_1954_, v___x_1963_, v___x_1955_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1966_; 
lean_dec(v___x_1963_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set_tag(v___x_1944_, 0);
lean_ctor_set(v___x_1944_, 0, v_names_1957_);
v___x_1966_ = v___x_1944_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_names_1957_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
else
{
lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1968_ = lean_array_push(v_names_1957_, v___x_1963_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set_tag(v___x_1944_, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1968_);
v___x_1970_ = v___x_1944_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
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
}
else
{
lean_dec(v_stx_1947_);
lean_dec(v_elaborator_1946_);
lean_del_object(v___x_1944_);
lean_dec(v___x_1934_);
goto v___jp_1935_;
}
}
else
{
lean_dec(v_stx_1947_);
lean_dec(v_elaborator_1946_);
lean_del_object(v___x_1944_);
lean_dec(v___x_1934_);
goto v___jp_1935_;
}
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1977_; 
lean_dec(v_stx_1947_);
lean_dec(v_elaborator_1946_);
lean_dec(v___x_1934_);
v___x_1975_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
if (v_isShared_1945_ == 0)
{
lean_ctor_set_tag(v___x_1944_, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1975_);
v___x_1977_ = v___x_1944_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_dec(v___x_1941_);
lean_dec(v___x_1934_);
v___x_1980_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
v___x_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
return v___x_1981_;
}
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
lean_dec(v___x_1934_);
v___x_1982_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
return v___x_1983_;
}
v___jp_1935_:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
v___x_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
return v___x_1937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___boxed(lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(v_a_1984_, v_a_1985_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames(lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(v_a_1988_, v_a_1992_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___boxed(lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames(v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
lean_dec(v_a_1997_);
lean_dec_ref(v_a_1996_);
lean_dec_ref(v_a_1995_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(lean_object* v_as_2002_, size_t v_sz_2003_, size_t v_i_2004_, lean_object* v_b_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
uint8_t v___x_2012_; 
v___x_2012_ = lean_usize_dec_lt(v_i_2004_, v_sz_2003_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; 
v___x_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2013_, 0, v_b_2005_);
return v___x_2013_;
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2015_; 
v_a_2014_ = lean_array_uget_borrowed(v_as_2002_, v_i_2004_);
lean_inc(v_a_2014_);
v___x_2015_ = l_Lean_Server_locationLinksFromDecl(v_a_2014_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2017_; size_t v___x_2018_; size_t v___x_2019_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref_known(v___x_2015_, 1);
v___x_2017_ = l_Array_append___redArg(v_b_2005_, v_a_2016_);
lean_dec(v_a_2016_);
v___x_2018_ = ((size_t)1ULL);
v___x_2019_ = lean_usize_add(v_i_2004_, v___x_2018_);
v_i_2004_ = v___x_2019_;
v_b_2005_ = v___x_2017_;
goto _start;
}
else
{
lean_dec_ref(v_b_2005_);
return v___x_2015_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0___boxed(lean_object* v_as_2021_, lean_object* v_sz_2022_, lean_object* v_i_2023_, lean_object* v_b_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
size_t v_sz_boxed_2031_; size_t v_i_boxed_2032_; lean_object* v_res_2033_; 
v_sz_boxed_2031_ = lean_unbox_usize(v_sz_2022_);
lean_dec(v_sz_2022_);
v_i_boxed_2032_ = lean_unbox_usize(v_i_2023_);
lean_dec(v_i_2023_);
v_res_2033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_as_2021_, v_sz_boxed_2031_, v_i_boxed_2032_, v_b_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec_ref(v_as_2021_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(size_t v_sz_2034_, size_t v_i_2035_, lean_object* v_bs_2036_){
_start:
{
uint8_t v___x_2037_; 
v___x_2037_ = lean_usize_dec_lt(v_i_2035_, v_sz_2034_);
if (v___x_2037_ == 0)
{
return v_bs_2036_;
}
else
{
lean_object* v_v_2038_; lean_object* v_toLocationLink_2039_; lean_object* v_ident_x3f_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2053_; 
v_v_2038_ = lean_array_uget(v_bs_2036_, v_i_2035_);
v_toLocationLink_2039_ = lean_ctor_get(v_v_2038_, 0);
v_ident_x3f_2040_ = lean_ctor_get(v_v_2038_, 1);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_v_2038_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2042_ = v_v_2038_;
v_isShared_2043_ = v_isSharedCheck_2053_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_ident_x3f_2040_);
lean_inc(v_toLocationLink_2039_);
lean_dec(v_v_2038_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2053_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v_bs_x27_2045_; lean_object* v___x_2047_; 
v___x_2044_ = lean_unsigned_to_nat(0u);
v_bs_x27_2045_ = lean_array_uset(v_bs_2036_, v_i_2035_, v___x_2044_);
if (v_isShared_2043_ == 0)
{
v___x_2047_ = v___x_2042_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_toLocationLink_2039_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_ident_x3f_2040_);
v___x_2047_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
size_t v___x_2048_; size_t v___x_2049_; lean_object* v___x_2050_; 
lean_ctor_set_uint8(v___x_2047_, sizeof(void*)*2, v___x_2037_);
v___x_2048_ = ((size_t)1ULL);
v___x_2049_ = lean_usize_add(v_i_2035_, v___x_2048_);
v___x_2050_ = lean_array_uset(v_bs_x27_2045_, v_i_2035_, v___x_2047_);
v_i_2035_ = v___x_2049_;
v_bs_2036_ = v___x_2050_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1___boxed(lean_object* v_sz_2054_, lean_object* v_i_2055_, lean_object* v_bs_2056_){
_start:
{
size_t v_sz_boxed_2057_; size_t v_i_boxed_2058_; lean_object* v_res_2059_; 
v_sz_boxed_2057_ = lean_unbox_usize(v_sz_2054_);
lean_dec(v_sz_2054_);
v_i_boxed_2058_ = lean_unbox_usize(v_i_2055_);
lean_dec(v_i_2055_);
v_res_2059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(v_sz_boxed_2057_, v_i_boxed_2058_, v_bs_2056_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksDefault(lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v___x_2066_; lean_object* v_a_2067_; lean_object* v___x_2068_; size_t v_sz_2069_; size_t v___x_2070_; lean_object* v___x_2071_; 
v___x_2066_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(v_a_2060_, v_a_2064_);
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref(v___x_2066_);
v___x_2068_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v_sz_2069_ = lean_array_size(v_a_2067_);
v___x_2070_ = ((size_t)0ULL);
v___x_2071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_a_2067_, v_sz_2069_, v___x_2070_, v___x_2068_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
lean_dec(v_a_2067_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2081_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2081_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2081_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
size_t v_sz_2076_; lean_object* v___x_2077_; lean_object* v___x_2079_; 
v_sz_2076_ = lean_array_size(v_a_2072_);
v___x_2077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(v_sz_2076_, v___x_2070_, v_a_2072_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v___x_2077_);
v___x_2079_ = v___x_2074_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v___x_2077_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
else
{
return v___x_2071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksDefault___boxed(lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Lean_Server_locationLinksDefault(v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
lean_dec(v_a_2086_);
lean_dec_ref(v_a_2085_);
lean_dec(v_a_2084_);
lean_dec_ref(v_a_2083_);
lean_dec_ref(v_a_2082_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(lean_object* v_name_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v_env_2094_; lean_object* v___x_2095_; lean_object* v_toEnvExtension_2096_; lean_object* v_asyncMode_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2092_ = lean_box(1);
v___x_2093_ = lean_st_ref_get(v___y_2090_);
v_env_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc_ref(v_env_2094_);
lean_dec(v___x_2093_);
v___x_2095_ = l_Lean_errorExplanationExt;
v_toEnvExtension_2096_ = lean_ctor_get(v___x_2095_, 0);
v_asyncMode_2097_ = lean_ctor_get(v_toEnvExtension_2096_, 2);
v___x_2098_ = lean_box(0);
v___x_2099_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2092_, v___x_2095_, v_env_2094_, v_asyncMode_2097_, v___x_2098_);
v___x_2100_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2099_, v_name_2089_);
lean_dec(v___x_2099_);
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg___boxed(lean_object* v_name_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_name_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec(v_name_2102_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0(lean_object* v_name_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_name_2106_, v___y_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___boxed(lean_object* v_name_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0(v_name_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v_name_2114_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromErrorNameInfo(lean_object* v_eni_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_){
_start:
{
lean_object* v_stx_2129_; lean_object* v_errorName_2130_; lean_object* v___x_2131_; lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2212_; 
v_stx_2129_ = lean_ctor_get(v_eni_2122_, 0);
v_errorName_2130_ = lean_ctor_get(v_eni_2122_, 1);
v___x_2131_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_errorName_2130_, v_a_2127_);
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2134_ = v___x_2131_;
v_isShared_2135_ = v_isSharedCheck_2212_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2131_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2212_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
if (lean_obj_tag(v_a_2132_) == 1)
{
lean_object* v_val_2136_; lean_object* v_declLoc_x3f_2137_; 
v_val_2136_ = lean_ctor_get(v_a_2132_, 0);
lean_inc(v_val_2136_);
lean_dec_ref_known(v_a_2132_, 1);
v_declLoc_x3f_2137_ = lean_ctor_get(v_val_2136_, 2);
lean_inc(v_declLoc_x3f_2137_);
lean_dec(v_val_2136_);
if (lean_obj_tag(v_declLoc_x3f_2137_) == 1)
{
lean_object* v_val_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2203_; 
lean_del_object(v___x_2134_);
v_val_2138_ = lean_ctor_get(v_declLoc_x3f_2137_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_declLoc_x3f_2137_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2140_ = v_declLoc_x3f_2137_;
v_isShared_2141_ = v_isSharedCheck_2203_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_val_2138_);
lean_dec(v_declLoc_x3f_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2203_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v_module_2142_; lean_object* v_range_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2202_; 
v_module_2142_ = lean_ctor_get(v_val_2138_, 0);
v_range_2143_ = lean_ctor_get(v_val_2138_, 1);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_val_2138_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2145_ = v_val_2138_;
v_isShared_2146_ = v_isSharedCheck_2202_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_range_2143_);
lean_inc(v_module_2142_);
lean_dec(v_val_2138_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2202_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v_ref_2147_; lean_object* v___x_2148_; 
v_ref_2147_ = lean_ctor_get(v_a_2126_, 2);
v___x_2148_ = l_Lean_Server_documentUriFromModule_x3f(v_module_2142_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2185_; 
lean_del_object(v___x_2145_);
lean_del_object(v___x_2140_);
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2151_ = v___x_2148_;
v_isShared_2152_ = v_isSharedCheck_2185_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2148_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2185_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
if (lean_obj_tag(v_a_2149_) == 1)
{
lean_object* v_val_2153_; lean_object* v___x_2154_; lean_object* v___y_2156_; uint8_t v___x_2167_; lean_object* v___x_2168_; 
v_val_2153_ = lean_ctor_get(v_a_2149_, 0);
lean_inc(v_val_2153_);
lean_dec_ref_known(v_a_2149_, 1);
v___x_2154_ = l_Lean_DeclarationRange_toLspRange(v_range_2143_);
v___x_2167_ = 1;
v___x_2168_ = l_Lean_Syntax_getRange_x3f(v_stx_2129_, v___x_2167_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v___x_2169_; 
v___x_2169_ = lean_box(0);
v___y_2156_ = v___x_2169_;
goto v___jp_2155_;
}
else
{
lean_object* v_doc_2170_; lean_object* v_val_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2180_; 
v_doc_2170_ = lean_ctor_get(v_a_2123_, 0);
v_val_2171_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2173_ = v___x_2168_;
v_isShared_2174_ = v_isSharedCheck_2180_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_val_2171_);
lean_dec(v___x_2168_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2180_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v_text_2175_; lean_object* v___x_2176_; lean_object* v___x_2178_; 
v_text_2175_ = lean_ctor_get(v_doc_2170_, 3);
lean_inc_ref(v_text_2175_);
v___x_2176_ = l_Lean_Syntax_Range_toLspRange(v_text_2175_, v_val_2171_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2176_);
v___x_2178_ = v___x_2173_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
v___y_2156_ = v___x_2178_;
goto v___jp_2155_;
}
}
}
v___jp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2165_; 
lean_inc_ref(v___x_2154_);
v___x_2157_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2157_, 0, v___y_2156_);
lean_ctor_set(v___x_2157_, 1, v_val_2153_);
lean_ctor_set(v___x_2157_, 2, v___x_2154_);
lean_ctor_set(v___x_2157_, 3, v___x_2154_);
v___x_2158_ = lean_box(0);
v___x_2159_ = 0;
v___x_2160_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2160_, 0, v___x_2157_);
lean_ctor_set(v___x_2160_, 1, v___x_2158_);
lean_ctor_set_uint8(v___x_2160_, sizeof(void*)*2, v___x_2159_);
v___x_2161_ = lean_unsigned_to_nat(1u);
v___x_2162_ = lean_mk_empty_array_with_capacity(v___x_2161_);
v___x_2163_ = lean_array_push(v___x_2162_, v___x_2160_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v___x_2163_);
v___x_2165_ = v___x_2151_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2183_; 
lean_dec(v_a_2149_);
lean_dec_ref(v_range_2143_);
v___x_2181_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v___x_2181_);
v___x_2183_ = v___x_2151_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2201_; 
lean_dec_ref(v_range_2143_);
v_a_2186_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2188_ = v___x_2148_;
v_isShared_2189_ = v_isSharedCheck_2201_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2148_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2201_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2190_ = lean_io_error_to_string(v_a_2186_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set_tag(v___x_2140_, 3);
lean_ctor_set(v___x_2140_, 0, v___x_2190_);
v___x_2192_ = v___x_2140_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2193_ = l_Lean_MessageData_ofFormat(v___x_2192_);
lean_inc(v_ref_2147_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 1, v___x_2193_);
lean_ctor_set(v___x_2145_, 0, v_ref_2147_);
v___x_2195_ = v___x_2145_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_ref_2147_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2197_; 
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v___x_2195_);
v___x_2197_ = v___x_2188_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
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
lean_object* v___x_2204_; lean_object* v___x_2206_; 
lean_dec(v_declLoc_x3f_2137_);
v___x_2204_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2204_);
v___x_2206_ = v___x_2134_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
lean_dec(v_a_2132_);
v___x_2208_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2208_);
v___x_2210_ = v___x_2134_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromErrorNameInfo___boxed(lean_object* v_eni_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_Server_locationLinksFromErrorNameInfo(v_eni_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec_ref(v_a_2214_);
lean_dec_ref(v_eni_2213_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(lean_object* v_e_2221_, lean_object* v_a_2222_){
_start:
{
switch(lean_obj_tag(v_e_2221_))
{
case 4:
{
lean_object* v_declName_2224_; lean_object* v___x_2225_; 
v_declName_2224_ = lean_ctor_get(v_e_2221_, 0);
lean_inc(v_declName_2224_);
lean_dec_ref_known(v_e_2221_, 2);
v___x_2225_ = l_Lean_Meta_isInstance___redArg(v_declName_2224_, v_a_2222_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2241_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2228_ = v___x_2225_;
v_isShared_2229_ = v_isSharedCheck_2241_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2225_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2241_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
uint8_t v___x_2230_; 
v___x_2230_ = lean_unbox(v_a_2226_);
lean_dec(v_a_2226_);
if (v___x_2230_ == 0)
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
lean_dec(v_declName_2224_);
v___x_2231_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v___x_2231_);
v___x_2233_ = v___x_2228_;
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
else
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2235_ = lean_unsigned_to_nat(1u);
v___x_2236_ = lean_mk_empty_array_with_capacity(v___x_2235_);
v___x_2237_ = lean_array_push(v___x_2236_, v_declName_2224_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v___x_2237_);
v___x_2239_ = v___x_2228_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_dec(v_declName_2224_);
v_a_2242_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2225_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2225_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
case 5:
{
lean_object* v_fn_2250_; lean_object* v_arg_2251_; lean_object* v___x_2252_; 
v_fn_2250_ = lean_ctor_get(v_e_2221_, 0);
lean_inc_ref(v_fn_2250_);
v_arg_2251_ = lean_ctor_get(v_e_2221_, 1);
lean_inc_ref(v_arg_2251_);
lean_dec_ref_known(v_e_2221_, 2);
v___x_2252_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_fn_2250_, v_a_2222_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2254_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2253_);
lean_dec_ref_known(v___x_2252_, 1);
v___x_2254_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_arg_2251_, v_a_2222_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2263_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2257_ = v___x_2254_;
v_isShared_2258_ = v_isSharedCheck_2263_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2254_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2263_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2259_ = l_Array_append___redArg(v_a_2255_, v_a_2253_);
lean_dec(v_a_2253_);
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 0, v___x_2259_);
v___x_2261_ = v___x_2257_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
else
{
lean_dec(v_a_2253_);
return v___x_2254_;
}
}
else
{
lean_dec_ref(v_arg_2251_);
return v___x_2252_;
}
}
case 10:
{
lean_object* v_expr_2264_; 
v_expr_2264_ = lean_ctor_get(v_e_2221_, 1);
lean_inc_ref(v_expr_2264_);
lean_dec_ref_known(v_e_2221_, 2);
v_e_2221_ = v_expr_2264_;
goto _start;
}
default: 
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_dec_ref(v_e_2221_);
v___x_2266_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
return v___x_2267_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg___boxed(lean_object* v_e_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_e_2268_, v_a_2269_);
lean_dec(v_a_2269_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances(lean_object* v_e_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_e_2272_, v_a_2277_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___boxed(lean_object* v_e_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances(v_e_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_);
lean_dec(v_a_2285_);
lean_dec_ref(v_a_2284_);
lean_dec(v_a_2283_);
lean_dec_ref(v_a_2282_);
lean_dec_ref(v_a_2281_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromInstanceProjection(lean_object* v_e_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = l_Lean_Expr_getAppFn(v_e_2288_);
v___x_2296_ = l_Lean_Expr_consumeMData(v___x_2295_);
lean_dec_ref(v___x_2295_);
if (lean_obj_tag(v___x_2296_) == 4)
{
lean_object* v_declName_2297_; lean_object* v___x_2298_; 
v_declName_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_declName_2297_);
lean_dec_ref_known(v___x_2296_, 2);
v___x_2298_ = l_Lean_Server_getInstanceProjectionArg_x3f(v_e_2288_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2333_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2333_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2333_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
if (lean_obj_tag(v_a_2299_) == 1)
{
lean_object* v_val_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
lean_del_object(v___x_2301_);
v_val_2303_ = lean_ctor_get(v_a_2299_, 0);
lean_inc(v_val_2303_);
lean_dec_ref_known(v_a_2299_, 1);
v___x_2304_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_2305_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_val_2303_, v_a_2293_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; size_t v_sz_2307_; size_t v___x_2308_; lean_object* v___x_2309_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v_sz_2307_ = lean_array_size(v_a_2306_);
v___x_2308_ = ((size_t)0ULL);
v___x_2309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_a_2306_, v_sz_2307_, v___x_2308_, v___x_2304_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
lean_dec(v_a_2306_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2311_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref_known(v___x_2309_, 1);
v___x_2311_ = l_Lean_Server_locationLinksFromDecl(v_declName_2297_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2320_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2314_ = v___x_2311_;
v_isShared_2315_ = v_isSharedCheck_2320_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2311_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2320_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2316_ = l_Array_append___redArg(v_a_2310_, v_a_2312_);
lean_dec(v_a_2312_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 0, v___x_2316_);
v___x_2318_ = v___x_2314_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
else
{
lean_dec(v_a_2310_);
return v___x_2311_;
}
}
else
{
lean_dec(v_declName_2297_);
return v___x_2309_;
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec(v_declName_2297_);
v_a_2321_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2305_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2305_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2331_; 
lean_dec(v_a_2299_);
lean_dec(v_declName_2297_);
v___x_2329_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2329_);
v___x_2331_ = v___x_2301_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v_declName_2297_);
v_a_2334_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2298_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2298_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
lean_dec_ref(v___x_2296_);
lean_dec_ref(v_e_2288_);
v___x_2342_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
return v___x_2343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromInstanceProjection___boxed(lean_object* v_e_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Lean_Server_locationLinksFromInstanceProjection(v_e_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec_ref(v_a_2345_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(lean_object* v_as_2352_, size_t v_sz_2353_, size_t v_i_2354_, lean_object* v_b_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v_newLL_2363_; uint8_t v___x_2368_; 
v___x_2368_ = lean_usize_dec_lt(v_i_2354_, v_sz_2353_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; 
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v_b_2355_);
return v___x_2369_;
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2371_; 
v_a_2370_ = lean_array_uget_borrowed(v_as_2352_, v_i_2354_);
v___x_2371_ = l_Lean_Expr_consumeMData(v_a_2370_);
switch(lean_obj_tag(v___x_2371_))
{
case 4:
{
lean_object* v_declName_2372_; lean_object* v___x_2373_; 
v_declName_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_declName_2372_);
lean_dec_ref_known(v___x_2371_, 2);
v___x_2373_ = l_Lean_Server_locationLinksFromDecl(v_declName_2372_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2374_);
lean_dec_ref_known(v___x_2373_, 1);
v_newLL_2363_ = v_a_2374_;
goto v___jp_2362_;
}
else
{
lean_dec_ref(v_b_2355_);
return v___x_2373_;
}
}
case 1:
{
lean_object* v_fvarId_2375_; lean_object* v___x_2376_; 
v_fvarId_2375_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_fvarId_2375_);
lean_dec_ref_known(v___x_2371_, 1);
v___x_2376_ = l_Lean_Server_locationLinksFromBinder___redArg(v_fvarId_2375_, v___y_2356_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref_known(v___x_2376_, 1);
v_newLL_2363_ = v_a_2377_;
goto v___jp_2362_;
}
else
{
lean_dec_ref(v_b_2355_);
return v___x_2376_;
}
}
default: 
{
lean_object* v___x_2378_; 
lean_dec_ref(v___x_2371_);
lean_inc(v_a_2370_);
v___x_2378_ = l_Lean_Server_locationLinksFromInstanceProjection(v_a_2370_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2378_, 1);
v_newLL_2363_ = v_a_2379_;
goto v___jp_2362_;
}
else
{
lean_dec_ref(v_b_2355_);
return v___x_2378_;
}
}
}
}
v___jp_2362_:
{
lean_object* v___x_2364_; size_t v___x_2365_; size_t v___x_2366_; 
v___x_2364_ = l_Array_append___redArg(v_b_2355_, v_newLL_2363_);
lean_dec_ref(v_newLL_2363_);
v___x_2365_ = ((size_t)1ULL);
v___x_2366_ = lean_usize_add(v_i_2354_, v___x_2365_);
v_i_2354_ = v___x_2366_;
v_b_2355_ = v___x_2364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0___boxed(lean_object* v_as_2380_, lean_object* v_sz_2381_, lean_object* v_i_2382_, lean_object* v_b_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
size_t v_sz_boxed_2390_; size_t v_i_boxed_2391_; lean_object* v_res_2392_; 
v_sz_boxed_2390_ = lean_unbox_usize(v_sz_2381_);
lean_dec(v_sz_2381_);
v_i_boxed_2391_ = lean_unbox_usize(v_i_2382_);
lean_dec(v_i_2382_);
v_res_2392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(v_as_2380_, v_sz_boxed_2390_, v_i_boxed_2391_, v_b_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec_ref(v_as_2380_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromTermInfo(lean_object* v_ti_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
uint8_t v_kind_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v_kind_2400_ = lean_ctor_get_uint8(v_a_2394_, sizeof(void*)*4);
v___x_2401_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_2402_ = l_Lean_Server_GoToKind_determineTargetExprs(v_kind_2400_, v_ti_2393_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; size_t v_sz_2404_; size_t v___x_2405_; lean_object* v___x_2406_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref_known(v___x_2402_, 1);
v_sz_2404_ = lean_array_size(v_a_2403_);
v___x_2405_ = ((size_t)0ULL);
v___x_2406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(v_a_2403_, v_sz_2404_, v___x_2405_, v___x_2401_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
lean_dec(v_a_2403_);
return v___x_2406_;
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
v_a_2407_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2402_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2402_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromTermInfo___boxed(lean_object* v_ti_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_Server_locationLinksFromTermInfo(v_ti_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
lean_dec_ref(v_a_2416_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDelabTermInfo(lean_object* v_dti_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_){
_start:
{
lean_object* v_location_x3f_2430_; 
v_location_x3f_2430_ = lean_ctor_get(v_dti_2423_, 1);
lean_inc(v_location_x3f_2430_);
if (lean_obj_tag(v_location_x3f_2430_) == 1)
{
lean_object* v_val_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2500_; 
v_val_2431_ = lean_ctor_get(v_location_x3f_2430_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_location_x3f_2430_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2433_ = v_location_x3f_2430_;
v_isShared_2434_ = v_isSharedCheck_2500_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_val_2431_);
lean_dec(v_location_x3f_2430_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2500_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v_toTermInfo_2435_; lean_object* v_module_2436_; lean_object* v_range_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2499_; 
v_toTermInfo_2435_ = lean_ctor_get(v_dti_2423_, 0);
v_module_2436_ = lean_ctor_get(v_val_2431_, 0);
v_range_2437_ = lean_ctor_get(v_val_2431_, 1);
v_isSharedCheck_2499_ = !lean_is_exclusive(v_val_2431_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2439_ = v_val_2431_;
v_isShared_2440_ = v_isSharedCheck_2499_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_range_2437_);
lean_inc(v_module_2436_);
lean_dec(v_val_2431_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2499_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v_ref_2441_; lean_object* v___x_2442_; 
v_ref_2441_ = lean_ctor_get(v_a_2427_, 2);
v___x_2442_ = l_Lean_Server_documentUriFromModule_x3f(v_module_2436_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2482_; 
lean_del_object(v___x_2439_);
lean_del_object(v___x_2433_);
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2482_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2482_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
if (lean_obj_tag(v_a_2443_) == 1)
{
lean_object* v_val_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2480_; 
v_val_2447_ = lean_ctor_get(v_a_2443_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_a_2443_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2449_ = v_a_2443_;
v_isShared_2450_ = v_isSharedCheck_2480_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_val_2447_);
lean_dec(v_a_2443_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2480_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2451_; lean_object* v___y_2453_; lean_object* v___x_2465_; 
v___x_2451_ = l_Lean_DeclarationRange_toLspRange(v_range_2437_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set_tag(v___x_2449_, 13);
lean_ctor_set(v___x_2449_, 0, v_dti_2423_);
v___x_2465_ = v___x_2449_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_dti_2423_);
v___x_2465_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2464_;
}
v___jp_2452_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2462_; 
lean_inc_ref(v___x_2451_);
v___x_2454_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2454_, 0, v___y_2453_);
lean_ctor_set(v___x_2454_, 1, v_val_2447_);
lean_ctor_set(v___x_2454_, 2, v___x_2451_);
lean_ctor_set(v___x_2454_, 3, v___x_2451_);
v___x_2455_ = lean_box(0);
v___x_2456_ = 0;
v___x_2457_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2457_, 0, v___x_2454_);
lean_ctor_set(v___x_2457_, 1, v___x_2455_);
lean_ctor_set_uint8(v___x_2457_, sizeof(void*)*2, v___x_2456_);
v___x_2458_ = lean_unsigned_to_nat(1u);
v___x_2459_ = lean_mk_empty_array_with_capacity(v___x_2458_);
v___x_2460_ = lean_array_push(v___x_2459_, v___x_2457_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2460_);
v___x_2462_ = v___x_2445_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2460_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
v_reusejp_2464_:
{
lean_object* v___x_2466_; 
v___x_2466_ = l_Lean_Elab_Info_range_x3f(v___x_2465_);
lean_dec_ref(v___x_2465_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v___x_2467_; 
v___x_2467_ = lean_box(0);
v___y_2453_ = v___x_2467_;
goto v___jp_2452_;
}
else
{
lean_object* v_doc_2468_; lean_object* v_val_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2478_; 
v_doc_2468_ = lean_ctor_get(v_a_2424_, 0);
v_val_2469_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2471_ = v___x_2466_;
v_isShared_2472_ = v_isSharedCheck_2478_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_val_2469_);
lean_dec(v___x_2466_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2478_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v_text_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
v_text_2473_ = lean_ctor_get(v_doc_2468_, 3);
lean_inc_ref(v_text_2473_);
v___x_2474_ = l_Lean_Syntax_Range_toLspRange(v_text_2473_, v_val_2469_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v___x_2474_);
v___x_2476_ = v___x_2471_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
v___y_2453_ = v___x_2476_;
goto v___jp_2452_;
}
}
}
}
}
}
else
{
lean_object* v___x_2481_; 
lean_inc_ref(v_toTermInfo_2435_);
lean_del_object(v___x_2445_);
lean_dec(v_a_2443_);
lean_dec_ref(v_range_2437_);
lean_dec_ref(v_dti_2423_);
v___x_2481_ = l_Lean_Server_locationLinksFromTermInfo(v_toTermInfo_2435_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
return v___x_2481_;
}
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2498_; 
lean_dec_ref(v_range_2437_);
lean_dec_ref(v_dti_2423_);
v_a_2483_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2485_ = v___x_2442_;
v_isShared_2486_ = v_isSharedCheck_2498_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2442_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2498_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; lean_object* v___x_2489_; 
v___x_2487_ = lean_io_error_to_string(v_a_2483_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set_tag(v___x_2433_, 3);
lean_ctor_set(v___x_2433_, 0, v___x_2487_);
v___x_2489_ = v___x_2433_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2487_);
v___x_2489_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2490_ = l_Lean_MessageData_ofFormat(v___x_2489_);
lean_inc(v_ref_2441_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 1, v___x_2490_);
lean_ctor_set(v___x_2439_, 0, v_ref_2441_);
v___x_2492_ = v___x_2439_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_ref_2441_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2494_; 
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2492_);
v___x_2494_ = v___x_2485_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2492_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
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
lean_object* v_toTermInfo_2501_; lean_object* v___x_2502_; 
lean_dec(v_location_x3f_2430_);
v_toTermInfo_2501_ = lean_ctor_get(v_dti_2423_, 0);
lean_inc_ref(v_toTermInfo_2501_);
lean_dec_ref(v_dti_2423_);
v___x_2502_ = l_Lean_Server_locationLinksFromTermInfo(v_toTermInfo_2501_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
return v___x_2502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDelabTermInfo___boxed(lean_object* v_dti_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_Server_locationLinksFromDelabTermInfo(v_dti_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec_ref(v_a_2504_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(lean_object* v_e_2511_, lean_object* v___y_2512_){
_start:
{
uint8_t v___x_2514_; 
v___x_2514_ = l_Lean_Expr_hasMVar(v_e_2511_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2515_, 0, v_e_2511_);
return v___x_2515_;
}
else
{
lean_object* v___x_2516_; lean_object* v_mctx_2517_; lean_object* v___x_2518_; lean_object* v_fst_2519_; lean_object* v_snd_2520_; lean_object* v___x_2521_; lean_object* v_cache_2522_; lean_object* v_zetaDeltaFVarIds_2523_; lean_object* v_postponed_2524_; lean_object* v_diag_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2534_; 
v___x_2516_ = lean_st_ref_get(v___y_2512_);
v_mctx_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc_ref(v_mctx_2517_);
lean_dec(v___x_2516_);
v___x_2518_ = l_Lean_instantiateMVarsCore(v_mctx_2517_, v_e_2511_);
v_fst_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_fst_2519_);
v_snd_2520_ = lean_ctor_get(v___x_2518_, 1);
lean_inc(v_snd_2520_);
lean_dec_ref(v___x_2518_);
v___x_2521_ = lean_st_ref_take(v___y_2512_);
v_cache_2522_ = lean_ctor_get(v___x_2521_, 1);
v_zetaDeltaFVarIds_2523_ = lean_ctor_get(v___x_2521_, 2);
v_postponed_2524_ = lean_ctor_get(v___x_2521_, 3);
v_diag_2525_ = lean_ctor_get(v___x_2521_, 4);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; 
v_unused_2535_ = lean_ctor_get(v___x_2521_, 0);
lean_dec(v_unused_2535_);
v___x_2527_ = v___x_2521_;
v_isShared_2528_ = v_isSharedCheck_2534_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_diag_2525_);
lean_inc(v_postponed_2524_);
lean_inc(v_zetaDeltaFVarIds_2523_);
lean_inc(v_cache_2522_);
lean_dec(v___x_2521_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2534_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v_snd_2520_);
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_snd_2520_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_cache_2522_);
lean_ctor_set(v_reuseFailAlloc_2533_, 2, v_zetaDeltaFVarIds_2523_);
lean_ctor_set(v_reuseFailAlloc_2533_, 3, v_postponed_2524_);
lean_ctor_set(v_reuseFailAlloc_2533_, 4, v_diag_2525_);
v___x_2530_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = lean_st_ref_put(v___y_2512_, v___x_2530_);
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_fst_2519_);
return v___x_2532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg___boxed(lean_object* v_e_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(v_e_2536_, v___y_2537_);
lean_dec(v___y_2537_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0(lean_object* v_e_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v___x_2547_; 
v___x_2547_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(v_e_2540_, v___y_2543_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___boxed(lean_object* v_e_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0(v_e_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec_ref(v___y_2549_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromFieldInfo(lean_object* v_fi_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_){
_start:
{
uint8_t v_kind_2563_; uint8_t v___x_2564_; uint8_t v___x_2565_; 
v_kind_2563_ = lean_ctor_get_uint8(v_a_2557_, sizeof(void*)*4);
v___x_2564_ = 2;
v___x_2565_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_2563_, v___x_2564_);
if (v___x_2565_ == 0)
{
lean_object* v_projName_2566_; lean_object* v___x_2567_; 
v_projName_2566_ = lean_ctor_get(v_fi_2556_, 0);
lean_inc(v_projName_2566_);
lean_dec_ref(v_fi_2556_);
v___x_2567_ = l_Lean_Server_locationLinksFromDecl(v_projName_2566_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
return v___x_2567_;
}
else
{
lean_object* v_val_2568_; lean_object* v___x_2569_; 
v_val_2568_ = lean_ctor_get(v_fi_2556_, 3);
lean_inc_ref(v_val_2568_);
lean_dec_ref(v_fi_2556_);
lean_inc(v_a_2561_);
lean_inc_ref(v_a_2560_);
lean_inc(v_a_2559_);
lean_inc_ref(v_a_2558_);
v___x_2569_ = lean_infer_type(v_val_2568_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2571_; lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2584_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
lean_dec_ref_known(v___x_2569_, 1);
v___x_2571_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(v_a_2570_, v_a_2559_);
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2584_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2584_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = l_Lean_Expr_getAppFn(v_a_2572_);
lean_dec(v_a_2572_);
v___x_2577_ = l_Lean_Expr_constName_x3f(v___x_2576_);
lean_dec_ref(v___x_2576_);
if (lean_obj_tag(v___x_2577_) == 1)
{
lean_object* v_val_2578_; lean_object* v___x_2579_; 
lean_del_object(v___x_2574_);
v_val_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_val_2578_);
lean_dec_ref_known(v___x_2577_, 1);
v___x_2579_ = l_Lean_Server_locationLinksFromDecl(v_val_2578_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
return v___x_2579_;
}
else
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
lean_dec(v___x_2577_);
v___x_2580_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 0, v___x_2580_);
v___x_2582_ = v___x_2574_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
v_a_2585_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2569_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2569_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromFieldInfo___boxed(lean_object* v_fi_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l_Lean_Server_locationLinksFromFieldInfo(v_fi_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_a_2596_);
lean_dec_ref(v_a_2595_);
lean_dec_ref(v_a_2594_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromOptionInfo(lean_object* v_i_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v_declName_2608_; lean_object* v___x_2609_; 
v_declName_2608_ = lean_ctor_get(v_i_2601_, 2);
lean_inc(v_declName_2608_);
lean_dec_ref(v_i_2601_);
v___x_2609_ = l_Lean_Server_locationLinksFromDecl(v_declName_2608_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromOptionInfo___boxed(lean_object* v_i_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Lean_Server_locationLinksFromOptionInfo(v_i_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
lean_dec(v_a_2613_);
lean_dec_ref(v_a_2612_);
lean_dec_ref(v_a_2611_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromCommandInfo___redArg(lean_object* v_i_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v_elaborator_2625_; 
v_elaborator_2625_ = lean_ctor_get(v_i_2618_, 0);
if (lean_obj_tag(v_elaborator_2625_) == 1)
{
lean_object* v_pre_2626_; 
v_pre_2626_ = lean_ctor_get(v_elaborator_2625_, 0);
if (lean_obj_tag(v_pre_2626_) == 0)
{
lean_object* v_str_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; 
v_str_2627_ = lean_ctor_get(v_elaborator_2625_, 1);
v___x_2628_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__3));
v___x_2629_ = lean_string_dec_eq(v_str_2627_, v___x_2628_);
if (v___x_2629_ == 0)
{
lean_dec_ref(v_i_2618_);
goto v___jp_2622_;
}
else
{
uint8_t v_kind_2630_; uint8_t v___x_2631_; uint8_t v___x_2632_; 
v_kind_2630_ = lean_ctor_get_uint8(v_a_2619_, sizeof(void*)*4);
v___x_2631_ = 2;
v___x_2632_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_2630_, v___x_2631_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_Server_locationLinksFromImport___redArg(v_i_2618_, v_a_2619_, v_a_2620_);
return v___x_2633_;
}
else
{
lean_dec_ref(v_i_2618_);
goto v___jp_2622_;
}
}
}
else
{
lean_dec_ref(v_i_2618_);
goto v___jp_2622_;
}
}
else
{
lean_dec_ref(v_i_2618_);
goto v___jp_2622_;
}
v___jp_2622_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
return v___x_2624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromCommandInfo___redArg___boxed(lean_object* v_i_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lean_Server_locationLinksFromCommandInfo___redArg(v_i_2634_, v_a_2635_, v_a_2636_);
lean_dec_ref(v_a_2636_);
lean_dec_ref(v_a_2635_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromCommandInfo(lean_object* v_i_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Lean_Server_locationLinksFromCommandInfo___redArg(v_i_2639_, v_a_2640_, v_a_2643_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromCommandInfo___boxed(lean_object* v_i_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_Lean_Server_locationLinksFromCommandInfo(v_i_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec_ref(v_a_2648_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___lam__0(uint8_t v_kind_2655_, lean_object* v_ll_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
uint8_t v___y_2664_; uint8_t v___x_2676_; uint8_t v___x_2677_; 
v___x_2676_ = 0;
v___x_2677_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_2655_, v___x_2676_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2679_; uint8_t v___x_2680_; 
v___x_2678_ = lean_array_get_size(v_ll_2656_);
v___x_2679_ = lean_unsigned_to_nat(0u);
v___x_2680_ = lean_nat_dec_eq(v___x_2678_, v___x_2679_);
v___y_2664_ = v___x_2680_;
goto v___jp_2663_;
}
else
{
v___y_2664_ = v___x_2677_;
goto v___jp_2663_;
}
v___jp_2663_:
{
if (v___y_2664_ == 0)
{
lean_object* v___x_2665_; 
v___x_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2665_, 0, v_ll_2656_);
return v___x_2665_;
}
else
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_Server_locationLinksDefault(v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2675_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2675_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2675_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2671_ = l_Array_append___redArg(v_ll_2656_, v_a_2667_);
lean_dec(v_a_2667_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2671_);
v___x_2673_ = v___x_2669_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
else
{
lean_dec_ref(v_ll_2656_);
return v___x_2666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___lam__0___boxed(lean_object* v_kind_2681_, lean_object* v_ll_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
uint8_t v_kind_boxed_2689_; lean_object* v_res_2690_; 
v_kind_boxed_2689_ = lean_unbox(v_kind_2681_);
v_res_2690_ = l_Lean_Server_locationLinksOfInfo___lam__0(v_kind_boxed_2689_, v_ll_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec_ref(v___y_2683_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___lam__1(lean_object* v_info_2691_, lean_object* v___f_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
switch(lean_obj_tag(v_info_2691_))
{
case 1:
{
lean_object* v_i_2699_; lean_object* v___x_2700_; 
v_i_2699_ = lean_ctor_get(v_info_2691_, 0);
lean_inc_ref(v_i_2699_);
lean_dec_ref_known(v_info_2691_, 1);
v___x_2700_ = l_Lean_Server_locationLinksFromTermInfo(v_i_2699_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_a_2701_; lean_object* v___x_2702_; 
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_a_2701_);
lean_dec_ref_known(v___x_2700_, 1);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
lean_inc_ref(v___y_2693_);
v___x_2702_ = lean_apply_7(v___f_2692_, v_a_2701_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, lean_box(0));
return v___x_2702_;
}
else
{
lean_dec_ref(v___f_2692_);
return v___x_2700_;
}
}
case 13:
{
lean_object* v_i_2703_; lean_object* v___x_2704_; 
v_i_2703_ = lean_ctor_get(v_info_2691_, 0);
lean_inc_ref(v_i_2703_);
lean_dec_ref_known(v_info_2691_, 1);
v___x_2704_ = l_Lean_Server_locationLinksFromDelabTermInfo(v_i_2703_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2706_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2704_, 1);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
lean_inc_ref(v___y_2693_);
v___x_2706_ = lean_apply_7(v___f_2692_, v_a_2705_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, lean_box(0));
return v___x_2706_;
}
else
{
lean_dec_ref(v___f_2692_);
return v___x_2704_;
}
}
case 7:
{
lean_object* v_i_2707_; lean_object* v___x_2708_; 
v_i_2707_ = lean_ctor_get(v_info_2691_, 0);
lean_inc_ref(v_i_2707_);
lean_dec_ref_known(v_info_2691_, 1);
v___x_2708_ = l_Lean_Server_locationLinksFromFieldInfo(v_i_2707_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v___x_2710_; 
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_a_2709_);
lean_dec_ref_known(v___x_2708_, 1);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
lean_inc_ref(v___y_2693_);
v___x_2710_ = lean_apply_7(v___f_2692_, v_a_2709_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, lean_box(0));
return v___x_2710_;
}
else
{
lean_dec_ref(v___f_2692_);
return v___x_2708_;
}
}
case 5:
{
lean_object* v_i_2711_; lean_object* v___x_2712_; 
v_i_2711_ = lean_ctor_get(v_info_2691_, 0);
lean_inc_ref(v_i_2711_);
lean_dec_ref_known(v_info_2691_, 1);
v___x_2712_ = l_Lean_Server_locationLinksFromOptionInfo(v_i_2711_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2714_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
lean_inc(v_a_2713_);
lean_dec_ref_known(v___x_2712_, 1);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
lean_inc_ref(v___y_2693_);
v___x_2714_ = lean_apply_7(v___f_2692_, v_a_2713_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, lean_box(0));
return v___x_2714_;
}
else
{
lean_dec_ref(v___f_2692_);
return v___x_2712_;
}
}
case 3:
{
lean_object* v_i_2715_; lean_object* v___x_2716_; 
v_i_2715_ = lean_ctor_get(v_info_2691_, 0);
lean_inc_ref(v_i_2715_);
lean_dec_ref_known(v_info_2691_, 1);
v___x_2716_ = l_Lean_Server_locationLinksFromCommandInfo___redArg(v_i_2715_, v___y_2693_, v___y_2696_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2718_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2716_, 1);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
lean_inc_ref(v___y_2693_);
v___x_2718_ = lean_apply_7(v___f_2692_, v_a_2717_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, lean_box(0));
return v___x_2718_;
}
else
{
lean_dec_ref(v___f_2692_);
return v___x_2716_;
}
}
case 6:
{
lean_object* v_i_2719_; lean_object* v___x_2720_; 
v_i_2719_ = lean_ctor_get(v_info_2691_, 0);
lean_inc_ref(v_i_2719_);
lean_dec_ref_known(v_info_2691_, 1);
v___x_2720_ = l_Lean_Server_locationLinksFromErrorNameInfo(v_i_2719_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec_ref(v_i_2719_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v___x_2722_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2720_, 1);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
lean_inc_ref(v___y_2693_);
v___x_2722_ = lean_apply_7(v___f_2692_, v_a_2721_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, lean_box(0));
return v___x_2722_;
}
else
{
lean_dec_ref(v___f_2692_);
return v___x_2720_;
}
}
case 17:
{
lean_object* v_i_2723_; lean_object* v_name_2724_; lean_object* v___x_2725_; 
v_i_2723_ = lean_ctor_get(v_info_2691_, 0);
lean_inc_ref(v_i_2723_);
lean_dec_ref_known(v_info_2691_, 1);
v_name_2724_ = lean_ctor_get(v_i_2723_, 1);
lean_inc(v_name_2724_);
lean_dec_ref(v_i_2723_);
v___x_2725_ = l_Lean_Server_locationLinksFromDecl(v_name_2724_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2727_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2725_, 1);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
lean_inc_ref(v___y_2693_);
v___x_2727_ = lean_apply_7(v___f_2692_, v_a_2726_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, lean_box(0));
return v___x_2727_;
}
else
{
lean_dec_ref(v___f_2692_);
return v___x_2725_;
}
}
default: 
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
lean_dec_ref(v_info_2691_);
v___x_2728_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
lean_inc_ref(v___y_2693_);
v___x_2729_ = lean_apply_7(v___f_2692_, v___x_2728_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, lean_box(0));
return v___x_2729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___lam__1___boxed(lean_object* v_info_2730_, lean_object* v___f_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_Server_locationLinksOfInfo___lam__1(v_info_2730_, v___f_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec_ref(v___y_2732_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo(lean_object* v_doc_2739_, uint8_t v_kind_2740_, lean_object* v_ictx_2741_, lean_object* v_infoTree_x3f_2742_){
_start:
{
lean_object* v_ctx_2744_; lean_object* v_info_2745_; lean_object* v_children_2746_; lean_object* v___x_2747_; lean_object* v___f_2748_; lean_object* v___y_2749_; lean_object* v___x_2750_; lean_object* v_ctx_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v_ctx_2744_ = lean_ctor_get(v_ictx_2741_, 0);
lean_inc_ref(v_ctx_2744_);
v_info_2745_ = lean_ctor_get(v_ictx_2741_, 1);
lean_inc_ref_n(v_info_2745_, 3);
v_children_2746_ = lean_ctor_get(v_ictx_2741_, 2);
lean_inc_ref(v_children_2746_);
lean_dec_ref(v_ictx_2741_);
v___x_2747_ = lean_box(v_kind_2740_);
v___f_2748_ = lean_alloc_closure((void*)(l_Lean_Server_locationLinksOfInfo___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2748_, 0, v___x_2747_);
v___y_2749_ = lean_alloc_closure((void*)(l_Lean_Server_locationLinksOfInfo___lam__1___boxed), 8, 2);
lean_closure_set(v___y_2749_, 0, v_info_2745_);
lean_closure_set(v___y_2749_, 1, v___f_2748_);
v___x_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2750_, 0, v_info_2745_);
v_ctx_2751_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_ctx_2751_, 0, v_doc_2739_);
lean_ctor_set(v_ctx_2751_, 1, v_infoTree_x3f_2742_);
lean_ctor_set(v_ctx_2751_, 2, v___x_2750_);
lean_ctor_set(v_ctx_2751_, 3, v_children_2746_);
lean_ctor_set_uint8(v_ctx_2751_, sizeof(void*)*4, v_kind_2740_);
v___x_2752_ = l_Lean_Elab_Info_lctx(v_info_2745_);
lean_dec_ref(v_info_2745_);
v___x_2753_ = l_Lean_Server_GoToM_run___redArg(v_ctx_2751_, v_ctx_2744_, v___x_2752_, v___y_2749_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___boxed(lean_object* v_doc_2754_, lean_object* v_kind_2755_, lean_object* v_ictx_2756_, lean_object* v_infoTree_x3f_2757_, lean_object* v_a_2758_){
_start:
{
uint8_t v_kind_boxed_2759_; lean_object* v_res_2760_; 
v_kind_boxed_2759_ = lean_unbox(v_kind_2755_);
v_res_2760_ = l_Lean_Server_locationLinksOfInfo(v_doc_2754_, v_kind_boxed_2759_, v_ictx_2756_, v_infoTree_x3f_2757_);
return v_res_2760_;
}
}
lean_object* runtime_initialize_Lean_Server_Utils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_Internal(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ForEachExpr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_GoTo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
