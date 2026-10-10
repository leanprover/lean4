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
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__27;
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
lean_object* l_Lean_Server_GoToKind_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Server_GoToKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_Server_GoToKind_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Server_GoToKind_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Server_GoToKind_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lean_Server_GoToKind_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_Server_GoToKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Server_GoToKind_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Server_GoToKind_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_declaration_elim___redArg(lean_object* v_declaration_24_){
_start:
{
lean_inc(v_declaration_24_);
return v_declaration_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_declaration_elim___redArg___boxed(lean_object* v_declaration_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Server_GoToKind_declaration_elim___redArg(v_declaration_25_);
lean_dec(v_declaration_25_);
return v_res_26_;
}
}
lean_object* l_Lean_Server_GoToKind_declaration_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_declaration_30_){
_start:
{
lean_inc(v_declaration_30_);
return v_declaration_30_;
}
}
LEAN_EXPORT void l_Lean_Server_GoToKind_declaration_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_declaration_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Server_GoToKind_declaration_elim(lean_box(0), v_t_28_, lean_box(0), v_declaration_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_declaration_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_declaration_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Server_GoToKind_declaration_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_declaration_35_);
lean_dec(v_declaration_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_definition_elim___redArg(lean_object* v_definition_38_){
_start:
{
lean_inc(v_definition_38_);
return v_definition_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_definition_elim___redArg___boxed(lean_object* v_definition_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Server_GoToKind_definition_elim___redArg(v_definition_39_);
lean_dec(v_definition_39_);
return v_res_40_;
}
}
lean_object* l_Lean_Server_GoToKind_definition_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_definition_44_){
_start:
{
lean_inc(v_definition_44_);
return v_definition_44_;
}
}
LEAN_EXPORT void l_Lean_Server_GoToKind_definition_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_definition_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Server_GoToKind_definition_elim(lean_box(0), v_t_42_, lean_box(0), v_definition_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_definition_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_definition_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Server_GoToKind_definition_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_definition_49_);
lean_dec(v_definition_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_type_elim___redArg(lean_object* v_type_52_){
_start:
{
lean_inc(v_type_52_);
return v_type_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_type_elim___redArg___boxed(lean_object* v_type_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Server_GoToKind_type_elim___redArg(v_type_53_);
lean_dec(v_type_53_);
return v_res_54_;
}
}
lean_object* l_Lean_Server_GoToKind_type_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_type_58_){
_start:
{
lean_inc(v_type_58_);
return v_type_58_;
}
}
LEAN_EXPORT void l_Lean_Server_GoToKind_type_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_type_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Server_GoToKind_type_elim(lean_box(0), v_t_56_, lean_box(0), v_type_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_type_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_type_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_Server_GoToKind_type_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_type_63_);
lean_dec(v_type_63_);
return v_res_65_;
}
}
uint8_t l_Lean_Server_instBEqGoToKind_beq(uint8_t v_x_66_, uint8_t v_y_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_68_ = lean_box(v_x_66_);
v___x_69_ = lean_obj_tag_nat(v___x_68_);
lean_dec(v___x_68_);
v___x_70_ = lean_box(v_y_67_);
v___x_71_ = lean_obj_tag_nat(v___x_70_);
lean_dec(v___x_70_);
v___x_72_ = lean_nat_dec_eq(v___x_69_, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT void l_Lean_Server_instBEqGoToKind_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_66_ = stack[0].m_num;
uint8_t v_y_67_ = stack[1].m_num;
uint8_t v_res_73_;
v_res_73_ = l_Lean_Server_instBEqGoToKind_beq(v_x_66_, v_y_67_);
stack->m_num = v_res_73_;
}
LEAN_EXPORT lean_object* l_Lean_Server_instBEqGoToKind_beq___boxed(lean_object* v_x_74_, lean_object* v_y_75_){
_start:
{
uint8_t v_x_24__boxed_76_; uint8_t v_y_25__boxed_77_; uint8_t v_res_78_; lean_object* v_r_79_; 
v_x_24__boxed_76_ = lean_unbox(v_x_74_);
v_y_25__boxed_77_ = lean_unbox(v_y_75_);
v_res_78_ = l_Lean_Server_instBEqGoToKind_beq(v_x_24__boxed_76_, v_y_25__boxed_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
lean_object* l_Lean_Server_instToJsonGoToKind_toJson(uint8_t v_x_91_){
_start:
{
switch(v_x_91_)
{
case 0:
{
lean_object* v___x_92_; 
v___x_92_ = ((lean_object*)(l_Lean_Server_instToJsonGoToKind_toJson___closed__1));
return v___x_92_;
}
case 1:
{
lean_object* v___x_93_; 
v___x_93_ = ((lean_object*)(l_Lean_Server_instToJsonGoToKind_toJson___closed__3));
return v___x_93_;
}
default: 
{
lean_object* v___x_94_; 
v___x_94_ = ((lean_object*)(l_Lean_Server_instToJsonGoToKind_toJson___closed__5));
return v___x_94_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_instToJsonGoToKind_toJson_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_91_ = stack[0].m_num;
lean_object* v_res_95_;
v_res_95_ = l_Lean_Server_instToJsonGoToKind_toJson(v_x_91_);
stack->m_obj
 = v_res_95_;
}
LEAN_EXPORT lean_object* l_Lean_Server_instToJsonGoToKind_toJson___boxed(lean_object* v_x_96_){
_start:
{
uint8_t v_x_67__boxed_97_; lean_object* v_res_98_; 
v_x_67__boxed_97_ = lean_unbox(v_x_96_);
v_res_98_ = l_Lean_Server_instToJsonGoToKind_toJson(v_x_67__boxed_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instFromJsonGoToKind_fromJson(lean_object* v_json_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Json_getTag_x3f(v_json_116_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v___x_118_; 
v___x_118_ = ((lean_object*)(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__1));
return v___x_118_;
}
else
{
lean_object* v_val_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v_val_119_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_val_119_);
lean_dec_ref_known(v___x_117_, 1);
v___x_120_ = ((lean_object*)(l_Lean_Server_instToJsonGoToKind_toJson___closed__4));
v___x_121_ = lean_string_dec_eq(v_val_119_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = ((lean_object*)(l_Lean_Server_instToJsonGoToKind_toJson___closed__0));
v___x_123_ = lean_string_dec_eq(v_val_119_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = ((lean_object*)(l_Lean_Server_instToJsonGoToKind_toJson___closed__2));
v___x_125_ = lean_string_dec_eq(v_val_119_, v___x_124_);
lean_dec(v_val_119_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
v___x_126_ = ((lean_object*)(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__3));
return v___x_126_;
}
else
{
lean_object* v___x_127_; 
v___x_127_ = ((lean_object*)(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__4));
return v___x_127_;
}
}
else
{
lean_object* v___x_128_; 
lean_dec(v_val_119_);
v___x_128_ = ((lean_object*)(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__5));
return v___x_128_;
}
}
else
{
lean_object* v___x_129_; 
lean_dec(v_val_119_);
v___x_129_ = ((lean_object*)(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__6));
return v___x_129_;
}
}
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(lean_object* v_e_132_, lean_object* v___y_133_){
_start:
{
uint8_t v___x_135_; 
v___x_135_ = l_Lean_Expr_hasMVar(v_e_132_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; 
v___x_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_136_, 0, v_e_132_);
return v___x_136_;
}
else
{
lean_object* v___x_137_; lean_object* v_mctx_138_; lean_object* v___x_139_; lean_object* v_fst_140_; lean_object* v_snd_141_; lean_object* v___x_142_; lean_object* v_cache_143_; lean_object* v_zetaDeltaFVarIds_144_; lean_object* v_postponed_145_; lean_object* v_diag_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_155_; 
v___x_137_ = lean_st_ref_get(v___y_133_);
v_mctx_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc_ref(v_mctx_138_);
lean_dec(v___x_137_);
v___x_139_ = l_Lean_instantiateMVarsCore(v_mctx_138_, v_e_132_);
v_fst_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_fst_140_);
v_snd_141_ = lean_ctor_get(v___x_139_, 1);
lean_inc(v_snd_141_);
lean_dec_ref(v___x_139_);
v___x_142_ = lean_st_ref_take(v___y_133_);
v_cache_143_ = lean_ctor_get(v___x_142_, 1);
v_zetaDeltaFVarIds_144_ = lean_ctor_get(v___x_142_, 2);
v_postponed_145_ = lean_ctor_get(v___x_142_, 3);
v_diag_146_ = lean_ctor_get(v___x_142_, 4);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; 
v_unused_156_ = lean_ctor_get(v___x_142_, 0);
lean_dec(v_unused_156_);
v___x_148_ = v___x_142_;
v_isShared_149_ = v_isSharedCheck_155_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_diag_146_);
lean_inc(v_postponed_145_);
lean_inc(v_zetaDeltaFVarIds_144_);
lean_inc(v_cache_143_);
lean_dec(v___x_142_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_155_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v_snd_141_);
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_snd_141_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_cache_143_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_zetaDeltaFVarIds_144_);
lean_ctor_set(v_reuseFailAlloc_154_, 3, v_postponed_145_);
lean_ctor_set(v_reuseFailAlloc_154_, 4, v_diag_146_);
v___x_151_ = v_reuseFailAlloc_154_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_st_ref_put(v___y_133_, v___x_151_);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v_fst_140_);
return v___x_153_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_132_ = stack[0].m_obj;
lean_object* v___y_133_ = stack[1].m_obj;
lean_object* v_res_157_;
v_res_157_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_e_132_, v___y_133_);
stack->m_obj
 = v_res_157_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg___boxed(lean_object* v_e_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_e_158_, v___y_159_);
lean_dec(v___y_159_);
return v_res_161_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0(lean_object* v_e_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_e_162_, v___y_164_);
return v___x_168_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_162_ = stack[0].m_obj;
lean_object* v___y_163_ = stack[1].m_obj;
lean_object* v___y_164_ = stack[2].m_obj;
lean_object* v___y_165_ = stack[3].m_obj;
lean_object* v___y_166_ = stack[4].m_obj;
lean_object* v_res_169_;
v_res_169_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0(v_e_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
stack->m_obj
 = v_res_169_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___boxed(lean_object* v_e_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0(v_e_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
return v_res_176_;
}
}
lean_object* l_Lean_Server_GoToKind_determineTargetExprs___lam__0(lean_object* v_e_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_snd_185_; 
switch(lean_obj_tag(v_e_177_))
{
case 1:
{
lean_object* v___x_190_; 
v___x_190_ = lean_array_push(v___y_178_, v_e_177_);
v_snd_185_ = v___x_190_;
goto v___jp_184_;
}
case 4:
{
lean_object* v___x_191_; 
v___x_191_ = lean_array_push(v___y_178_, v_e_177_);
v_snd_185_ = v___x_191_;
goto v___jp_184_;
}
default: 
{
lean_dec_ref(v_e_177_);
v_snd_185_ = v___y_178_;
goto v___jp_184_;
}
}
v___jp_184_:
{
uint8_t v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_186_ = 1;
v___x_187_ = lean_box(v___x_186_);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v_snd_185_);
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
return v___x_189_;
}
}
}
LEAN_EXPORT void l_Lean_Server_GoToKind_determineTargetExprs___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_177_ = stack[0].m_obj;
lean_object* v___y_178_ = stack[1].m_obj;
lean_object* v___y_179_ = stack[2].m_obj;
lean_object* v___y_180_ = stack[3].m_obj;
lean_object* v___y_181_ = stack[4].m_obj;
lean_object* v___y_182_ = stack[5].m_obj;
lean_object* v_res_192_;
v_res_192_ = l_Lean_Server_GoToKind_determineTargetExprs___lam__0(v_e_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
stack->m_obj
 = v_res_192_;
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_determineTargetExprs___lam__0___boxed(lean_object* v_e_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Server_GoToKind_determineTargetExprs___lam__0(v_e_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(lean_object* v_a_201_, lean_object* v_b_202_, lean_object* v_x_203_){
_start:
{
if (lean_obj_tag(v_x_203_) == 0)
{
lean_dec(v_b_202_);
lean_dec_ref(v_a_201_);
return v_x_203_;
}
else
{
lean_object* v_key_204_; lean_object* v_value_205_; lean_object* v_tail_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_218_; 
v_key_204_ = lean_ctor_get(v_x_203_, 0);
v_value_205_ = lean_ctor_get(v_x_203_, 1);
v_tail_206_ = lean_ctor_get(v_x_203_, 2);
v_isSharedCheck_218_ = !lean_is_exclusive(v_x_203_);
if (v_isSharedCheck_218_ == 0)
{
v___x_208_ = v_x_203_;
v_isShared_209_ = v_isSharedCheck_218_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_tail_206_);
lean_inc(v_value_205_);
lean_inc(v_key_204_);
lean_dec(v_x_203_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_218_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
uint8_t v___x_210_; 
v___x_210_ = lean_expr_eqv(v_key_204_, v_a_201_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(v_a_201_, v_b_202_, v_tail_206_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 2, v___x_211_);
v___x_213_ = v___x_208_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_key_204_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_value_205_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
else
{
lean_object* v___x_216_; 
lean_dec(v_value_205_);
lean_dec(v_key_204_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v_b_202_);
lean_ctor_set(v___x_208_, 0, v_a_201_);
v___x_216_ = v___x_208_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_201_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_b_202_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v_tail_206_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(lean_object* v_a_219_, lean_object* v_x_220_){
_start:
{
if (lean_obj_tag(v_x_220_) == 0)
{
uint8_t v___x_221_; 
v___x_221_ = 0;
return v___x_221_;
}
else
{
lean_object* v_key_222_; lean_object* v_tail_223_; uint8_t v___x_224_; 
v_key_222_ = lean_ctor_get(v_x_220_, 0);
v_tail_223_ = lean_ctor_get(v_x_220_, 2);
v___x_224_ = lean_expr_eqv(v_key_222_, v_a_219_);
if (v___x_224_ == 0)
{
v_x_220_ = v_tail_223_;
goto _start;
}
else
{
return v___x_224_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_219_ = stack[0].m_obj;
lean_object* v_x_220_ = stack[1].m_obj;
uint8_t v_res_226_;
v_res_226_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(v_a_219_, v_x_220_);
stack->m_num = v_res_226_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_227_, lean_object* v_x_228_){
_start:
{
uint8_t v_res_229_; lean_object* v_r_230_; 
v_res_229_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(v_a_227_, v_x_228_);
lean_dec(v_x_228_);
lean_dec_ref(v_a_227_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
if (lean_obj_tag(v_x_232_) == 0)
{
return v_x_231_;
}
else
{
lean_object* v_key_233_; lean_object* v_value_234_; lean_object* v_tail_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_258_; 
v_key_233_ = lean_ctor_get(v_x_232_, 0);
v_value_234_ = lean_ctor_get(v_x_232_, 1);
v_tail_235_ = lean_ctor_get(v_x_232_, 2);
v_isSharedCheck_258_ = !lean_is_exclusive(v_x_232_);
if (v_isSharedCheck_258_ == 0)
{
v___x_237_ = v_x_232_;
v_isShared_238_ = v_isSharedCheck_258_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_tail_235_);
lean_inc(v_value_234_);
lean_inc(v_key_233_);
lean_dec(v_x_232_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_258_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; uint64_t v___x_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v_fold_243_; uint64_t v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; size_t v___x_247_; size_t v___x_248_; size_t v___x_249_; size_t v___x_250_; size_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_239_ = lean_array_get_size(v_x_231_);
v___x_240_ = l_Lean_Expr_hash(v_key_233_);
v___x_241_ = 32ULL;
v___x_242_ = lean_uint64_shift_right(v___x_240_, v___x_241_);
v_fold_243_ = lean_uint64_xor(v___x_240_, v___x_242_);
v___x_244_ = 16ULL;
v___x_245_ = lean_uint64_shift_right(v_fold_243_, v___x_244_);
v___x_246_ = lean_uint64_xor(v_fold_243_, v___x_245_);
v___x_247_ = lean_uint64_to_usize(v___x_246_);
v___x_248_ = lean_usize_of_nat(v___x_239_);
v___x_249_ = ((size_t)1ULL);
v___x_250_ = lean_usize_sub(v___x_248_, v___x_249_);
v___x_251_ = lean_usize_land(v___x_247_, v___x_250_);
v___x_252_ = lean_array_uget_borrowed(v_x_231_, v___x_251_);
lean_inc(v___x_252_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 2, v___x_252_);
v___x_254_ = v___x_237_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_key_233_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_value_234_);
lean_ctor_set(v_reuseFailAlloc_257_, 2, v___x_252_);
v___x_254_ = v_reuseFailAlloc_257_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; 
v___x_255_ = lean_array_uset(v_x_231_, v___x_251_, v___x_254_);
v_x_231_ = v___x_255_;
v_x_232_ = v_tail_235_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6___redArg(lean_object* v_i_259_, lean_object* v_source_260_, lean_object* v_target_261_){
_start:
{
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = lean_array_get_size(v_source_260_);
v___x_263_ = lean_nat_dec_lt(v_i_259_, v___x_262_);
if (v___x_263_ == 0)
{
lean_dec_ref(v_source_260_);
lean_dec(v_i_259_);
return v_target_261_;
}
else
{
lean_object* v_es_264_; lean_object* v___x_265_; lean_object* v_source_266_; lean_object* v_target_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_es_264_ = lean_array_fget(v_source_260_, v_i_259_);
v___x_265_ = lean_box(0);
v_source_266_ = lean_array_fset(v_source_260_, v_i_259_, v___x_265_);
v_target_267_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(v_target_261_, v_es_264_);
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_nat_add(v_i_259_, v___x_268_);
lean_dec(v_i_259_);
v_i_259_ = v___x_269_;
v_source_260_ = v_source_266_;
v_target_261_ = v_target_267_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5___redArg(lean_object* v_data_271_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v_nbuckets_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_272_ = lean_array_get_size(v_data_271_);
v___x_273_ = lean_unsigned_to_nat(2u);
v_nbuckets_274_ = lean_nat_mul(v___x_272_, v___x_273_);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_box(0);
v___x_277_ = lean_mk_array(v_nbuckets_274_, v___x_276_);
v___x_278_ = lean_array_propagate_mark(v_data_271_, v___x_277_);
v___x_279_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6___redArg(v___x_275_, v_data_271_, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2___redArg(lean_object* v_m_280_, lean_object* v_a_281_, lean_object* v_b_282_){
_start:
{
lean_object* v_size_283_; lean_object* v_buckets_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_327_; 
v_size_283_ = lean_ctor_get(v_m_280_, 0);
v_buckets_284_ = lean_ctor_get(v_m_280_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v_m_280_);
if (v_isSharedCheck_327_ == 0)
{
v___x_286_ = v_m_280_;
v_isShared_287_ = v_isSharedCheck_327_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_buckets_284_);
lean_inc(v_size_283_);
lean_dec(v_m_280_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_327_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v_fold_292_; uint64_t v___x_293_; uint64_t v___x_294_; uint64_t v___x_295_; size_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; lean_object* v_bkt_301_; uint8_t v___x_302_; 
v___x_288_ = lean_array_get_size(v_buckets_284_);
v___x_289_ = l_Lean_Expr_hash(v_a_281_);
v___x_290_ = 32ULL;
v___x_291_ = lean_uint64_shift_right(v___x_289_, v___x_290_);
v_fold_292_ = lean_uint64_xor(v___x_289_, v___x_291_);
v___x_293_ = 16ULL;
v___x_294_ = lean_uint64_shift_right(v_fold_292_, v___x_293_);
v___x_295_ = lean_uint64_xor(v_fold_292_, v___x_294_);
v___x_296_ = lean_uint64_to_usize(v___x_295_);
v___x_297_ = lean_usize_of_nat(v___x_288_);
v___x_298_ = ((size_t)1ULL);
v___x_299_ = lean_usize_sub(v___x_297_, v___x_298_);
v___x_300_ = lean_usize_land(v___x_296_, v___x_299_);
v_bkt_301_ = lean_array_uget_borrowed(v_buckets_284_, v___x_300_);
v___x_302_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(v_a_281_, v_bkt_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v_size_x27_304_; lean_object* v___x_305_; lean_object* v_buckets_x27_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_303_ = lean_unsigned_to_nat(1u);
v_size_x27_304_ = lean_nat_add(v_size_283_, v___x_303_);
lean_dec(v_size_283_);
lean_inc(v_bkt_301_);
v___x_305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_305_, 0, v_a_281_);
lean_ctor_set(v___x_305_, 1, v_b_282_);
lean_ctor_set(v___x_305_, 2, v_bkt_301_);
v_buckets_x27_306_ = lean_array_uset(v_buckets_284_, v___x_300_, v___x_305_);
v___x_307_ = lean_unsigned_to_nat(4u);
v___x_308_ = lean_nat_mul(v_size_x27_304_, v___x_307_);
v___x_309_ = lean_unsigned_to_nat(3u);
v___x_310_ = lean_nat_div(v___x_308_, v___x_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_array_get_size(v_buckets_x27_306_);
v___x_312_ = lean_nat_dec_le(v___x_310_, v___x_311_);
lean_dec(v___x_310_);
if (v___x_312_ == 0)
{
lean_object* v_val_313_; lean_object* v___x_315_; 
v_val_313_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5___redArg(v_buckets_x27_306_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 1, v_val_313_);
lean_ctor_set(v___x_286_, 0, v_size_x27_304_);
v___x_315_ = v___x_286_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_size_x27_304_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_val_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
else
{
lean_object* v___x_318_; 
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 1, v_buckets_x27_306_);
lean_ctor_set(v___x_286_, 0, v_size_x27_304_);
v___x_318_ = v___x_286_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_size_x27_304_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_buckets_x27_306_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
else
{
lean_object* v___x_320_; lean_object* v_buckets_x27_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
lean_inc(v_bkt_301_);
v___x_320_ = lean_box(0);
v_buckets_x27_321_ = lean_array_uset(v_buckets_284_, v___x_300_, v___x_320_);
v___x_322_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(v_a_281_, v_b_282_, v_bkt_301_);
v___x_323_ = lean_array_uset(v_buckets_x27_321_, v___x_300_, v___x_322_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 1, v___x_323_);
v___x_325_ = v___x_286_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_size_283_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(lean_object* v_a_328_, lean_object* v_x_329_){
_start:
{
if (lean_obj_tag(v_x_329_) == 0)
{
lean_object* v___x_330_; 
v___x_330_ = lean_box(0);
return v___x_330_;
}
else
{
lean_object* v_key_331_; lean_object* v_value_332_; lean_object* v_tail_333_; uint8_t v___x_334_; 
v_key_331_ = lean_ctor_get(v_x_329_, 0);
v_value_332_ = lean_ctor_get(v_x_329_, 1);
v_tail_333_ = lean_ctor_get(v_x_329_, 2);
v___x_334_ = lean_expr_eqv(v_key_331_, v_a_328_);
if (v___x_334_ == 0)
{
v_x_329_ = v_tail_333_;
goto _start;
}
else
{
lean_object* v___x_336_; 
lean_inc(v_value_332_);
v___x_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_336_, 0, v_value_332_);
return v___x_336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_a_337_, lean_object* v_x_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(v_a_337_, v_x_338_);
lean_dec(v_x_338_);
lean_dec_ref(v_a_337_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(lean_object* v_m_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_buckets_342_; lean_object* v___x_343_; uint64_t v___x_344_; uint64_t v___x_345_; uint64_t v___x_346_; uint64_t v_fold_347_; uint64_t v___x_348_; uint64_t v___x_349_; uint64_t v___x_350_; size_t v___x_351_; size_t v___x_352_; size_t v___x_353_; size_t v___x_354_; size_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_buckets_342_ = lean_ctor_get(v_m_340_, 1);
v___x_343_ = lean_array_get_size(v_buckets_342_);
v___x_344_ = l_Lean_Expr_hash(v_a_341_);
v___x_345_ = 32ULL;
v___x_346_ = lean_uint64_shift_right(v___x_344_, v___x_345_);
v_fold_347_ = lean_uint64_xor(v___x_344_, v___x_346_);
v___x_348_ = 16ULL;
v___x_349_ = lean_uint64_shift_right(v_fold_347_, v___x_348_);
v___x_350_ = lean_uint64_xor(v_fold_347_, v___x_349_);
v___x_351_ = lean_uint64_to_usize(v___x_350_);
v___x_352_ = lean_usize_of_nat(v___x_343_);
v___x_353_ = ((size_t)1ULL);
v___x_354_ = lean_usize_sub(v___x_352_, v___x_353_);
v___x_355_ = lean_usize_land(v___x_351_, v___x_354_);
v___x_356_ = lean_array_uget_borrowed(v_buckets_342_, v___x_355_);
v___x_357_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(v_a_341_, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg___boxed(lean_object* v_m_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(v_m_358_, v_a_359_);
lean_dec_ref(v_a_359_);
lean_dec_ref(v_m_358_);
return v_res_360_;
}
}
lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(lean_object* v_g_361_, lean_object* v_e_362_, lean_object* v_a_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_a_371_; lean_object* v_fst_372_; lean_object* v___y_378_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_st_ref_get(v_a_363_);
v___x_382_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(v___x_381_, v_e_362_);
lean_dec(v___x_381_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v___x_383_; 
lean_inc_ref(v_g_361_);
lean_inc(v___y_368_);
lean_inc_ref(v___y_367_);
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
lean_inc_ref(v_e_362_);
v___x_383_ = lean_apply_7(v_g_361_, v_e_362_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, lean_box(0));
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v_fst_385_; lean_object* v_snd_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_431_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref_known(v___x_383_, 1);
v_fst_385_ = lean_ctor_get(v_a_384_, 0);
v_snd_386_ = lean_ctor_get(v_a_384_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_a_384_);
if (v_isSharedCheck_431_ == 0)
{
v___x_388_ = v_a_384_;
v_isShared_389_ = v_isSharedCheck_431_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_snd_386_);
lean_inc(v_fst_385_);
lean_dec(v_a_384_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_431_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v_d_391_; lean_object* v_b_392_; lean_object* v___y_393_; uint8_t v___x_398_; 
v___x_398_ = lean_unbox(v_fst_385_);
lean_dec(v_fst_385_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; lean_object* v___x_401_; 
lean_dec_ref(v_g_361_);
v___x_399_ = lean_box(0);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_399_);
v___x_401_ = v___x_388_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_snd_386_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
v_a_371_ = v___x_401_;
v_fst_372_ = v___x_399_;
goto v___jp_370_;
}
}
else
{
switch(lean_obj_tag(v_e_362_))
{
case 7:
{
lean_object* v_binderType_403_; lean_object* v_body_404_; 
lean_del_object(v___x_388_);
v_binderType_403_ = lean_ctor_get(v_e_362_, 1);
v_body_404_ = lean_ctor_get(v_e_362_, 2);
lean_inc_ref(v_body_404_);
lean_inc_ref(v_binderType_403_);
v_d_391_ = v_binderType_403_;
v_b_392_ = v_body_404_;
v___y_393_ = v_a_363_;
goto v___jp_390_;
}
case 6:
{
lean_object* v_binderType_405_; lean_object* v_body_406_; 
lean_del_object(v___x_388_);
v_binderType_405_ = lean_ctor_get(v_e_362_, 1);
v_body_406_ = lean_ctor_get(v_e_362_, 2);
lean_inc_ref(v_body_406_);
lean_inc_ref(v_binderType_405_);
v_d_391_ = v_binderType_405_;
v_b_392_ = v_body_406_;
v___y_393_ = v_a_363_;
goto v___jp_390_;
}
case 8:
{
lean_object* v_type_407_; lean_object* v_value_408_; lean_object* v_body_409_; lean_object* v___x_410_; 
lean_del_object(v___x_388_);
v_type_407_ = lean_ctor_get(v_e_362_, 1);
v_value_408_ = lean_ctor_get(v_e_362_, 2);
v_body_409_ = lean_ctor_get(v_e_362_, 3);
lean_inc_ref(v_type_407_);
lean_inc_ref(v_g_361_);
v___x_410_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_361_, v_type_407_, v_a_363_, v_snd_386_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v_snd_412_; lean_object* v___x_413_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_410_, 1);
v_snd_412_ = lean_ctor_get(v_a_411_, 1);
lean_inc(v_snd_412_);
lean_dec(v_a_411_);
lean_inc_ref(v_value_408_);
lean_inc_ref(v_g_361_);
v___x_413_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_361_, v_value_408_, v_a_363_, v_snd_412_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v_snd_415_; lean_object* v___x_416_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
v_snd_415_ = lean_ctor_get(v_a_414_, 1);
lean_inc(v_snd_415_);
lean_dec(v_a_414_);
lean_inc_ref(v_body_409_);
v___x_416_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_361_, v_body_409_, v_a_363_, v_snd_415_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
v___y_378_ = v___x_416_;
goto v___jp_377_;
}
else
{
lean_dec_ref(v_g_361_);
v___y_378_ = v___x_413_;
goto v___jp_377_;
}
}
else
{
lean_dec_ref(v_g_361_);
v___y_378_ = v___x_410_;
goto v___jp_377_;
}
}
case 5:
{
lean_object* v_fn_417_; lean_object* v_arg_418_; lean_object* v___x_419_; 
lean_del_object(v___x_388_);
v_fn_417_ = lean_ctor_get(v_e_362_, 0);
v_arg_418_ = lean_ctor_get(v_e_362_, 1);
lean_inc_ref(v_fn_417_);
lean_inc_ref(v_g_361_);
v___x_419_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_361_, v_fn_417_, v_a_363_, v_snd_386_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v_snd_421_; lean_object* v___x_422_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
lean_dec_ref_known(v___x_419_, 1);
v_snd_421_ = lean_ctor_get(v_a_420_, 1);
lean_inc(v_snd_421_);
lean_dec(v_a_420_);
lean_inc_ref(v_arg_418_);
v___x_422_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_361_, v_arg_418_, v_a_363_, v_snd_421_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
v___y_378_ = v___x_422_;
goto v___jp_377_;
}
else
{
lean_dec_ref(v_g_361_);
v___y_378_ = v___x_419_;
goto v___jp_377_;
}
}
case 10:
{
lean_object* v_expr_423_; lean_object* v___x_424_; 
lean_del_object(v___x_388_);
v_expr_423_ = lean_ctor_get(v_e_362_, 1);
lean_inc_ref(v_expr_423_);
v___x_424_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_361_, v_expr_423_, v_a_363_, v_snd_386_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
v___y_378_ = v___x_424_;
goto v___jp_377_;
}
case 11:
{
lean_object* v_struct_425_; lean_object* v___x_426_; 
lean_del_object(v___x_388_);
v_struct_425_ = lean_ctor_get(v_e_362_, 2);
lean_inc_ref(v_struct_425_);
v___x_426_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_361_, v_struct_425_, v_a_363_, v_snd_386_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
v___y_378_ = v___x_426_;
goto v___jp_377_;
}
default: 
{
lean_object* v___x_427_; lean_object* v___x_429_; 
lean_dec_ref(v_g_361_);
v___x_427_ = lean_box(0);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_427_);
v___x_429_ = v___x_388_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_snd_386_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
v_a_371_ = v___x_429_;
v_fst_372_ = v___x_427_;
goto v___jp_370_;
}
}
}
}
v___jp_390_:
{
lean_object* v___x_394_; 
lean_inc_ref(v_g_361_);
v___x_394_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_361_, v_d_391_, v___y_393_, v_snd_386_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v_snd_396_; lean_object* v___x_397_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 1);
v_snd_396_ = lean_ctor_get(v_a_395_, 1);
lean_inc(v_snd_396_);
lean_dec(v_a_395_);
v___x_397_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_361_, v_b_392_, v___y_393_, v_snd_396_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
v___y_378_ = v___x_397_;
goto v___jp_377_;
}
else
{
lean_dec_ref(v_b_392_);
lean_dec_ref(v_g_361_);
v___y_378_ = v___x_394_;
goto v___jp_377_;
}
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_dec_ref(v_e_362_);
lean_dec_ref(v_g_361_);
v_a_432_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_383_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_383_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
else
{
lean_object* v_val_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_448_; 
lean_dec_ref(v_e_362_);
lean_dec_ref(v_g_361_);
v_val_440_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_448_ == 0)
{
v___x_442_ = v___x_382_;
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_val_440_);
lean_dec(v___x_382_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v_val_440_);
lean_ctor_set(v___x_444_, 1, v___y_364_);
if (v_isShared_443_ == 0)
{
lean_ctor_set_tag(v___x_442_, 0);
lean_ctor_set(v___x_442_, 0, v___x_444_);
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
v___jp_370_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_373_ = lean_st_ref_take(v_a_363_);
v___x_374_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2___redArg(v___x_373_, v_e_362_, v_fst_372_);
v___x_375_ = lean_st_ref_put(v_a_363_, v___x_374_);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v_a_371_);
return v___x_376_;
}
v___jp_377_:
{
if (lean_obj_tag(v___y_378_) == 0)
{
lean_object* v_a_379_; lean_object* v_fst_380_; 
v_a_379_ = lean_ctor_get(v___y_378_, 0);
lean_inc(v_a_379_);
lean_dec_ref_known(v___y_378_, 1);
v_fst_380_ = lean_ctor_get(v_a_379_, 0);
lean_inc(v_fst_380_);
v_a_371_ = v_a_379_;
v_fst_372_ = v_fst_380_;
goto v___jp_370_;
}
else
{
lean_dec_ref(v_e_362_);
return v___y_378_;
}
}
}
}
LEAN_EXPORT void l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_361_ = stack[0].m_obj;
lean_object* v_e_362_ = stack[1].m_obj;
lean_object* v_a_363_ = stack[2].m_obj;
lean_object* v___y_364_ = stack[3].m_obj;
lean_object* v___y_365_ = stack[4].m_obj;
lean_object* v___y_366_ = stack[5].m_obj;
lean_object* v___y_367_ = stack[6].m_obj;
lean_object* v___y_368_ = stack[7].m_obj;
lean_object* v_res_449_;
v_res_449_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_361_, v_e_362_, v_a_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
stack->m_obj
 = v_res_449_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1___boxed(lean_object* v_g_450_, lean_object* v_e_451_, lean_object* v_a_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_450_, v_e_451_, v_a_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v_a_452_);
return v_res_459_;
}
}
static lean_object* _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__1(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_box(0);
v___x_462_ = lean_unsigned_to_nat(16u);
v___x_463_ = lean_mk_array(v___x_462_, v___x_461_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__2(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_464_ = lean_obj_once(&l_Lean_Server_GoToKind_determineTargetExprs___closed__1, &l_Lean_Server_GoToKind_determineTargetExprs___closed__1_once, _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__1);
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v___x_464_);
return v___x_466_;
}
}
lean_object* l_Lean_Server_GoToKind_determineTargetExprs(uint8_t v_kind_469_, lean_object* v_ti_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
if (v_kind_469_ == 2)
{
lean_object* v_expr_476_; lean_object* v___f_477_; lean_object* v___x_478_; 
v_expr_476_ = lean_ctor_get(v_ti_470_, 3);
lean_inc_ref(v_expr_476_);
lean_dec_ref(v_ti_470_);
v___f_477_ = ((lean_object*)(l_Lean_Server_GoToKind_determineTargetExprs___closed__0));
lean_inc(v_a_474_);
lean_inc_ref(v_a_473_);
lean_inc(v_a_472_);
lean_inc_ref(v_a_471_);
v___x_478_ = lean_infer_type(v_expr_476_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_480_; lean_object* v_a_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
v___x_480_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_a_479_, v_a_472_);
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
lean_dec_ref(v___x_480_);
v___x_482_ = lean_obj_once(&l_Lean_Server_GoToKind_determineTargetExprs___closed__2, &l_Lean_Server_GoToKind_determineTargetExprs___closed__2_once, _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__2);
v___x_483_ = ((lean_object*)(l_Lean_Server_GoToKind_determineTargetExprs___closed__3));
v___x_484_ = lean_st_mk_ref(v___x_482_);
v___x_485_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v___f_477_, v_a_481_, v___x_484_, v___x_483_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_495_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_495_ == 0)
{
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_495_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_495_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v_snd_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
v_snd_490_ = lean_ctor_get(v_a_486_, 1);
lean_inc(v_snd_490_);
lean_dec(v_a_486_);
v___x_491_ = lean_st_ref_get(v___x_484_);
lean_dec(v___x_484_);
lean_dec(v___x_491_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v_snd_490_);
v___x_493_ = v___x_488_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_snd_490_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec(v___x_484_);
v_a_496_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_485_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_485_);
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
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
v_a_504_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_478_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_478_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
else
{
lean_object* v_expr_512_; lean_object* v___x_513_; lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_524_; 
v_expr_512_ = lean_ctor_get(v_ti_470_, 3);
lean_inc_ref(v_expr_512_);
lean_dec_ref(v_ti_470_);
v___x_513_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_expr_512_, v_a_472_);
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_524_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_524_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_524_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_mk_empty_array_with_capacity(v___x_518_);
v___x_520_ = lean_array_push(v___x_519_, v_a_514_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_520_);
v___x_522_ = v___x_516_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_GoToKind_determineTargetExprs_0interp(lean_interpreter_value* stack)
{
uint8_t v_kind_469_ = stack[0].m_num;
lean_object* v_ti_470_ = stack[1].m_obj;
lean_object* v_a_471_ = stack[2].m_obj;
lean_object* v_a_472_ = stack[3].m_obj;
lean_object* v_a_473_ = stack[4].m_obj;
lean_object* v_a_474_ = stack[5].m_obj;
lean_object* v_res_525_;
v_res_525_ = l_Lean_Server_GoToKind_determineTargetExprs(v_kind_469_, v_ti_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
stack->m_obj
 = v_res_525_;
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToKind_determineTargetExprs___boxed(lean_object* v_kind_526_, lean_object* v_ti_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
uint8_t v_kind_boxed_533_; lean_object* v_res_534_; 
v_kind_boxed_533_ = lean_unbox(v_kind_526_);
v_res_534_ = l_Lean_Server_GoToKind_determineTargetExprs(v_kind_boxed_533_, v_ti_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
lean_dec(v_a_531_);
lean_dec_ref(v_a_530_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_528_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1(lean_object* v_00_u03b2_535_, lean_object* v_m_536_, lean_object* v_a_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(v_m_536_, v_a_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___boxed(lean_object* v_00_u03b2_539_, lean_object* v_m_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1(v_00_u03b2_539_, v_m_540_, v_a_541_);
lean_dec_ref(v_a_541_);
lean_dec_ref(v_m_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2(lean_object* v_00_u03b2_543_, lean_object* v_m_544_, lean_object* v_a_545_, lean_object* v_b_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2___redArg(v_m_544_, v_a_545_, v_b_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_548_, lean_object* v_a_549_, lean_object* v_x_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(v_a_549_, v_x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_552_, lean_object* v_a_553_, lean_object* v_x_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2(v_00_u03b2_552_, v_a_553_, v_x_554_);
lean_dec(v_x_554_);
lean_dec_ref(v_a_553_);
return v_res_555_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_556_, lean_object* v_a_557_, lean_object* v_x_558_){
_start:
{
uint8_t v___x_559_; 
v___x_559_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(v_a_557_, v_x_558_);
return v___x_559_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_557_ = stack[1].m_obj;
lean_object* v_x_558_ = stack[2].m_obj;
uint8_t v_res_560_;
v_res_560_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4(lean_box(0), v_a_557_, v_x_558_);
stack->m_num = v_res_560_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_561_, lean_object* v_a_562_, lean_object* v_x_563_){
_start:
{
uint8_t v_res_564_; lean_object* v_r_565_; 
v_res_564_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4(v_00_u03b2_561_, v_a_562_, v_x_563_);
lean_dec(v_x_563_);
lean_dec_ref(v_a_562_);
v_r_565_ = lean_box(v_res_564_);
return v_r_565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_566_, lean_object* v_data_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5___redArg(v_data_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_569_, lean_object* v_a_570_, lean_object* v_b_571_, lean_object* v_x_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(v_a_570_, v_b_571_, v_x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_574_, lean_object* v_i_575_, lean_object* v_source_576_, lean_object* v_target_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6___redArg(v_i_575_, v_source_576_, v_target_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_579_, lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(v_x_580_, v_x_581_);
return v___x_582_;
}
}
lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(lean_object* v_e_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_st_ref_get(v_a_587_);
v___x_590_ = l_Lean_Expr_getAppFn_x27(v_e_583_);
if (lean_obj_tag(v___x_590_) == 4)
{
lean_object* v_declName_591_; lean_object* v_env_592_; lean_object* v___x_593_; 
v_declName_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_declName_591_);
lean_dec_ref_known(v___x_590_, 2);
v_env_592_ = lean_ctor_get(v___x_589_, 0);
lean_inc_ref(v_env_592_);
lean_dec(v___x_589_);
v___x_593_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_592_, v_declName_591_);
if (lean_obj_tag(v___x_593_) == 1)
{
lean_object* v_val_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_603_; 
v_val_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_603_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_603_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_val_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_603_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_e_583_);
lean_ctor_set(v___x_598_, 1, v_val_594_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_598_);
v___x_600_ = v___x_596_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_602_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
}
}
else
{
uint8_t v___x_604_; lean_object* v___x_605_; 
lean_dec(v___x_593_);
v___x_604_ = 0;
v___x_605_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_583_, v___x_604_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_616_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_616_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_616_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_616_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
if (lean_obj_tag(v_a_606_) == 1)
{
lean_object* v_val_610_; 
lean_del_object(v___x_608_);
v_val_610_ = lean_ctor_get(v_a_606_, 0);
lean_inc(v_val_610_);
lean_dec_ref_known(v_a_606_, 1);
v_e_583_ = v_val_610_;
goto _start;
}
else
{
lean_object* v___x_612_; lean_object* v___x_614_; 
lean_dec(v_a_606_);
v___x_612_ = lean_box(0);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_612_);
v___x_614_ = v___x_608_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
v_a_617_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_605_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_605_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec_ref(v___x_590_);
lean_dec(v___x_589_);
lean_dec_ref(v_e_583_);
v___x_625_ = lean_box(0);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_583_ = stack[0].m_obj;
lean_object* v_a_584_ = stack[1].m_obj;
lean_object* v_a_585_ = stack[2].m_obj;
lean_object* v_a_586_ = stack[3].m_obj;
lean_object* v_a_587_ = stack[4].m_obj;
lean_object* v_res_627_;
v_res_627_ = l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(v_e_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
stack->m_obj
 = v_res_627_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f___boxed(lean_object* v_e_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(v_e_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
return v_res_634_;
}
}
static lean_object* _init_l_Lean_Server_getInstanceProjectionArg_x3f___closed__0(void){
_start:
{
lean_object* v___x_635_; lean_object* v_dummy_636_; 
v___x_635_ = lean_box(0);
v_dummy_636_ = l_Lean_Expr_sort___override(v___x_635_);
return v_dummy_636_;
}
}
lean_object* l_Lean_Server_getInstanceProjectionArg_x3f(lean_object* v_e_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v___y_644_; lean_object* v___x_689_; uint8_t v_transparency_690_; uint8_t v___x_691_; uint8_t v___x_692_; 
v___x_689_ = l_Lean_Meta_Context_config(v_a_638_);
v_transparency_690_ = lean_ctor_get_uint8(v___x_689_, 9);
lean_dec_ref(v___x_689_);
v___x_691_ = 2;
v___x_692_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_690_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v_keyedConfig_693_; uint8_t v_trackZetaDelta_694_; lean_object* v_zetaDeltaSet_695_; lean_object* v_lctx_696_; lean_object* v_localInstances_697_; lean_object* v_defEqCtx_x3f_698_; lean_object* v_synthPendingDepth_699_; lean_object* v_customCanUnfoldPredicate_x3f_700_; uint8_t v_univApprox_701_; uint8_t v_inTypeClassResolution_702_; uint8_t v_cacheInferType_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_keyedConfig_693_ = lean_ctor_get(v_a_638_, 0);
v_trackZetaDelta_694_ = lean_ctor_get_uint8(v_a_638_, sizeof(void*)*7);
v_zetaDeltaSet_695_ = lean_ctor_get(v_a_638_, 1);
v_lctx_696_ = lean_ctor_get(v_a_638_, 2);
v_localInstances_697_ = lean_ctor_get(v_a_638_, 3);
v_defEqCtx_x3f_698_ = lean_ctor_get(v_a_638_, 4);
v_synthPendingDepth_699_ = lean_ctor_get(v_a_638_, 5);
v_customCanUnfoldPredicate_x3f_700_ = lean_ctor_get(v_a_638_, 6);
v_univApprox_701_ = lean_ctor_get_uint8(v_a_638_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_702_ = lean_ctor_get_uint8(v_a_638_, sizeof(void*)*7 + 2);
v_cacheInferType_703_ = lean_ctor_get_uint8(v_a_638_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_693_);
v___x_704_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_691_, v_keyedConfig_693_);
lean_inc(v_customCanUnfoldPredicate_x3f_700_);
lean_inc(v_synthPendingDepth_699_);
lean_inc(v_defEqCtx_x3f_698_);
lean_inc_ref(v_localInstances_697_);
lean_inc_ref(v_lctx_696_);
lean_inc(v_zetaDeltaSet_695_);
v___x_705_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v_zetaDeltaSet_695_);
lean_ctor_set(v___x_705_, 2, v_lctx_696_);
lean_ctor_set(v___x_705_, 3, v_localInstances_697_);
lean_ctor_set(v___x_705_, 4, v_defEqCtx_x3f_698_);
lean_ctor_set(v___x_705_, 5, v_synthPendingDepth_699_);
lean_ctor_set(v___x_705_, 6, v_customCanUnfoldPredicate_x3f_700_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*7, v_trackZetaDelta_694_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*7 + 1, v_univApprox_701_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*7 + 2, v_inTypeClassResolution_702_);
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*7 + 3, v_cacheInferType_703_);
v___x_706_ = l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(v_e_637_, v___x_705_, v_a_639_, v_a_640_, v_a_641_);
lean_dec_ref_known(v___x_705_, 7);
v___y_644_ = v___x_706_;
goto v___jp_643_;
}
else
{
lean_object* v___x_707_; 
v___x_707_ = l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(v_e_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
v___y_644_ = v___x_707_;
goto v___jp_643_;
}
v___jp_643_:
{
if (lean_obj_tag(v___y_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_680_; 
v_a_645_ = lean_ctor_get(v___y_644_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___y_644_);
if (v_isSharedCheck_680_ == 0)
{
v___x_647_ = v___y_644_;
v_isShared_648_ = v_isSharedCheck_680_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___y_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_680_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
if (lean_obj_tag(v_a_645_) == 1)
{
lean_object* v_val_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_675_; 
v_val_649_ = lean_ctor_get(v_a_645_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v_a_645_);
if (v_isSharedCheck_675_ == 0)
{
v___x_651_ = v_a_645_;
v_isShared_652_ = v_isSharedCheck_675_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_val_649_);
lean_dec(v_a_645_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_675_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v_snd_653_; lean_object* v_fst_654_; lean_object* v_numParams_655_; lean_object* v_dummy_656_; lean_object* v_nargs_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v_snd_653_ = lean_ctor_get(v_val_649_, 1);
lean_inc(v_snd_653_);
v_fst_654_ = lean_ctor_get(v_val_649_, 0);
lean_inc(v_fst_654_);
lean_dec(v_val_649_);
v_numParams_655_ = lean_ctor_get(v_snd_653_, 1);
lean_inc(v_numParams_655_);
lean_dec(v_snd_653_);
v_dummy_656_ = lean_obj_once(&l_Lean_Server_getInstanceProjectionArg_x3f___closed__0, &l_Lean_Server_getInstanceProjectionArg_x3f___closed__0_once, _init_l_Lean_Server_getInstanceProjectionArg_x3f___closed__0);
v_nargs_657_ = l_Lean_Expr_getAppNumArgs(v_fst_654_);
lean_inc(v_nargs_657_);
v___x_658_ = lean_mk_array(v_nargs_657_, v_dummy_656_);
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = lean_nat_sub(v_nargs_657_, v___x_659_);
lean_dec(v_nargs_657_);
v___x_661_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_654_, v___x_658_, v___x_660_);
v___x_662_ = lean_array_get_size(v___x_661_);
v___x_663_ = lean_nat_dec_lt(v_numParams_655_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_666_; 
lean_dec_ref(v___x_661_);
lean_dec(v_numParams_655_);
lean_del_object(v___x_651_);
v___x_664_ = lean_box(0);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_664_);
v___x_666_ = v___x_647_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
else
{
lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_668_ = lean_array_fget(v___x_661_, v_numParams_655_);
lean_dec(v_numParams_655_);
lean_dec_ref(v___x_661_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_668_);
v___x_670_ = v___x_651_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_674_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_672_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_670_);
v___x_672_ = v___x_647_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
else
{
lean_object* v___x_676_; lean_object* v___x_678_; 
lean_dec(v_a_645_);
v___x_676_ = lean_box(0);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_676_);
v___x_678_ = v___x_647_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
v_a_681_ = lean_ctor_get(v___y_644_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___y_644_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___y_644_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___y_644_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_getInstanceProjectionArg_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_637_ = stack[0].m_obj;
lean_object* v_a_638_ = stack[1].m_obj;
lean_object* v_a_639_ = stack[2].m_obj;
lean_object* v_a_640_ = stack[3].m_obj;
lean_object* v_a_641_ = stack[4].m_obj;
lean_object* v_res_708_;
v_res_708_ = l_Lean_Server_getInstanceProjectionArg_x3f(v_e_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
stack->m_obj
 = v_res_708_;
}
LEAN_EXPORT lean_object* l_Lean_Server_getInstanceProjectionArg_x3f___boxed(lean_object* v_e_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Server_getInstanceProjectionArg_x3f(v_e_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
return v_res_715_;
}
}
lean_object* l_Lean_Server_isInstanceProjection(lean_object* v_e_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Server_getInstanceProjectionArg_x3f(v_e_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_737_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_737_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_737_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_737_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
if (lean_obj_tag(v_a_723_) == 0)
{
uint8_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_727_ = 0;
v___x_728_ = lean_box(v___x_727_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_728_);
v___x_730_ = v___x_725_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
else
{
uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
lean_dec_ref_known(v_a_723_, 1);
v___x_732_ = 1;
v___x_733_ = lean_box(v___x_732_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_733_);
v___x_735_ = v___x_725_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
v_a_738_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_722_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_722_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_isInstanceProjection_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_716_ = stack[0].m_obj;
lean_object* v_a_717_ = stack[1].m_obj;
lean_object* v_a_718_ = stack[2].m_obj;
lean_object* v_a_719_ = stack[3].m_obj;
lean_object* v_a_720_ = stack[4].m_obj;
lean_object* v_res_746_;
v_res_746_ = l_Lean_Server_isInstanceProjection(v_e_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
stack->m_obj
 = v_res_746_;
}
LEAN_EXPORT lean_object* l_Lean_Server_isInstanceProjection___boxed(lean_object* v_e_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Server_isInstanceProjection(v_e_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
return v_res_753_;
}
}
lean_object* l_Lean_Server_isInstanceProjectionInfoFor(uint8_t v_kind_754_, lean_object* v_ti1_755_, lean_object* v_ti2_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
uint8_t v___x_762_; uint8_t v___x_763_; 
v___x_762_ = 2;
v___x_763_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_754_, v___x_762_);
if (v___x_763_ == 0)
{
lean_object* v_toElabInfo_764_; lean_object* v_expr_765_; lean_object* v_stx_766_; uint8_t v___x_767_; lean_object* v___x_768_; 
v_toElabInfo_764_ = lean_ctor_get(v_ti1_755_, 0);
lean_inc_ref(v_toElabInfo_764_);
v_expr_765_ = lean_ctor_get(v_ti1_755_, 3);
lean_inc_ref(v_expr_765_);
lean_dec_ref(v_ti1_755_);
v_stx_766_ = lean_ctor_get(v_toElabInfo_764_, 1);
lean_inc(v_stx_766_);
lean_dec_ref(v_toElabInfo_764_);
v___x_767_ = 1;
v___x_768_ = l_Lean_Syntax_getPos_x3f(v_stx_766_, v___x_767_);
lean_dec(v_stx_766_);
if (lean_obj_tag(v___x_768_) == 1)
{
lean_object* v_toElabInfo_769_; lean_object* v_val_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_838_; 
v_toElabInfo_769_ = lean_ctor_get(v_ti2_756_, 0);
lean_inc_ref(v_toElabInfo_769_);
v_val_770_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_838_ == 0)
{
v___x_772_ = v___x_768_;
v_isShared_773_ = v_isSharedCheck_838_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_val_770_);
lean_dec(v___x_768_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_838_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_expr_774_; lean_object* v_stx_775_; lean_object* v___x_776_; 
v_expr_774_ = lean_ctor_get(v_ti2_756_, 3);
lean_inc_ref(v_expr_774_);
lean_dec_ref(v_ti2_756_);
v_stx_775_ = lean_ctor_get(v_toElabInfo_769_, 1);
lean_inc(v_stx_775_);
lean_dec_ref(v_toElabInfo_769_);
v___x_776_ = l_Lean_Syntax_getPos_x3f(v_stx_775_, v___x_767_);
lean_dec(v_stx_775_);
if (lean_obj_tag(v___x_776_) == 1)
{
lean_object* v_val_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_833_; 
lean_del_object(v___x_772_);
v_val_777_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_833_ == 0)
{
v___x_779_ = v___x_776_;
v_isShared_780_ = v_isSharedCheck_833_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_val_777_);
lean_dec(v___x_776_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_833_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
uint8_t v_decide_781_; 
v_decide_781_ = lean_nat_dec_eq(v_val_770_, v_val_777_);
lean_dec(v_val_777_);
lean_dec(v_val_770_);
if (v_decide_781_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_784_; 
lean_dec_ref(v_expr_774_);
lean_dec_ref(v_expr_765_);
v___x_782_ = lean_box(v___x_763_);
if (v_isShared_780_ == 0)
{
lean_ctor_set_tag(v___x_779_, 0);
lean_ctor_set(v___x_779_, 0, v___x_782_);
v___x_784_ = v___x_779_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
else
{
if (v___x_763_ == 0)
{
lean_object* v___x_786_; lean_object* v_a_787_; lean_object* v___x_788_; lean_object* v_a_789_; lean_object* v___x_790_; 
lean_del_object(v___x_779_);
v___x_786_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_expr_765_, v_a_758_);
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc_n(v_a_787_, 2);
lean_dec_ref(v___x_786_);
v___x_788_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_expr_774_, v_a_758_);
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref(v___x_788_);
v___x_790_ = l_Lean_Server_isInstanceProjection(v_a_787_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_792_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref_known(v___x_790_, 1);
lean_inc(v_a_789_);
v___x_792_ = l_Lean_Server_isInstanceProjection(v_a_789_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_792_) == 0)
{
uint8_t v___x_793_; 
v___x_793_ = lean_unbox(v_a_791_);
lean_dec(v_a_791_);
if (v___x_793_ == 0)
{
lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_801_; 
lean_dec(v_a_789_);
lean_dec(v_a_787_);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; 
v_unused_802_ = lean_ctor_get(v___x_792_, 0);
lean_dec(v_unused_802_);
v___x_795_ = v___x_792_;
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
else
{
lean_dec(v___x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_box(v___x_763_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
else
{
if (v___x_763_ == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_819_; 
v_a_803_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_819_ == 0)
{
v___x_805_ = v___x_792_;
v_isShared_806_ = v_isSharedCheck_819_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_792_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_819_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
uint8_t v___x_807_; 
v___x_807_ = lean_unbox(v_a_803_);
lean_dec(v_a_803_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_808_ = l_Lean_Expr_getAppFn_x27(v_a_787_);
lean_dec(v_a_787_);
v___x_809_ = l_Lean_Expr_getAppFn_x27(v_a_789_);
lean_dec(v_a_789_);
v___x_810_ = lean_expr_eqv(v___x_808_, v___x_809_);
lean_dec_ref(v___x_809_);
lean_dec_ref(v___x_808_);
v___x_811_ = lean_box(v___x_810_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_811_);
v___x_813_ = v___x_805_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
else
{
lean_object* v___x_815_; lean_object* v___x_817_; 
lean_dec(v_a_789_);
lean_dec(v_a_787_);
v___x_815_ = lean_box(v___x_763_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_815_);
v___x_817_ = v___x_805_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
else
{
lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_827_; 
lean_dec(v_a_789_);
lean_dec(v_a_787_);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v___x_792_, 0);
lean_dec(v_unused_828_);
v___x_821_ = v___x_792_;
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
else
{
lean_dec(v___x_792_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_823_ = lean_box(v___x_763_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_823_);
v___x_825_ = v___x_821_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
else
{
lean_dec(v_a_791_);
lean_dec(v_a_789_);
lean_dec(v_a_787_);
return v___x_792_;
}
}
else
{
lean_dec(v_a_789_);
lean_dec(v_a_787_);
return v___x_790_;
}
}
else
{
lean_object* v___x_829_; lean_object* v___x_831_; 
lean_dec_ref(v_expr_774_);
lean_dec_ref(v_expr_765_);
v___x_829_ = lean_box(v___x_763_);
if (v_isShared_780_ == 0)
{
lean_ctor_set_tag(v___x_779_, 0);
lean_ctor_set(v___x_779_, 0, v___x_829_);
v___x_831_ = v___x_779_;
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
}
}
}
else
{
lean_object* v___x_834_; lean_object* v___x_836_; 
lean_dec(v___x_776_);
lean_dec_ref(v_expr_774_);
lean_dec(v_val_770_);
lean_dec_ref(v_expr_765_);
v___x_834_ = lean_box(v___x_763_);
if (v_isShared_773_ == 0)
{
lean_ctor_set_tag(v___x_772_, 0);
lean_ctor_set(v___x_772_, 0, v___x_834_);
v___x_836_ = v___x_772_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec(v___x_768_);
lean_dec_ref(v_expr_765_);
lean_dec_ref(v_ti2_756_);
v___x_839_ = lean_box(v___x_763_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
}
else
{
uint8_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec_ref(v_ti2_756_);
lean_dec_ref(v_ti1_755_);
v___x_841_ = 0;
v___x_842_ = lean_box(v___x_841_);
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
return v___x_843_;
}
}
}
LEAN_EXPORT void l_Lean_Server_isInstanceProjectionInfoFor_0interp(lean_interpreter_value* stack)
{
uint8_t v_kind_754_ = stack[0].m_num;
lean_object* v_ti1_755_ = stack[1].m_obj;
lean_object* v_ti2_756_ = stack[2].m_obj;
lean_object* v_a_757_ = stack[3].m_obj;
lean_object* v_a_758_ = stack[4].m_obj;
lean_object* v_a_759_ = stack[5].m_obj;
lean_object* v_a_760_ = stack[6].m_obj;
lean_object* v_res_844_;
v_res_844_ = l_Lean_Server_isInstanceProjectionInfoFor(v_kind_754_, v_ti1_755_, v_ti2_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
stack->m_obj
 = v_res_844_;
}
LEAN_EXPORT lean_object* l_Lean_Server_isInstanceProjectionInfoFor___boxed(lean_object* v_kind_845_, lean_object* v_ti1_846_, lean_object* v_ti2_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
uint8_t v_kind_boxed_853_; lean_object* v_res_854_; 
v_kind_boxed_853_ = lean_unbox(v_kind_845_);
v_res_854_ = l_Lean_Server_isInstanceProjectionInfoFor(v_kind_boxed_853_, v_ti1_846_, v_ti2_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
return v_res_854_;
}
}
lean_object* l_Lean_Server_GoToM_run___redArg(lean_object* v_ctx_855_, lean_object* v_ci_856_, lean_object* v_lctx_857_, lean_object* v_act_858_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_apply_1(v_act_858_, v_ctx_855_);
v___x_861_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ci_856_, v_lctx_857_, v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT void l_Lean_Server_GoToM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_855_ = stack[0].m_obj;
lean_object* v_ci_856_ = stack[1].m_obj;
lean_object* v_lctx_857_ = stack[2].m_obj;
lean_object* v_act_858_ = stack[3].m_obj;
lean_object* v_res_862_;
v_res_862_ = l_Lean_Server_GoToM_run___redArg(v_ctx_855_, v_ci_856_, v_lctx_857_, v_act_858_);
stack->m_obj
 = v_res_862_;
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToM_run___redArg___boxed(lean_object* v_ctx_863_, lean_object* v_ci_864_, lean_object* v_lctx_865_, lean_object* v_act_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Server_GoToM_run___redArg(v_ctx_863_, v_ci_864_, v_lctx_865_, v_act_866_);
return v_res_868_;
}
}
lean_object* l_Lean_Server_GoToM_run(lean_object* v_00_u03b1_869_, lean_object* v_ctx_870_, lean_object* v_ci_871_, lean_object* v_lctx_872_, lean_object* v_act_873_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_Server_GoToM_run___redArg(v_ctx_870_, v_ci_871_, v_lctx_872_, v_act_873_);
return v___x_875_;
}
}
LEAN_EXPORT void l_Lean_Server_GoToM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_870_ = stack[1].m_obj;
lean_object* v_ci_871_ = stack[2].m_obj;
lean_object* v_lctx_872_ = stack[3].m_obj;
lean_object* v_act_873_ = stack[4].m_obj;
lean_object* v_res_876_;
v_res_876_ = l_Lean_Server_GoToM_run(lean_box(0), v_ctx_870_, v_ci_871_, v_lctx_872_, v_act_873_);
stack->m_obj
 = v_res_876_;
}
LEAN_EXPORT lean_object* l_Lean_Server_GoToM_run___boxed(lean_object* v_00_u03b1_877_, lean_object* v_ctx_878_, lean_object* v_ci_879_, lean_object* v_lctx_880_, lean_object* v_act_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_Server_GoToM_run(v_00_u03b1_877_, v_ctx_878_, v_ci_879_, v_lctx_880_, v_act_881_);
return v_res_883_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___x_890_; lean_object* v_env_891_; uint8_t v___x_892_; lean_object* v_env_893_; lean_object* v___x_894_; lean_object* v_toCold_895_; lean_object* v_mctx_896_; lean_object* v_lctx_897_; lean_object* v_options_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_890_ = lean_st_ref_get(v___y_888_);
v_env_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc_ref(v_env_891_);
lean_dec(v___x_890_);
v___x_892_ = 0;
v_env_893_ = l_Lean_Environment_setRecordingDeps(v_env_891_, v___x_892_);
v___x_894_ = lean_st_ref_get(v___y_886_);
v_toCold_895_ = lean_ctor_get(v___y_887_, 0);
v_mctx_896_ = lean_ctor_get(v___x_894_, 0);
lean_inc_ref(v_mctx_896_);
lean_dec(v___x_894_);
v_lctx_897_ = lean_ctor_get(v___y_885_, 2);
v_options_898_ = lean_ctor_get(v_toCold_895_, 2);
lean_inc_ref(v_options_898_);
lean_inc_ref(v_lctx_897_);
v___x_899_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_899_, 0, v_env_893_);
lean_ctor_set(v___x_899_, 1, v_mctx_896_);
lean_ctor_set(v___x_899_, 2, v_lctx_897_);
lean_ctor_set(v___x_899_, 3, v_options_898_);
v___x_900_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v_msgData_884_);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_884_ = stack[0].m_obj;
lean_object* v___y_885_ = stack[1].m_obj;
lean_object* v___y_886_ = stack[2].m_obj;
lean_object* v___y_887_ = stack[3].m_obj;
lean_object* v___y_888_ = stack[4].m_obj;
lean_object* v_res_902_;
v_res_902_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
stack->m_obj
 = v_res_902_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
return v_res_909_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_ref_916_; lean_object* v___x_917_; lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_926_; 
v_ref_916_ = lean_ctor_get(v___y_913_, 2);
v___x_917_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_926_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_926_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_926_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; lean_object* v___x_924_; 
lean_inc(v_ref_916_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_ref_916_);
lean_ctor_set(v___x_922_, 1, v_a_918_);
if (v_isShared_921_ == 0)
{
lean_ctor_set_tag(v___x_920_, 1);
lean_ctor_set(v___x_920_, 0, v___x_922_);
v___x_924_ = v___x_920_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_910_ = stack[0].m_obj;
lean_object* v___y_911_ = stack[1].m_obj;
lean_object* v___y_912_ = stack[2].m_obj;
lean_object* v___y_913_ = stack[3].m_obj;
lean_object* v___y_914_ = stack[4].m_obj;
lean_object* v_res_927_;
v_res_927_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
stack->m_obj
 = v_res_927_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
return v_res_934_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_935_, lean_object* v_msg_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_toCold_943_; lean_object* v_currRecDepth_944_; lean_object* v_ref_945_; uint16_t v_optionFlags_946_; uint8_t v_suppressElabErrors_947_; uint8_t v_isRecordingDeps_948_; lean_object* v_ref_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_toCold_943_ = lean_ctor_get(v___y_940_, 0);
v_currRecDepth_944_ = lean_ctor_get(v___y_940_, 1);
v_ref_945_ = lean_ctor_get(v___y_940_, 2);
v_optionFlags_946_ = lean_ctor_get_uint16(v___y_940_, sizeof(void*)*3);
v_suppressElabErrors_947_ = lean_ctor_get_uint8(v___y_940_, sizeof(void*)*3 + 2);
v_isRecordingDeps_948_ = lean_ctor_get_uint8(v___y_940_, sizeof(void*)*3 + 3);
v_ref_949_ = l_Lean_replaceRef(v_ref_935_, v_ref_945_);
lean_inc(v_currRecDepth_944_);
lean_inc_ref(v_toCold_943_);
v___x_950_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_950_, 0, v_toCold_943_);
lean_ctor_set(v___x_950_, 1, v_currRecDepth_944_);
lean_ctor_set(v___x_950_, 2, v_ref_949_);
lean_ctor_set_uint16(v___x_950_, sizeof(void*)*3, v_optionFlags_946_);
lean_ctor_set_uint8(v___x_950_, sizeof(void*)*3 + 2, v_suppressElabErrors_947_);
lean_ctor_set_uint8(v___x_950_, sizeof(void*)*3 + 3, v_isRecordingDeps_948_);
v___x_951_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_936_, v___y_938_, v___y_939_, v___x_950_, v___y_941_);
lean_dec_ref_known(v___x_950_, 3);
return v___x_951_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_935_ = stack[0].m_obj;
lean_object* v_msg_936_ = stack[1].m_obj;
lean_object* v___y_937_ = stack[2].m_obj;
lean_object* v___y_938_ = stack[3].m_obj;
lean_object* v___y_939_ = stack[4].m_obj;
lean_object* v___y_940_ = stack[5].m_obj;
lean_object* v___y_941_ = stack[6].m_obj;
lean_object* v_res_952_;
v_res_952_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_935_, v_msg_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
stack->m_obj
 = v_res_952_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_953_, lean_object* v_msg_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_953_, v_msg_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v_ref_953_);
return v_res_961_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_962_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_965_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_966_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
lean_ctor_set(v___x_968_, 2, v___x_967_);
lean_ctor_set(v___x_968_, 3, v___x_967_);
lean_ctor_set(v___x_968_, 4, v___x_966_);
lean_ctor_set(v___x_968_, 5, v___x_966_);
lean_ctor_set(v___x_968_, 6, v___x_966_);
lean_ctor_set(v___x_968_, 7, v___x_966_);
lean_ctor_set(v___x_968_, 8, v___x_966_);
lean_ctor_set(v___x_968_, 9, v___x_966_);
lean_ctor_set(v___x_968_, 10, v___x_966_);
lean_ctor_set(v___x_968_, 11, v___x_965_);
return v___x_968_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_969_ = lean_unsigned_to_nat(32u);
v___x_970_ = lean_mk_empty_array_with_capacity(v___x_969_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_972_ = ((size_t)5ULL);
v___x_973_ = lean_unsigned_to_nat(0u);
v___x_974_ = lean_unsigned_to_nat(32u);
v___x_975_ = lean_mk_empty_array_with_capacity(v___x_974_);
v___x_976_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_977_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v___x_975_);
lean_ctor_set(v___x_977_, 2, v___x_973_);
lean_ctor_set(v___x_977_, 3, v___x_973_);
lean_ctor_set_usize(v___x_977_, 4, v___x_972_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_978_ = lean_box(1);
v___x_979_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_980_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_981_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___x_979_);
lean_ctor_set(v___x_981_, 2, v___x_978_);
return v___x_981_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_984_ = l_Lean_stringToMessageData(v___x_983_);
return v___x_984_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_987_ = l_Lean_stringToMessageData(v___x_986_);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_990_ = l_Lean_stringToMessageData(v___x_989_);
return v___x_990_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_993_ = l_Lean_stringToMessageData(v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_996_ = l_Lean_stringToMessageData(v___x_995_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__21(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__20));
v___x_1005_ = l_Lean_stringToMessageData(v___x_1004_);
return v___x_1005_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__23(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__22));
v___x_1008_ = l_Lean_stringToMessageData(v___x_1007_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__25(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__24));
v___x_1011_ = l_Lean_stringToMessageData(v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__27(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__26));
v___x_1014_ = l_Lean_stringToMessageData(v___x_1013_);
return v___x_1014_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1015_, lean_object* v_declHint_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_env_1021_; uint8_t v___x_1022_; 
v___x_1019_ = lean_box(0);
v___x_1020_ = lean_st_ref_get(v___y_1017_);
v_env_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc_ref(v_env_1021_);
lean_dec(v___x_1020_);
v___x_1022_ = l_Lean_Name_isAnonymous(v_declHint_1016_);
if (v___x_1022_ == 0)
{
uint8_t v_isExporting_1023_; 
v_isExporting_1023_ = lean_ctor_get_uint8(v_env_1021_, sizeof(void*)*13);
if (v_isExporting_1023_ == 0)
{
lean_object* v___x_1024_; 
lean_dec_ref(v_env_1021_);
lean_dec(v_declHint_1016_);
v___x_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1024_, 0, v_msg_1015_);
return v___x_1024_;
}
else
{
lean_object* v___x_1025_; uint8_t v___x_1026_; 
lean_inc_ref(v_env_1021_);
v___x_1025_ = l_Lean_Environment_setExporting(v_env_1021_, v___x_1022_);
lean_inc(v_declHint_1016_);
lean_inc_ref(v___x_1025_);
v___x_1026_ = l_Lean_Environment_contains(v___x_1025_, v_declHint_1016_, v_isExporting_1023_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; 
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_env_1021_);
lean_dec(v_declHint_1016_);
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v_msg_1015_);
return v___x_1027_;
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v_c_1033_; lean_object* v___x_1034_; 
v___x_1028_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1029_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1030_ = l_Lean_Options_empty;
v___x_1031_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1025_);
lean_ctor_set(v___x_1031_, 1, v___x_1028_);
lean_ctor_set(v___x_1031_, 2, v___x_1029_);
lean_ctor_set(v___x_1031_, 3, v___x_1030_);
lean_inc(v_declHint_1016_);
v___x_1032_ = l_Lean_MessageData_ofConstName(v_declHint_1016_, v___x_1022_);
v_c_1033_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1033_, 0, v___x_1031_);
lean_ctor_set(v_c_1033_, 1, v___x_1032_);
v___x_1034_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1021_, v_declHint_1016_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
lean_dec_ref(v_env_1021_);
lean_dec(v_declHint_1016_);
v___x_1035_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set(v___x_1036_, 1, v_c_1033_);
v___x_1037_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = l_Lean_MessageData_note(v___x_1038_);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v_msg_1015_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
else
{
lean_object* v_val_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1098_; 
v_val_1042_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1044_ = v___x_1034_;
v_isShared_1045_ = v_isSharedCheck_1098_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_val_1042_);
lean_dec(v___x_1034_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1098_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v_modules_1047_; lean_object* v_moduleNames_1048_; lean_object* v_mod_1049_; uint8_t v___y_1051_; uint8_t v___x_1081_; 
v___x_1046_ = l_Lean_Environment_header(v_env_1021_);
lean_dec_ref(v_env_1021_);
v_modules_1047_ = lean_ctor_get(v___x_1046_, 3);
lean_inc_ref(v_modules_1047_);
v_moduleNames_1048_ = lean_ctor_get(v___x_1046_, 4);
lean_inc_ref(v_moduleNames_1048_);
lean_dec_ref(v___x_1046_);
v_mod_1049_ = lean_array_get(v___x_1019_, v_moduleNames_1048_, v_val_1042_);
lean_dec_ref(v_moduleNames_1048_);
v___x_1081_ = l_Lean_isPrivateName(v_declHint_1016_);
lean_dec(v_declHint_1016_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1082_ = lean_array_get_size(v_modules_1047_);
v___x_1083_ = lean_nat_dec_lt(v_val_1042_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_dec_ref(v_modules_1047_);
lean_dec(v_val_1042_);
v___y_1051_ = v___x_1081_;
goto v___jp_1050_;
}
else
{
lean_object* v___x_1084_; lean_object* v_toImport_1085_; uint8_t v_isExported_1086_; 
v___x_1084_ = lean_array_fget(v_modules_1047_, v_val_1042_);
lean_dec(v_val_1042_);
lean_dec_ref(v_modules_1047_);
v_toImport_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc_ref(v_toImport_1085_);
lean_dec(v___x_1084_);
v_isExported_1086_ = lean_ctor_get_uint8(v_toImport_1085_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1085_);
v___y_1051_ = v_isExported_1086_;
goto v___jp_1050_;
}
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_dec_ref(v_modules_1047_);
lean_del_object(v___x_1044_);
lean_dec(v_val_1042_);
v___x_1087_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v_c_1033_);
v___x_1089_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__25);
v___x_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = l_Lean_MessageData_ofName(v_mod_1049_);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__27);
v___x_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = l_Lean_MessageData_note(v___x_1094_);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v_msg_1015_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
v___jp_1050_:
{
if (v___y_1051_ == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1052_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v_c_1033_);
v___x_1054_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = l_Lean_MessageData_ofName(v_mod_1049_);
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = l_Lean_MessageData_note(v___x_1059_);
v___x_1061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1061_, 0, v_msg_1015_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set_tag(v___x_1044_, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1061_);
v___x_1063_ = v___x_1044_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1065_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v_c_1033_);
v___x_1067_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = l_Lean_MessageData_ofName(v_mod_1049_);
lean_inc_ref(v___x_1069_);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__21);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v___x_1069_);
v___x_1074_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__23);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = l_Lean_MessageData_note(v___x_1075_);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_msg_1015_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set_tag(v___x_1044_, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1077_);
v___x_1079_ = v___x_1044_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
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
lean_object* v___x_1099_; 
lean_dec_ref(v_env_1021_);
lean_dec(v_declHint_1016_);
v___x_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_msg_1015_);
return v___x_1099_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1015_ = stack[0].m_obj;
lean_object* v_declHint_1016_ = stack[1].m_obj;
lean_object* v___y_1017_ = stack[2].m_obj;
lean_object* v_res_1100_;
v_res_1100_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1015_, v_declHint_1016_, v___y_1017_);
stack->m_obj
 = v_res_1100_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1101_, lean_object* v_declHint_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1101_, v_declHint_1102_, v___y_1103_);
lean_dec(v___y_1103_);
return v_res_1105_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1106_, lean_object* v_declHint_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1124_; 
v___x_1114_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1106_, v_declHint_1107_, v___y_1112_);
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1124_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1124_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1119_ = l_Lean_unknownIdentifierMessageTag;
v___x_1120_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v_a_1115_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1120_);
v___x_1122_ = v___x_1117_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1106_ = stack[0].m_obj;
lean_object* v_declHint_1107_ = stack[1].m_obj;
lean_object* v___y_1108_ = stack[2].m_obj;
lean_object* v___y_1109_ = stack[3].m_obj;
lean_object* v___y_1110_ = stack[4].m_obj;
lean_object* v___y_1111_ = stack[5].m_obj;
lean_object* v___y_1112_ = stack[6].m_obj;
lean_object* v_res_1125_;
v_res_1125_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1106_, v_declHint_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
stack->m_obj
 = v_res_1125_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1126_, lean_object* v_declHint_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1126_, v_declHint_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec_ref(v___y_1128_);
return v_res_1134_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_1135_, lean_object* v_msg_1136_, lean_object* v_declHint_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; lean_object* v_a_1145_; lean_object* v___x_1146_; 
v___x_1144_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1136_, v_declHint_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref(v___x_1144_);
v___x_1146_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_1135_, v_a_1145_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
return v___x_1146_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1135_ = stack[0].m_obj;
lean_object* v_msg_1136_ = stack[1].m_obj;
lean_object* v_declHint_1137_ = stack[2].m_obj;
lean_object* v___y_1138_ = stack[3].m_obj;
lean_object* v___y_1139_ = stack[4].m_obj;
lean_object* v___y_1140_ = stack[5].m_obj;
lean_object* v___y_1141_ = stack[6].m_obj;
lean_object* v___y_1142_ = stack[7].m_obj;
lean_object* v_res_1147_;
v_res_1147_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_1135_, v_msg_1136_, v_declHint_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
stack->m_obj
 = v_res_1147_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1148_, lean_object* v_msg_1149_, lean_object* v_declHint_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_1148_, v_msg_1149_, v_declHint_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v_ref_1148_);
return v_res_1157_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0));
v___x_1160_ = l_Lean_stringToMessageData(v___x_1159_);
return v___x_1160_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2));
v___x_1163_ = l_Lean_stringToMessageData(v___x_1162_);
return v___x_1163_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1164_, lean_object* v_constName_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v___x_1172_; uint8_t v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1172_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_1173_ = 0;
lean_inc(v_constName_1165_);
v___x_1174_ = l_Lean_MessageData_ofConstName(v_constName_1165_, v___x_1173_);
v___x_1175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1172_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_1177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_1164_, v___x_1177_, v_constName_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
return v___x_1178_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1164_ = stack[0].m_obj;
lean_object* v_constName_1165_ = stack[1].m_obj;
lean_object* v___y_1166_ = stack[2].m_obj;
lean_object* v___y_1167_ = stack[3].m_obj;
lean_object* v___y_1168_ = stack[4].m_obj;
lean_object* v___y_1169_ = stack[5].m_obj;
lean_object* v___y_1170_ = stack[6].m_obj;
lean_object* v_res_1179_;
v_res_1179_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1164_, v_constName_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
stack->m_obj
 = v_res_1179_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1180_, lean_object* v_constName_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1180_, v_constName_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v_ref_1180_);
return v_res_1188_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_ref_1196_; lean_object* v___x_1197_; 
v_ref_1196_ = lean_ctor_get(v___y_1193_, 2);
v___x_1197_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1196_, v_constName_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
return v___x_1197_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1189_ = stack[0].m_obj;
lean_object* v___y_1190_ = stack[1].m_obj;
lean_object* v___y_1191_ = stack[2].m_obj;
lean_object* v___y_1192_ = stack[3].m_obj;
lean_object* v___y_1193_ = stack[4].m_obj;
lean_object* v___y_1194_ = stack[5].m_obj;
lean_object* v_res_1198_;
v_res_1198_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
stack->m_obj
 = v_res_1198_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec_ref(v___y_1200_);
return v_res_1206_;
}
}
lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(lean_object* v_constName_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___x_1214_; lean_object* v_env_1215_; uint8_t v___x_1216_; lean_object* v___x_1217_; 
v___x_1214_ = lean_st_ref_get(v___y_1212_);
v_env_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc_ref(v_env_1215_);
lean_dec(v___x_1214_);
v___x_1216_ = 0;
lean_inc(v_constName_1207_);
v___x_1217_ = l_Lean_Environment_find_x3f(v_env_1215_, v_constName_1207_, v___x_1216_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
return v___x_1218_;
}
else
{
lean_object* v_val_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec(v_constName_1207_);
v_val_1219_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1217_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_val_1219_);
lean_dec(v___x_1217_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set_tag(v___x_1221_, 0);
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_val_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1207_ = stack[0].m_obj;
lean_object* v___y_1208_ = stack[1].m_obj;
lean_object* v___y_1209_ = stack[2].m_obj;
lean_object* v___y_1210_ = stack[3].m_obj;
lean_object* v___y_1211_ = stack[4].m_obj;
lean_object* v___y_1212_ = stack[5].m_obj;
lean_object* v_res_1227_;
v_res_1227_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(v_constName_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
stack->m_obj
 = v_res_1227_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0___boxed(lean_object* v_constName_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(v_constName_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec_ref(v___y_1229_);
return v_res_1235_;
}
}
lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(lean_object* v_declName_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_box(0);
lean_inc(v_declName_1236_);
v___x_1244_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(v_declName_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1270_; 
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1270_ == 0)
{
lean_object* v_unused_1271_; 
v_unused_1271_ = lean_ctor_get(v___x_1244_, 0);
lean_dec(v_unused_1271_);
v___x_1246_ = v___x_1244_;
v_isShared_1247_ = v_isSharedCheck_1270_;
goto v_resetjp_1245_;
}
else
{
lean_dec(v___x_1244_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1270_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; lean_object* v_env_1249_; lean_object* v___x_1250_; 
v___x_1248_ = lean_st_ref_get(v___y_1241_);
v_env_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc_ref(v_env_1249_);
lean_dec(v___x_1248_);
v___x_1250_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1249_, v_declName_1236_);
lean_dec(v_declName_1236_);
lean_dec_ref(v_env_1249_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1251_ = lean_box(0);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1251_);
v___x_1253_ = v___x_1246_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
else
{
lean_object* v_val_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1269_; 
v_val_1255_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1257_ = v___x_1250_;
v_isShared_1258_ = v_isSharedCheck_1269_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_val_1255_);
lean_dec(v___x_1250_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1269_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v_env_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1259_ = lean_st_ref_get(v___y_1241_);
v_env_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc_ref(v_env_1260_);
lean_dec(v___x_1259_);
v___x_1261_ = l_Lean_Environment_allImportedModuleNames(v_env_1260_);
lean_dec_ref(v_env_1260_);
v___x_1262_ = lean_array_get(v___x_1243_, v___x_1261_, v_val_1255_);
lean_dec(v_val_1255_);
lean_dec_ref(v___x_1261_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1262_);
v___x_1264_ = v___x_1257_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1266_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1264_);
v___x_1266_ = v___x_1246_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec(v_declName_1236_);
v_a_1272_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1244_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1244_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1236_ = stack[0].m_obj;
lean_object* v___y_1237_ = stack[1].m_obj;
lean_object* v___y_1238_ = stack[2].m_obj;
lean_object* v___y_1239_ = stack[3].m_obj;
lean_object* v___y_1240_ = stack[4].m_obj;
lean_object* v___y_1241_ = stack[5].m_obj;
lean_object* v_res_1280_;
v_res_1280_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(v_declName_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
stack->m_obj
 = v_res_1280_;
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0___boxed(lean_object* v_declName_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(v_declName_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec_ref(v___y_1282_);
return v_res_1288_;
}
}
lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(lean_object* v_declName_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(v_declName_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1351_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1351_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1351_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
if (lean_obj_tag(v_a_1297_) == 0)
{
lean_object* v_doc_1301_; lean_object* v_uri_1302_; lean_object* v_mod_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
v_doc_1301_ = lean_ctor_get(v_a_1290_, 0);
v_uri_1302_ = lean_ctor_get(v_doc_1301_, 0);
v_mod_1303_ = lean_ctor_get(v_doc_1301_, 1);
lean_inc_ref(v_uri_1302_);
lean_inc(v_mod_1303_);
v___x_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1304_, 0, v_mod_1303_);
lean_ctor_set(v___x_1304_, 1, v_uri_1302_);
v___x_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1305_);
v___x_1307_ = v___x_1299_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
else
{
lean_object* v_val_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1350_; 
lean_del_object(v___x_1299_);
v_val_1309_ = lean_ctor_get(v_a_1297_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_a_1297_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1311_ = v_a_1297_;
v_isShared_1312_ = v_isSharedCheck_1350_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_val_1309_);
lean_dec(v_a_1297_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1350_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v_ref_1313_; lean_object* v___x_1314_; 
v_ref_1313_ = lean_ctor_get(v_a_1293_, 2);
lean_inc(v_val_1309_);
v___x_1314_ = l_Lean_Server_documentUriFromModule_x3f(v_val_1309_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1335_; 
lean_del_object(v___x_1311_);
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1317_ = v___x_1314_;
v_isShared_1318_ = v_isSharedCheck_1335_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1314_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1335_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
if (lean_obj_tag(v_a_1315_) == 1)
{
lean_object* v_val_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1330_; 
v_val_1319_ = lean_ctor_get(v_a_1315_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_a_1315_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1321_ = v_a_1315_;
v_isShared_1322_ = v_isSharedCheck_1330_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_val_1319_);
lean_dec(v_a_1315_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1330_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1323_, 0, v_val_1309_);
lean_ctor_set(v___x_1323_, 1, v_val_1319_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1323_);
v___x_1325_ = v___x_1321_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
lean_object* v___x_1327_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1325_);
v___x_1327_ = v___x_1317_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1333_; 
lean_dec(v_a_1315_);
lean_dec(v_val_1309_);
v___x_1331_ = lean_box(0);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1331_);
v___x_1333_ = v___x_1317_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1349_; 
lean_dec(v_val_1309_);
v_a_1336_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1338_ = v___x_1314_;
v_isShared_1339_ = v_isSharedCheck_1349_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1314_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1349_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1340_ = lean_io_error_to_string(v_a_1336_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set_tag(v___x_1311_, 3);
lean_ctor_set(v___x_1311_, 0, v___x_1340_);
v___x_1342_ = v___x_1311_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1343_ = l_Lean_MessageData_ofFormat(v___x_1342_);
lean_inc(v_ref_1313_);
v___x_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1344_, 0, v_ref_1313_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1344_);
v___x_1346_ = v___x_1338_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
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
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
v_a_1352_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1296_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1296_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1289_ = stack[0].m_obj;
lean_object* v_a_1290_ = stack[1].m_obj;
lean_object* v_a_1291_ = stack[2].m_obj;
lean_object* v_a_1292_ = stack[3].m_obj;
lean_object* v_a_1293_ = stack[4].m_obj;
lean_object* v_a_1294_ = stack[5].m_obj;
lean_object* v_res_1360_;
v_res_1360_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(v_declName_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_);
stack->m_obj
 = v_res_1360_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f___boxed(lean_object* v_declName_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(v_declName_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec_ref(v_a_1362_);
return v_res_1368_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1369_, lean_object* v_constName_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
return v___x_1377_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1370_ = stack[1].m_obj;
lean_object* v___y_1371_ = stack[2].m_obj;
lean_object* v___y_1372_ = stack[3].m_obj;
lean_object* v___y_1373_ = stack[4].m_obj;
lean_object* v___y_1374_ = stack[5].m_obj;
lean_object* v___y_1375_ = stack[6].m_obj;
lean_object* v_res_1378_;
v_res_1378_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1(lean_box(0), v_constName_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
stack->m_obj
 = v_res_1378_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1379_, lean_object* v_constName_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1(v_00_u03b1_1379_, v_constName_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec_ref(v___y_1381_);
return v_res_1387_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1388_, lean_object* v_ref_1389_, lean_object* v_constName_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1389_, v_constName_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
return v___x_1397_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1389_ = stack[1].m_obj;
lean_object* v_constName_1390_ = stack[2].m_obj;
lean_object* v___y_1391_ = stack[3].m_obj;
lean_object* v___y_1392_ = stack[4].m_obj;
lean_object* v___y_1393_ = stack[5].m_obj;
lean_object* v___y_1394_ = stack[6].m_obj;
lean_object* v___y_1395_ = stack[7].m_obj;
lean_object* v_res_1398_;
v_res_1398_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2(lean_box(0), v_ref_1389_, v_constName_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
stack->m_obj
 = v_res_1398_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1399_, lean_object* v_ref_1400_, lean_object* v_constName_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1399_, v_ref_1400_, v_constName_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v_ref_1400_);
return v_res_1408_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_1409_, lean_object* v_ref_1410_, lean_object* v_msg_1411_, lean_object* v_declHint_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_1410_, v_msg_1411_, v_declHint_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
return v___x_1419_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1410_ = stack[1].m_obj;
lean_object* v_msg_1411_ = stack[2].m_obj;
lean_object* v_declHint_1412_ = stack[3].m_obj;
lean_object* v___y_1413_ = stack[4].m_obj;
lean_object* v___y_1414_ = stack[5].m_obj;
lean_object* v___y_1415_ = stack[6].m_obj;
lean_object* v___y_1416_ = stack[7].m_obj;
lean_object* v___y_1417_ = stack[8].m_obj;
lean_object* v_res_1420_;
v_res_1420_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_box(0), v_ref_1410_, v_msg_1411_, v_declHint_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
stack->m_obj
 = v_res_1420_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1421_, lean_object* v_ref_1422_, lean_object* v_msg_1423_, lean_object* v_declHint_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b1_1421_, v_ref_1422_, v_msg_1423_, v_declHint_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v_ref_1422_);
return v_res_1431_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1432_, lean_object* v_declHint_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1432_, v_declHint_1433_, v___y_1438_);
return v___x_1440_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1432_ = stack[0].m_obj;
lean_object* v_declHint_1433_ = stack[1].m_obj;
lean_object* v___y_1434_ = stack[2].m_obj;
lean_object* v___y_1435_ = stack[3].m_obj;
lean_object* v___y_1436_ = stack[4].m_obj;
lean_object* v___y_1437_ = stack[5].m_obj;
lean_object* v___y_1438_ = stack[6].m_obj;
lean_object* v_res_1441_;
v_res_1441_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1432_, v_declHint_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
stack->m_obj
 = v_res_1441_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1442_, lean_object* v_declHint_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1442_, v_declHint_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec_ref(v___y_1444_);
return v_res_1450_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1451_, lean_object* v_ref_1452_, lean_object* v_msg_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_1452_, v_msg_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
return v___x_1460_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1452_ = stack[1].m_obj;
lean_object* v_msg_1453_ = stack[2].m_obj;
lean_object* v___y_1454_ = stack[3].m_obj;
lean_object* v___y_1455_ = stack[4].m_obj;
lean_object* v___y_1456_ = stack[5].m_obj;
lean_object* v___y_1457_ = stack[6].m_obj;
lean_object* v___y_1458_ = stack[7].m_obj;
lean_object* v_res_1461_;
v_res_1461_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(lean_box(0), v_ref_1452_, v_msg_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
stack->m_obj
 = v_res_1461_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1462_, lean_object* v_ref_1463_, lean_object* v_msg_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_1462_, v_ref_1463_, v_msg_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v_ref_1463_);
return v_res_1471_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1472_, lean_object* v_msg_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1473_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
return v___x_1480_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1473_ = stack[1].m_obj;
lean_object* v___y_1474_ = stack[2].m_obj;
lean_object* v___y_1475_ = stack[3].m_obj;
lean_object* v___y_1476_ = stack[4].m_obj;
lean_object* v___y_1477_ = stack[5].m_obj;
lean_object* v___y_1478_ = stack[6].m_obj;
lean_object* v_res_1481_;
v_res_1481_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(lean_box(0), v_msg_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
stack->m_obj
 = v_res_1481_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1482_, lean_object* v_msg_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1482_, v_msg_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec_ref(v___y_1484_);
return v_res_1490_;
}
}
lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(lean_object* v_declName_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v___x_1494_; lean_object* v_env_1495_; uint8_t v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1494_ = lean_st_ref_get(v___y_1492_);
v_env_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc_ref(v_env_1495_);
lean_dec(v___x_1494_);
v___x_1496_ = l_Lean_isRecCore(v_env_1495_, v_declName_1491_);
v___x_1497_ = lean_box(v___x_1496_);
v___x_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT void l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1491_ = stack[0].m_obj;
lean_object* v___y_1492_ = stack[1].m_obj;
lean_object* v_res_1499_;
v_res_1499_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_1491_, v___y_1492_);
stack->m_obj
 = v_res_1499_;
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_1500_, v___y_1501_);
lean_dec(v___y_1501_);
return v_res_1503_;
}
}
lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(lean_object* v_declName_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v_env_1509_; lean_object* v___x_1510_; lean_object* v_env_1511_; lean_object* v___x_1512_; lean_object* v_toEnvExtension_1513_; lean_object* v_asyncMode_1514_; uint8_t v___x_1515_; lean_object* v___x_1516_; 
v___x_1507_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1508_ = lean_st_ref_get(v___y_1505_);
v_env_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc_ref(v_env_1509_);
lean_dec(v___x_1508_);
v___x_1510_ = lean_st_ref_get(v___y_1505_);
v_env_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc_ref(v_env_1511_);
lean_dec(v___x_1510_);
v___x_1512_ = l_Lean_declRangeExt;
v_toEnvExtension_1513_ = lean_ctor_get(v___x_1512_, 0);
v_asyncMode_1514_ = lean_ctor_get(v_toEnvExtension_1513_, 2);
v___x_1515_ = 0;
lean_inc(v_declName_1504_);
v___x_1516_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1507_, v___x_1512_, v_env_1509_, v_declName_1504_, v_asyncMode_1514_, v___x_1515_);
if (lean_obj_tag(v___x_1516_) == 0)
{
uint8_t v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = 1;
v___x_1518_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1507_, v___x_1512_, v_env_1511_, v_declName_1504_, v_asyncMode_1514_, v___x_1517_);
v___x_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
return v___x_1519_;
}
else
{
lean_object* v___x_1520_; 
lean_dec_ref(v_env_1511_);
lean_dec(v_declName_1504_);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1516_);
return v___x_1520_;
}
}
}
LEAN_EXPORT void l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1504_ = stack[0].m_obj;
lean_object* v___y_1505_ = stack[1].m_obj;
lean_object* v_res_1521_;
v_res_1521_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_1504_, v___y_1505_);
stack->m_obj
 = v_res_1521_;
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_1522_, v___y_1523_);
lean_dec(v___y_1523_);
return v_res_1525_;
}
}
lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(lean_object* v_declName_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_ranges_1534_; lean_object* v___x_1540_; lean_object* v_env_1541_; lean_object* v___x_1542_; lean_object* v_a_1543_; uint8_t v___y_1549_; uint8_t v___x_1553_; 
v___x_1540_ = lean_st_ref_get(v___y_1531_);
v_env_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc_ref_n(v_env_1541_, 2);
lean_dec(v___x_1540_);
lean_inc_n(v_declName_1526_, 2);
v___x_1542_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_1526_, v___y_1531_);
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref(v___x_1542_);
v___x_1553_ = l_Lean_isAuxRecursor(v_env_1541_, v_declName_1526_);
if (v___x_1553_ == 0)
{
uint8_t v___x_1554_; 
lean_inc(v_declName_1526_);
v___x_1554_ = l_Lean_isNoConfusion(v_env_1541_, v_declName_1526_);
v___y_1549_ = v___x_1554_;
goto v___jp_1548_;
}
else
{
lean_dec_ref(v_env_1541_);
v___y_1549_ = v___x_1553_;
goto v___jp_1548_;
}
v___jp_1533_:
{
if (lean_obj_tag(v_ranges_1534_) == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1535_ = l_Lean_builtinDeclRanges;
v___x_1536_ = lean_st_ref_get(v___x_1535_);
v___x_1537_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1536_, v_declName_1526_);
lean_dec(v_declName_1526_);
lean_dec(v___x_1536_);
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
return v___x_1538_;
}
else
{
lean_object* v___x_1539_; 
lean_dec(v_declName_1526_);
v___x_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1539_, 0, v_ranges_1534_);
return v___x_1539_;
}
}
v___jp_1544_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v_a_1547_; 
v___x_1545_ = l_Lean_Name_getPrefix(v_declName_1526_);
v___x_1546_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v___x_1545_, v___y_1531_);
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref(v___x_1546_);
v_ranges_1534_ = v_a_1547_;
goto v___jp_1533_;
}
v___jp_1548_:
{
if (v___y_1549_ == 0)
{
uint8_t v___x_1550_; 
v___x_1550_ = lean_unbox(v_a_1543_);
lean_dec(v_a_1543_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; lean_object* v_a_1552_; 
lean_inc(v_declName_1526_);
v___x_1551_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_1526_, v___y_1531_);
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref(v___x_1551_);
v_ranges_1534_ = v_a_1552_;
goto v___jp_1533_;
}
else
{
goto v___jp_1544_;
}
}
else
{
lean_dec(v_a_1543_);
goto v___jp_1544_;
}
}
}
}
LEAN_EXPORT void l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1526_ = stack[0].m_obj;
lean_object* v___y_1527_ = stack[1].m_obj;
lean_object* v___y_1528_ = stack[2].m_obj;
lean_object* v___y_1529_ = stack[3].m_obj;
lean_object* v___y_1530_ = stack[4].m_obj;
lean_object* v___y_1531_ = stack[5].m_obj;
lean_object* v_res_1555_;
v_res_1555_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(v_declName_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
stack->m_obj
 = v_res_1555_;
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0___boxed(lean_object* v_declName_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(v_declName_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec_ref(v___y_1557_);
return v_res_1563_;
}
}
lean_object* l_Lean_Server_locationLinksFromDecl(lean_object* v_declName_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v___x_1573_; lean_object* v_env_1574_; uint8_t v___x_1575_; uint8_t v___x_1576_; 
v___x_1573_ = lean_st_ref_get(v_a_1571_);
v_env_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc_ref(v_env_1574_);
lean_dec(v___x_1573_);
v___x_1575_ = 1;
lean_inc(v_declName_1566_);
v___x_1576_ = l_Lean_Environment_contains(v_env_1574_, v_declName_1566_, v___x_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_dec(v_declName_1566_);
v___x_1577_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
return v___x_1578_;
}
else
{
uint8_t v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = 0;
lean_inc(v_declName_1566_);
v___x_1580_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(v_declName_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1656_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1656_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1656_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
if (lean_obj_tag(v_a_1581_) == 1)
{
lean_object* v_val_1585_; lean_object* v_fst_1586_; lean_object* v_snd_1587_; lean_object* v___x_1588_; 
lean_del_object(v___x_1583_);
v_val_1585_ = lean_ctor_get(v_a_1581_, 0);
lean_inc(v_val_1585_);
lean_dec_ref_known(v_a_1581_, 1);
v_fst_1586_ = lean_ctor_get(v_val_1585_, 0);
lean_inc(v_fst_1586_);
v_snd_1587_ = lean_ctor_get(v_val_1585_, 1);
lean_inc(v_snd_1587_);
lean_dec(v_val_1585_);
lean_inc(v_declName_1566_);
v___x_1588_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(v_declName_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1643_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1643_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1643_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
if (lean_obj_tag(v_a_1589_) == 1)
{
lean_object* v_val_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1638_; 
v_val_1593_ = lean_ctor_get(v_a_1589_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_a_1589_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1595_ = v_a_1589_;
v_isShared_1596_ = v_isSharedCheck_1638_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_val_1593_);
lean_dec(v_a_1589_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1638_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___y_1598_; lean_object* v_originInfo_x3f_1622_; 
v_originInfo_x3f_1622_ = lean_ctor_get(v_a_1567_, 2);
if (lean_obj_tag(v_originInfo_x3f_1622_) == 0)
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_box(0);
v___y_1598_ = v___x_1623_;
goto v___jp_1597_;
}
else
{
lean_object* v_doc_1624_; lean_object* v_val_1625_; lean_object* v___x_1626_; 
v_doc_1624_ = lean_ctor_get(v_a_1567_, 0);
v_val_1625_ = lean_ctor_get(v_originInfo_x3f_1622_, 0);
v___x_1626_ = l_Lean_Elab_Info_range_x3f(v_val_1625_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_box(0);
v___y_1598_ = v___x_1627_;
goto v___jp_1597_;
}
else
{
lean_object* v_val_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1637_; 
v_val_1628_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1630_ = v___x_1626_;
v_isShared_1631_ = v_isSharedCheck_1637_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_val_1628_);
lean_dec(v___x_1626_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1637_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v_text_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
v_text_1632_ = lean_ctor_get(v_doc_1624_, 3);
lean_inc_ref(v_text_1632_);
v___x_1633_ = l_Lean_Syntax_Range_toLspRange(v_text_1632_, v_val_1628_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v___x_1633_);
v___x_1635_ = v___x_1630_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
v___y_1598_ = v___x_1635_;
goto v___jp_1597_;
}
}
}
}
v___jp_1597_:
{
lean_object* v_range_1599_; lean_object* v_selectionRange_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1621_; 
v_range_1599_ = lean_ctor_get(v_val_1593_, 0);
v_selectionRange_1600_ = lean_ctor_get(v_val_1593_, 1);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_val_1593_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1602_ = v_val_1593_;
v_isShared_1603_ = v_isSharedCheck_1621_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_selectionRange_1600_);
lean_inc(v_range_1599_);
lean_dec(v_val_1593_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1621_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1604_ = l_Lean_DeclarationRange_toLspRange(v_range_1599_);
v___x_1605_ = l_Lean_DeclarationRange_toLspRange(v_selectionRange_1600_);
v___x_1606_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1606_, 0, v___y_1598_);
lean_ctor_set(v___x_1606_, 1, v_snd_1587_);
lean_ctor_set(v___x_1606_, 2, v___x_1604_);
lean_ctor_set(v___x_1606_, 3, v___x_1605_);
v___x_1607_ = l_Lean_Name_eraseMacroScopes(v_declName_1566_);
lean_dec(v_declName_1566_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 1, v___x_1607_);
lean_ctor_set(v___x_1602_, 0, v_fst_1586_);
v___x_1609_ = v___x_1602_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_fst_1586_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1611_; 
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v___x_1609_);
v___x_1611_ = v___x_1595_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1612_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1612_, 0, v___x_1606_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
lean_ctor_set_uint8(v___x_1612_, sizeof(void*)*2, v___x_1579_);
v___x_1613_ = lean_unsigned_to_nat(1u);
v___x_1614_ = lean_mk_empty_array_with_capacity(v___x_1613_);
v___x_1615_ = lean_array_push(v___x_1614_, v___x_1612_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1615_);
v___x_1617_ = v___x_1591_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
lean_dec(v_a_1589_);
lean_dec(v_snd_1587_);
lean_dec(v_fst_1586_);
lean_dec(v_declName_1566_);
v___x_1639_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1639_);
v___x_1641_ = v___x_1591_;
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
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec(v_snd_1587_);
lean_dec(v_fst_1586_);
lean_dec(v_declName_1566_);
v_a_1644_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1588_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1588_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1654_; 
lean_dec(v_a_1581_);
lean_dec(v_declName_1566_);
v___x_1652_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1652_);
v___x_1654_ = v___x_1583_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec(v_declName_1566_);
v_a_1657_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1580_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1580_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_locationLinksFromDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1566_ = stack[0].m_obj;
lean_object* v_a_1567_ = stack[1].m_obj;
lean_object* v_a_1568_ = stack[2].m_obj;
lean_object* v_a_1569_ = stack[3].m_obj;
lean_object* v_a_1570_ = stack[4].m_obj;
lean_object* v_a_1571_ = stack[5].m_obj;
lean_object* v_res_1665_;
v_res_1665_ = l_Lean_Server_locationLinksFromDecl(v_declName_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
stack->m_obj
 = v_res_1665_;
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDecl___boxed(lean_object* v_declName_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_Server_locationLinksFromDecl(v_declName_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec_ref(v_a_1667_);
return v_res_1673_;
}
}
lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0(lean_object* v_declName_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_1674_, v___y_1679_);
return v___x_1681_;
}
}
LEAN_EXPORT void l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1674_ = stack[0].m_obj;
lean_object* v___y_1675_ = stack[1].m_obj;
lean_object* v___y_1676_ = stack[2].m_obj;
lean_object* v___y_1677_ = stack[3].m_obj;
lean_object* v___y_1678_ = stack[4].m_obj;
lean_object* v___y_1679_ = stack[5].m_obj;
lean_object* v_res_1682_;
v_res_1682_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0(v_declName_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
stack->m_obj
 = v_res_1682_;
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___boxed(lean_object* v_declName_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0(v_declName_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec_ref(v___y_1684_);
return v_res_1690_;
}
}
lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1(lean_object* v_declName_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_1691_, v___y_1696_);
return v___x_1698_;
}
}
LEAN_EXPORT void l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1691_ = stack[0].m_obj;
lean_object* v___y_1692_ = stack[1].m_obj;
lean_object* v___y_1693_ = stack[2].m_obj;
lean_object* v___y_1694_ = stack[3].m_obj;
lean_object* v___y_1695_ = stack[4].m_obj;
lean_object* v___y_1696_ = stack[5].m_obj;
lean_object* v_res_1699_;
v_res_1699_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1(v_declName_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
stack->m_obj
 = v_res_1699_;
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___boxed(lean_object* v_declName_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1(v_declName_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec_ref(v___y_1701_);
return v_res_1707_;
}
}
uint8_t l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0(lean_object* v_id_1708_, lean_object* v_x_1709_){
_start:
{
if (lean_obj_tag(v_x_1709_) == 1)
{
lean_object* v_i_1710_; lean_object* v_expr_1711_; 
v_i_1710_ = lean_ctor_get(v_x_1709_, 0);
v_expr_1711_ = lean_ctor_get(v_i_1710_, 3);
if (lean_obj_tag(v_expr_1711_) == 1)
{
uint8_t v_isBinder_1712_; 
v_isBinder_1712_ = lean_ctor_get_uint8(v_i_1710_, sizeof(void*)*4);
if (v_isBinder_1712_ == 1)
{
lean_object* v_fvarId_1713_; uint8_t v___x_1714_; 
v_fvarId_1713_ = lean_ctor_get(v_expr_1711_, 0);
v___x_1714_ = l_Lean_instBEqFVarId_beq(v_fvarId_1713_, v_id_1708_);
return v___x_1714_;
}
else
{
uint8_t v___x_1715_; 
v___x_1715_ = 0;
return v___x_1715_;
}
}
else
{
uint8_t v___x_1716_; 
v___x_1716_ = 0;
return v___x_1716_;
}
}
else
{
uint8_t v___x_1717_; 
v___x_1717_ = 0;
return v___x_1717_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_1708_ = stack[0].m_obj;
lean_object* v_x_1709_ = stack[1].m_obj;
uint8_t v_res_1718_;
v_res_1718_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0(v_id_1708_, v_x_1709_);
stack->m_num = v_res_1718_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0___boxed(lean_object* v_id_1719_, lean_object* v_x_1720_){
_start:
{
uint8_t v_res_1721_; lean_object* v_r_1722_; 
v_res_1721_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0(v_id_1719_, v_x_1720_);
lean_dec_ref(v_x_1720_);
lean_dec(v_id_1719_);
v_r_1722_ = lean_box(v_res_1721_);
return v_r_1722_;
}
}
lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(lean_object* v_id_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v_infoTree_x3f_1726_; 
v_infoTree_x3f_1726_ = lean_ctor_get(v_a_1724_, 1);
if (lean_obj_tag(v_infoTree_x3f_1726_) == 1)
{
lean_object* v_val_1727_; lean_object* v___f_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v_val_1727_ = lean_ctor_get(v_infoTree_x3f_1726_, 0);
v___f_1728_ = lean_alloc_closure((void*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1728_, 0, v_id_1723_);
lean_inc(v_val_1727_);
v___x_1729_ = l_Lean_Elab_InfoTree_findInfo_x3f(v___f_1728_, v_val_1727_);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
lean_dec(v_id_1723_);
v___x_1731_ = lean_box(0);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
return v___x_1732_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_1723_ = stack[0].m_obj;
lean_object* v_a_1724_ = stack[1].m_obj;
lean_object* v_res_1733_;
v_res_1733_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(v_id_1723_, v_a_1724_);
stack->m_obj
 = v_res_1733_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___boxed(lean_object* v_id_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(v_id_1734_, v_a_1735_);
lean_dec_ref(v_a_1735_);
return v_res_1737_;
}
}
lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f(lean_object* v_id_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(v_id_1738_, v_a_1739_);
return v___x_1745_;
}
}
LEAN_EXPORT void l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_1738_ = stack[0].m_obj;
lean_object* v_a_1739_ = stack[1].m_obj;
lean_object* v_a_1740_ = stack[2].m_obj;
lean_object* v_a_1741_ = stack[3].m_obj;
lean_object* v_a_1742_ = stack[4].m_obj;
lean_object* v_a_1743_ = stack[5].m_obj;
lean_object* v_res_1746_;
v_res_1746_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f(v_id_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
stack->m_obj
 = v_res_1746_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___boxed(lean_object* v_id_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f(v_id_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
lean_dec(v_a_1750_);
lean_dec_ref(v_a_1749_);
lean_dec_ref(v_a_1748_);
return v_res_1754_;
}
}
lean_object* l_Lean_Server_locationLinksFromBinder___redArg(lean_object* v_id_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v_doc_1758_; lean_object* v_originInfo_x3f_1759_; lean_object* v___x_1760_; lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1804_; 
v_doc_1758_ = lean_ctor_get(v_a_1756_, 0);
v_originInfo_x3f_1759_ = lean_ctor_get(v_a_1756_, 2);
v___x_1760_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(v_id_1755_, v_a_1756_);
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1763_ = v___x_1760_;
v_isShared_1764_ = v_isSharedCheck_1804_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1760_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1804_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
if (lean_obj_tag(v_a_1761_) == 1)
{
lean_object* v_val_1765_; lean_object* v___x_1766_; 
v_val_1765_ = lean_ctor_get(v_a_1761_, 0);
lean_inc(v_val_1765_);
lean_dec_ref_known(v_a_1761_, 1);
v___x_1766_ = l_Lean_Elab_Info_range_x3f(v_val_1765_);
lean_dec(v_val_1765_);
if (lean_obj_tag(v___x_1766_) == 1)
{
lean_object* v_val_1767_; lean_object* v_uri_1768_; lean_object* v_text_1769_; lean_object* v___x_1770_; lean_object* v___y_1772_; 
v_val_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_val_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v_uri_1768_ = lean_ctor_get(v_doc_1758_, 0);
v_text_1769_ = lean_ctor_get(v_doc_1758_, 3);
lean_inc_ref(v_text_1769_);
v___x_1770_ = l_Lean_Syntax_Range_toLspRange(v_text_1769_, v_val_1767_);
if (lean_obj_tag(v_originInfo_x3f_1759_) == 0)
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_box(0);
v___y_1772_ = v___x_1783_;
goto v___jp_1771_;
}
else
{
lean_object* v_val_1784_; lean_object* v___x_1785_; 
v_val_1784_ = lean_ctor_get(v_originInfo_x3f_1759_, 0);
v___x_1785_ = l_Lean_Elab_Info_range_x3f(v_val_1784_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_box(0);
v___y_1772_ = v___x_1786_;
goto v___jp_1771_;
}
else
{
lean_object* v_val_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1795_; 
v_val_1787_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1789_ = v___x_1785_;
v_isShared_1790_ = v_isSharedCheck_1795_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_val_1787_);
lean_dec(v___x_1785_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1795_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___x_1793_; 
lean_inc_ref(v_text_1769_);
v___x_1791_ = l_Lean_Syntax_Range_toLspRange(v_text_1769_, v_val_1787_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1791_);
v___x_1793_ = v___x_1789_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
v___y_1772_ = v___x_1793_;
goto v___jp_1771_;
}
}
}
}
v___jp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
lean_inc_ref(v___x_1770_);
lean_inc_ref(v_uri_1768_);
v___x_1773_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1773_, 0, v___y_1772_);
lean_ctor_set(v___x_1773_, 1, v_uri_1768_);
lean_ctor_set(v___x_1773_, 2, v___x_1770_);
lean_ctor_set(v___x_1773_, 3, v___x_1770_);
v___x_1774_ = lean_box(0);
v___x_1775_ = 0;
v___x_1776_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1776_, 0, v___x_1773_);
lean_ctor_set(v___x_1776_, 1, v___x_1774_);
lean_ctor_set_uint8(v___x_1776_, sizeof(void*)*2, v___x_1775_);
v___x_1777_ = lean_unsigned_to_nat(1u);
v___x_1778_ = lean_mk_empty_array_with_capacity(v___x_1777_);
v___x_1779_ = lean_array_push(v___x_1778_, v___x_1776_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1779_);
v___x_1781_ = v___x_1763_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1798_; 
lean_dec(v___x_1766_);
v___x_1796_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1796_);
v___x_1798_ = v___x_1763_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1802_; 
lean_dec(v_a_1761_);
v___x_1800_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1800_);
v___x_1802_ = v___x_1763_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_locationLinksFromBinder___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_1755_ = stack[0].m_obj;
lean_object* v_a_1756_ = stack[1].m_obj;
lean_object* v_res_1805_;
v_res_1805_ = l_Lean_Server_locationLinksFromBinder___redArg(v_id_1755_, v_a_1756_);
stack->m_obj
 = v_res_1805_;
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromBinder___redArg___boxed(lean_object* v_id_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_Server_locationLinksFromBinder___redArg(v_id_1806_, v_a_1807_);
lean_dec_ref(v_a_1807_);
return v_res_1809_;
}
}
lean_object* l_Lean_Server_locationLinksFromBinder(lean_object* v_id_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_Server_locationLinksFromBinder___redArg(v_id_1810_, v_a_1811_);
return v___x_1817_;
}
}
LEAN_EXPORT void l_Lean_Server_locationLinksFromBinder_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_1810_ = stack[0].m_obj;
lean_object* v_a_1811_ = stack[1].m_obj;
lean_object* v_a_1812_ = stack[2].m_obj;
lean_object* v_a_1813_ = stack[3].m_obj;
lean_object* v_a_1814_ = stack[4].m_obj;
lean_object* v_a_1815_ = stack[5].m_obj;
lean_object* v_res_1818_;
v_res_1818_ = l_Lean_Server_locationLinksFromBinder(v_id_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
stack->m_obj
 = v_res_1818_;
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromBinder___boxed(lean_object* v_id_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_Server_locationLinksFromBinder(v_id_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
lean_dec_ref(v_a_1820_);
return v_res_1826_;
}
}
lean_object* l_Lean_Server_locationLinksFromImport___redArg(lean_object* v_i_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v_stx_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1971_; 
v_stx_1874_ = lean_ctor_get(v_i_1858_, 1);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_i_1858_);
if (v_isSharedCheck_1971_ == 0)
{
lean_object* v_unused_1972_; 
v_unused_1972_ = lean_ctor_get(v_i_1858_, 0);
lean_dec(v_unused_1972_);
v___x_1876_ = v_i_1858_;
v_isShared_1877_ = v_isSharedCheck_1971_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_stx_1874_);
lean_dec(v_i_1858_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1971_;
goto v_resetjp_1875_;
}
v___jp_1862_:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
lean_inc_ref_n(v___y_1864_, 2);
v___x_1866_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1866_, 0, v___y_1865_);
lean_ctor_set(v___x_1866_, 1, v___y_1863_);
lean_ctor_set(v___x_1866_, 2, v___y_1864_);
lean_ctor_set(v___x_1866_, 3, v___y_1864_);
v___x_1867_ = lean_box(0);
v___x_1868_ = 0;
v___x_1869_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1869_, 0, v___x_1866_);
lean_ctor_set(v___x_1869_, 1, v___x_1867_);
lean_ctor_set_uint8(v___x_1869_, sizeof(void*)*2, v___x_1868_);
v___x_1870_ = lean_unsigned_to_nat(1u);
v___x_1871_ = lean_mk_empty_array_with_capacity(v___x_1870_);
v___x_1872_ = lean_array_push(v___x_1871_, v___x_1869_);
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
return v___x_1873_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; uint8_t v___x_1879_; 
v___x_1878_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__4));
lean_inc(v_stx_1874_);
v___x_1879_ = l_Lean_Syntax_isOfKind(v_stx_1874_, v___x_1878_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
lean_del_object(v___x_1876_);
lean_dec(v_stx_1874_);
v___x_1880_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
return v___x_1881_;
}
else
{
lean_object* v___x_1882_; lean_object* v___y_1884_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1948_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
v___x_1882_ = lean_unsigned_to_nat(0u);
v___x_1960_ = l_Lean_Syntax_getArg(v_stx_1874_, v___x_1882_);
v___x_1961_ = l_Lean_Syntax_isNone(v___x_1960_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1962_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1960_);
v___x_1963_ = l_Lean_Syntax_matchesNull(v___x_1960_, v___x_1962_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_dec(v___x_1960_);
lean_del_object(v___x_1876_);
lean_dec(v_stx_1874_);
v___x_1964_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
return v___x_1965_;
}
else
{
lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1966_ = l_Lean_Syntax_getArg(v___x_1960_, v___x_1882_);
lean_dec(v___x_1960_);
v___x_1967_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__12));
v___x_1968_ = l_Lean_Syntax_isOfKind(v___x_1966_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
lean_del_object(v___x_1876_);
lean_dec(v_stx_1874_);
v___x_1969_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
return v___x_1970_;
}
else
{
v___y_1948_ = v_a_1860_;
goto v___jp_1947_;
}
}
}
else
{
lean_dec(v___x_1960_);
v___y_1948_ = v_a_1860_;
goto v___jp_1947_;
}
v___jp_1883_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v___x_1885_ = lean_unsigned_to_nat(5u);
v___x_1886_ = l_Lean_Syntax_getArg(v_stx_1874_, v___x_1885_);
v___x_1887_ = l_Lean_Syntax_matchesNull(v___x_1886_, v___x_1882_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_del_object(v___x_1876_);
lean_dec(v_stx_1874_);
v___x_1888_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
return v___x_1889_;
}
else
{
lean_object* v_ref_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v_ref_1890_ = lean_ctor_get(v___y_1884_, 2);
v___x_1891_ = lean_unsigned_to_nat(4u);
v___x_1892_ = l_Lean_Syntax_getArg(v_stx_1874_, v___x_1891_);
lean_dec(v_stx_1874_);
v___x_1893_ = l_Lean_TSyntax_getId(v___x_1892_);
v___x_1894_ = l_Lean_Server_documentUriFromModule_x3f(v___x_1893_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1918_; 
lean_del_object(v___x_1876_);
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1918_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1918_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
if (lean_obj_tag(v_a_1895_) == 1)
{
lean_object* v_val_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
lean_del_object(v___x_1897_);
v_val_1899_ = lean_ctor_get(v_a_1895_, 0);
lean_inc(v_val_1899_);
lean_dec_ref_known(v_a_1895_, 1);
v___x_1900_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__6));
v___x_1901_ = l_Lean_Syntax_getRange_x3f(v___x_1892_, v___x_1879_);
lean_dec(v___x_1892_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v___x_1902_; 
v___x_1902_ = lean_box(0);
v___y_1863_ = v_val_1899_;
v___y_1864_ = v___x_1900_;
v___y_1865_ = v___x_1902_;
goto v___jp_1862_;
}
else
{
lean_object* v_doc_1903_; lean_object* v_val_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1913_; 
v_doc_1903_ = lean_ctor_get(v_a_1859_, 0);
v_val_1904_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1906_ = v___x_1901_;
v_isShared_1907_ = v_isSharedCheck_1913_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_val_1904_);
lean_dec(v___x_1901_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1913_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v_text_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
v_text_1908_ = lean_ctor_get(v_doc_1903_, 3);
lean_inc_ref(v_text_1908_);
v___x_1909_ = l_Lean_Syntax_Range_toLspRange(v_text_1908_, v_val_1904_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v___x_1909_);
v___x_1911_ = v___x_1906_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
v___y_1863_ = v_val_1899_;
v___y_1864_ = v___x_1900_;
v___y_1865_ = v___x_1911_;
goto v___jp_1862_;
}
}
}
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
lean_dec(v_a_1895_);
lean_dec(v___x_1892_);
v___x_1914_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1914_);
v___x_1916_ = v___x_1897_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1932_; 
lean_dec(v___x_1892_);
v_a_1919_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1921_ = v___x_1894_;
v_isShared_1922_ = v_isSharedCheck_1932_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1894_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1932_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1923_ = lean_io_error_to_string(v_a_1919_);
v___x_1924_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
v___x_1925_ = l_Lean_MessageData_ofFormat(v___x_1924_);
lean_inc(v_ref_1890_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 1, v___x_1925_);
lean_ctor_set(v___x_1876_, 0, v_ref_1890_);
v___x_1927_ = v___x_1876_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_ref_1890_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1929_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1927_);
v___x_1929_ = v___x_1921_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
}
}
v___jp_1933_:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; 
v___x_1936_ = lean_unsigned_to_nat(3u);
v___x_1937_ = l_Lean_Syntax_getArg(v_stx_1874_, v___x_1936_);
v___x_1938_ = l_Lean_Syntax_isNone(v___x_1937_);
if (v___x_1938_ == 0)
{
uint8_t v___x_1939_; 
lean_inc(v___x_1937_);
v___x_1939_ = l_Lean_Syntax_matchesNull(v___x_1937_, v___y_1934_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
lean_dec(v___x_1937_);
lean_del_object(v___x_1876_);
lean_dec(v_stx_1874_);
v___x_1940_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
return v___x_1941_;
}
else
{
lean_object* v___x_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1942_ = l_Lean_Syntax_getArg(v___x_1937_, v___x_1882_);
lean_dec(v___x_1937_);
v___x_1943_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__8));
v___x_1944_ = l_Lean_Syntax_isOfKind(v___x_1942_, v___x_1943_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
lean_del_object(v___x_1876_);
lean_dec(v_stx_1874_);
v___x_1945_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
return v___x_1946_;
}
else
{
v___y_1884_ = v___y_1935_;
goto v___jp_1883_;
}
}
}
else
{
lean_dec(v___x_1937_);
v___y_1884_ = v___y_1935_;
goto v___jp_1883_;
}
}
v___jp_1947_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1949_ = lean_unsigned_to_nat(1u);
v___x_1950_ = l_Lean_Syntax_getArg(v_stx_1874_, v___x_1949_);
v___x_1951_ = l_Lean_Syntax_isNone(v___x_1950_);
if (v___x_1951_ == 0)
{
uint8_t v___x_1952_; 
lean_inc(v___x_1950_);
v___x_1952_ = l_Lean_Syntax_matchesNull(v___x_1950_, v___x_1949_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
lean_dec(v___x_1950_);
lean_del_object(v___x_1876_);
lean_dec(v_stx_1874_);
v___x_1953_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
return v___x_1954_;
}
else
{
lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v___x_1955_ = l_Lean_Syntax_getArg(v___x_1950_, v___x_1882_);
lean_dec(v___x_1950_);
v___x_1956_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__10));
v___x_1957_ = l_Lean_Syntax_isOfKind(v___x_1955_, v___x_1956_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
lean_del_object(v___x_1876_);
lean_dec(v_stx_1874_);
v___x_1958_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
return v___x_1959_;
}
else
{
v___y_1934_ = v___x_1949_;
v___y_1935_ = v___y_1948_;
goto v___jp_1933_;
}
}
}
else
{
lean_dec(v___x_1950_);
v___y_1934_ = v___x_1949_;
v___y_1935_ = v___y_1948_;
goto v___jp_1933_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_locationLinksFromImport___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1858_ = stack[0].m_obj;
lean_object* v_a_1859_ = stack[1].m_obj;
lean_object* v_a_1860_ = stack[2].m_obj;
lean_object* v_res_1973_;
v_res_1973_ = l_Lean_Server_locationLinksFromImport___redArg(v_i_1858_, v_a_1859_, v_a_1860_);
stack->m_obj
 = v_res_1973_;
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromImport___redArg___boxed(lean_object* v_i_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_Server_locationLinksFromImport___redArg(v_i_1974_, v_a_1975_, v_a_1976_);
lean_dec_ref(v_a_1976_);
lean_dec_ref(v_a_1975_);
return v_res_1978_;
}
}
lean_object* l_Lean_Server_locationLinksFromImport(lean_object* v_i_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_Server_locationLinksFromImport___redArg(v_i_1979_, v_a_1980_, v_a_1983_);
return v___x_1986_;
}
}
LEAN_EXPORT void l_Lean_Server_locationLinksFromImport_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1979_ = stack[0].m_obj;
lean_object* v_a_1980_ = stack[1].m_obj;
lean_object* v_a_1981_ = stack[2].m_obj;
lean_object* v_a_1982_ = stack[3].m_obj;
lean_object* v_a_1983_ = stack[4].m_obj;
lean_object* v_a_1984_ = stack[5].m_obj;
lean_object* v_res_1987_;
v_res_1987_ = l_Lean_Server_locationLinksFromImport(v_i_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
stack->m_obj
 = v_res_1987_;
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromImport___boxed(lean_object* v_i_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_Server_locationLinksFromImport(v_i_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
lean_dec(v_a_1993_);
lean_dec_ref(v_a_1992_);
lean_dec(v_a_1991_);
lean_dec_ref(v_a_1990_);
lean_dec_ref(v_a_1989_);
return v_res_1995_;
}
}
lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(lean_object* v_a_2015_, lean_object* v_a_2016_){
_start:
{
lean_object* v___x_2018_; lean_object* v_originInfo_x3f_2022_; 
v___x_2018_ = lean_st_ref_get(v_a_2016_);
v_originInfo_x3f_2022_ = lean_ctor_get(v_a_2015_, 2);
if (lean_obj_tag(v_originInfo_x3f_2022_) == 1)
{
uint8_t v_kind_2023_; lean_object* v_val_2024_; lean_object* v___x_2025_; 
v_kind_2023_ = lean_ctor_get_uint8(v_a_2015_, sizeof(void*)*4);
v_val_2024_ = lean_ctor_get(v_originInfo_x3f_2022_, 0);
lean_inc(v_val_2024_);
v___x_2025_ = l_Lean_Elab_Info_toElabInfo_x3f(v_val_2024_);
if (lean_obj_tag(v___x_2025_) == 1)
{
lean_object* v_val_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2063_; 
v_val_2026_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2063_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_val_2026_);
lean_dec(v___x_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2063_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v_elaborator_2030_; lean_object* v_stx_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v_elaborator_2030_ = lean_ctor_get(v_val_2026_, 0);
lean_inc(v_elaborator_2030_);
v_stx_2031_ = lean_ctor_get(v_val_2026_, 1);
lean_inc(v_stx_2031_);
lean_dec(v_val_2026_);
v___x_2032_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__2));
v___x_2033_ = lean_name_eq(v_elaborator_2030_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6));
v___x_2035_ = lean_name_eq(v_elaborator_2030_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8));
v___x_2037_ = lean_name_eq(v_elaborator_2030_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_object* v_env_2038_; uint8_t v___x_2039_; lean_object* v_names_2041_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
v_env_2038_ = lean_ctor_get(v___x_2018_, 0);
lean_inc_ref_n(v_env_2038_, 2);
lean_dec(v___x_2018_);
v___x_2039_ = 1;
v___x_2056_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
lean_inc(v_elaborator_2030_);
v___x_2057_ = l_Lean_Environment_contains(v_env_2038_, v_elaborator_2030_, v___x_2039_);
if (v___x_2057_ == 0)
{
lean_dec(v_elaborator_2030_);
v_names_2041_ = v___x_2056_;
goto v___jp_2040_;
}
else
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_array_push(v___x_2056_, v_elaborator_2030_);
v_names_2041_ = v___x_2058_;
goto v___jp_2040_;
}
v___jp_2040_:
{
uint8_t v___x_2042_; uint8_t v___x_2043_; 
v___x_2042_ = 0;
v___x_2043_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_2023_, v___x_2042_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2045_; 
lean_dec_ref(v_env_2038_);
lean_dec(v_stx_2031_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 0);
lean_ctor_set(v___x_2028_, 0, v_names_2041_);
v___x_2045_ = v___x_2028_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_names_2041_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
else
{
lean_object* v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = l_Lean_Syntax_getKind(v_stx_2031_);
lean_inc(v___x_2047_);
v___x_2048_ = l_Lean_Environment_contains(v_env_2038_, v___x_2047_, v___x_2039_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2050_; 
lean_dec(v___x_2047_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 0);
lean_ctor_set(v___x_2028_, 0, v_names_2041_);
v___x_2050_ = v___x_2028_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_names_2041_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2052_ = lean_array_push(v_names_2041_, v___x_2047_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2052_);
v___x_2054_ = v___x_2028_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
else
{
lean_dec(v_stx_2031_);
lean_dec(v_elaborator_2030_);
lean_del_object(v___x_2028_);
lean_dec(v___x_2018_);
goto v___jp_2019_;
}
}
else
{
lean_dec(v_stx_2031_);
lean_dec(v_elaborator_2030_);
lean_del_object(v___x_2028_);
lean_dec(v___x_2018_);
goto v___jp_2019_;
}
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2061_; 
lean_dec(v_stx_2031_);
lean_dec(v_elaborator_2030_);
lean_dec(v___x_2018_);
v___x_2059_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2059_);
v___x_2061_ = v___x_2028_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2059_);
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
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
lean_dec(v___x_2025_);
lean_dec(v___x_2018_);
v___x_2064_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
v___x_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
return v___x_2065_;
}
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
lean_dec(v___x_2018_);
v___x_2066_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
v___x_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
return v___x_2067_;
}
v___jp_2019_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
return v___x_2021_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2015_ = stack[0].m_obj;
lean_object* v_a_2016_ = stack[1].m_obj;
lean_object* v_res_2068_;
v_res_2068_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(v_a_2015_, v_a_2016_);
stack->m_obj
 = v_res_2068_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___boxed(lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(v_a_2069_, v_a_2070_);
lean_dec(v_a_2070_);
lean_dec_ref(v_a_2069_);
return v_res_2072_;
}
}
lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames(lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
lean_object* v___x_2079_; 
v___x_2079_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(v_a_2073_, v_a_2077_);
return v___x_2079_;
}
}
LEAN_EXPORT void l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2073_ = stack[0].m_obj;
lean_object* v_a_2074_ = stack[1].m_obj;
lean_object* v_a_2075_ = stack[2].m_obj;
lean_object* v_a_2076_ = stack[3].m_obj;
lean_object* v_a_2077_ = stack[4].m_obj;
lean_object* v_res_2080_;
v_res_2080_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames(v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
stack->m_obj
 = v_res_2080_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___boxed(lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames(v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec_ref(v_a_2081_);
return v_res_2087_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(lean_object* v_as_2088_, size_t v_sz_2089_, size_t v_i_2090_, lean_object* v_b_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
uint8_t v___x_2098_; 
v___x_2098_ = lean_usize_dec_lt(v_i_2090_, v_sz_2089_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; 
v___x_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2099_, 0, v_b_2091_);
return v___x_2099_;
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2101_; 
v_a_2100_ = lean_array_uget_borrowed(v_as_2088_, v_i_2090_);
lean_inc(v_a_2100_);
v___x_2101_ = l_Lean_Server_locationLinksFromDecl(v_a_2100_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2103_; size_t v___x_2104_; size_t v___x_2105_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2101_, 1);
v___x_2103_ = l_Array_append___redArg(v_b_2091_, v_a_2102_);
lean_dec(v_a_2102_);
v___x_2104_ = ((size_t)1ULL);
v___x_2105_ = lean_usize_add(v_i_2090_, v___x_2104_);
v_i_2090_ = v___x_2105_;
v_b_2091_ = v___x_2103_;
goto _start;
}
else
{
lean_dec_ref(v_b_2091_);
return v___x_2101_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2088_ = stack[0].m_obj;
size_t v_sz_2089_ = stack[1].m_num;
size_t v_i_2090_ = stack[2].m_num;
lean_object* v_b_2091_ = stack[3].m_obj;
lean_object* v___y_2092_ = stack[4].m_obj;
lean_object* v___y_2093_ = stack[5].m_obj;
lean_object* v___y_2094_ = stack[6].m_obj;
lean_object* v___y_2095_ = stack[7].m_obj;
lean_object* v___y_2096_ = stack[8].m_obj;
lean_object* v_res_2107_;
v_res_2107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_as_2088_, v_sz_2089_, v_i_2090_, v_b_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
stack->m_obj
 = v_res_2107_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0___boxed(lean_object* v_as_2108_, lean_object* v_sz_2109_, lean_object* v_i_2110_, lean_object* v_b_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
size_t v_sz_boxed_2118_; size_t v_i_boxed_2119_; lean_object* v_res_2120_; 
v_sz_boxed_2118_ = lean_unbox_usize(v_sz_2109_);
lean_dec(v_sz_2109_);
v_i_boxed_2119_ = lean_unbox_usize(v_i_2110_);
lean_dec(v_i_2110_);
v_res_2120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_as_2108_, v_sz_boxed_2118_, v_i_boxed_2119_, v_b_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec_ref(v_as_2108_);
return v_res_2120_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(size_t v_sz_2121_, size_t v_i_2122_, lean_object* v_bs_2123_){
_start:
{
uint8_t v___x_2124_; 
v___x_2124_ = lean_usize_dec_lt(v_i_2122_, v_sz_2121_);
if (v___x_2124_ == 0)
{
return v_bs_2123_;
}
else
{
lean_object* v_v_2125_; lean_object* v_toLocationLink_2126_; lean_object* v_ident_x3f_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2140_; 
v_v_2125_ = lean_array_uget(v_bs_2123_, v_i_2122_);
v_toLocationLink_2126_ = lean_ctor_get(v_v_2125_, 0);
v_ident_x3f_2127_ = lean_ctor_get(v_v_2125_, 1);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_v_2125_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2129_ = v_v_2125_;
v_isShared_2130_ = v_isSharedCheck_2140_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_ident_x3f_2127_);
lean_inc(v_toLocationLink_2126_);
lean_dec(v_v_2125_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2140_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2131_; lean_object* v_bs_x27_2132_; lean_object* v___x_2134_; 
v___x_2131_ = lean_unsigned_to_nat(0u);
v_bs_x27_2132_ = lean_array_uset(v_bs_2123_, v_i_2122_, v___x_2131_);
if (v_isShared_2130_ == 0)
{
v___x_2134_ = v___x_2129_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_toLocationLink_2126_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_ident_x3f_2127_);
v___x_2134_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
size_t v___x_2135_; size_t v___x_2136_; lean_object* v___x_2137_; 
lean_ctor_set_uint8(v___x_2134_, sizeof(void*)*2, v___x_2124_);
v___x_2135_ = ((size_t)1ULL);
v___x_2136_ = lean_usize_add(v_i_2122_, v___x_2135_);
v___x_2137_ = lean_array_uset(v_bs_x27_2132_, v_i_2122_, v___x_2134_);
v_i_2122_ = v___x_2136_;
v_bs_2123_ = v___x_2137_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2121_ = stack[0].m_num;
size_t v_i_2122_ = stack[1].m_num;
lean_object* v_bs_2123_ = stack[2].m_obj;
lean_object* v_res_2141_;
v_res_2141_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(v_sz_2121_, v_i_2122_, v_bs_2123_);
stack->m_obj
 = v_res_2141_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1___boxed(lean_object* v_sz_2142_, lean_object* v_i_2143_, lean_object* v_bs_2144_){
_start:
{
size_t v_sz_boxed_2145_; size_t v_i_boxed_2146_; lean_object* v_res_2147_; 
v_sz_boxed_2145_ = lean_unbox_usize(v_sz_2142_);
lean_dec(v_sz_2142_);
v_i_boxed_2146_ = lean_unbox_usize(v_i_2143_);
lean_dec(v_i_2143_);
v_res_2147_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(v_sz_boxed_2145_, v_i_boxed_2146_, v_bs_2144_);
return v_res_2147_;
}
}
lean_object* l_Lean_Server_locationLinksDefault(lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v___x_2154_; lean_object* v_a_2155_; lean_object* v___x_2156_; size_t v_sz_2157_; size_t v___x_2158_; lean_object* v___x_2159_; 
v___x_2154_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(v_a_2148_, v_a_2152_);
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref(v___x_2154_);
v___x_2156_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v_sz_2157_ = lean_array_size(v_a_2155_);
v___x_2158_ = ((size_t)0ULL);
v___x_2159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_a_2155_, v_sz_2157_, v___x_2158_, v___x_2156_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
lean_dec(v_a_2155_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2169_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2162_ = v___x_2159_;
v_isShared_2163_ = v_isSharedCheck_2169_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2159_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2169_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
size_t v_sz_2164_; lean_object* v___x_2165_; lean_object* v___x_2167_; 
v_sz_2164_ = lean_array_size(v_a_2160_);
v___x_2165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(v_sz_2164_, v___x_2158_, v_a_2160_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2165_);
v___x_2167_ = v___x_2162_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
else
{
return v___x_2159_;
}
}
}
LEAN_EXPORT void l_Lean_Server_locationLinksDefault_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2148_ = stack[0].m_obj;
lean_object* v_a_2149_ = stack[1].m_obj;
lean_object* v_a_2150_ = stack[2].m_obj;
lean_object* v_a_2151_ = stack[3].m_obj;
lean_object* v_a_2152_ = stack[4].m_obj;
lean_object* v_res_2170_;
v_res_2170_ = l_Lean_Server_locationLinksDefault(v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
stack->m_obj
 = v_res_2170_;
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksDefault___boxed(lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_Server_locationLinksDefault(v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
lean_dec(v_a_2175_);
lean_dec_ref(v_a_2174_);
lean_dec(v_a_2173_);
lean_dec_ref(v_a_2172_);
lean_dec_ref(v_a_2171_);
return v_res_2177_;
}
}
lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(lean_object* v_name_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v_env_2183_; lean_object* v___x_2184_; lean_object* v_toEnvExtension_2185_; lean_object* v_asyncMode_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2181_ = lean_box(1);
v___x_2182_ = lean_st_ref_get(v___y_2179_);
v_env_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc_ref(v_env_2183_);
lean_dec(v___x_2182_);
v___x_2184_ = l_Lean_errorExplanationExt;
v_toEnvExtension_2185_ = lean_ctor_get(v___x_2184_, 0);
v_asyncMode_2186_ = lean_ctor_get(v_toEnvExtension_2185_, 2);
v___x_2187_ = lean_box(0);
v___x_2188_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2181_, v___x_2184_, v_env_2183_, v_asyncMode_2186_, v___x_2187_);
v___x_2189_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2188_, v_name_2178_);
lean_dec(v___x_2188_);
v___x_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT void l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2178_ = stack[0].m_obj;
lean_object* v___y_2179_ = stack[1].m_obj;
lean_object* v_res_2191_;
v_res_2191_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_name_2178_, v___y_2179_);
stack->m_obj
 = v_res_2191_;
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg___boxed(lean_object* v_name_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_name_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec(v_name_2192_);
return v_res_2195_;
}
}
lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0(lean_object* v_name_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_name_2196_, v___y_2201_);
return v___x_2203_;
}
}
LEAN_EXPORT void l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2196_ = stack[0].m_obj;
lean_object* v___y_2197_ = stack[1].m_obj;
lean_object* v___y_2198_ = stack[2].m_obj;
lean_object* v___y_2199_ = stack[3].m_obj;
lean_object* v___y_2200_ = stack[4].m_obj;
lean_object* v___y_2201_ = stack[5].m_obj;
lean_object* v_res_2204_;
v_res_2204_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0(v_name_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
stack->m_obj
 = v_res_2204_;
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___boxed(lean_object* v_name_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0(v_name_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v_name_2205_);
return v_res_2212_;
}
}
lean_object* l_Lean_Server_locationLinksFromErrorNameInfo(lean_object* v_eni_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v_stx_2220_; lean_object* v_errorName_2221_; lean_object* v___x_2222_; lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2303_; 
v_stx_2220_ = lean_ctor_get(v_eni_2213_, 0);
v_errorName_2221_ = lean_ctor_get(v_eni_2213_, 1);
v___x_2222_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_errorName_2221_, v_a_2218_);
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2225_ = v___x_2222_;
v_isShared_2226_ = v_isSharedCheck_2303_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2222_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2303_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
if (lean_obj_tag(v_a_2223_) == 1)
{
lean_object* v_val_2227_; lean_object* v_declLoc_x3f_2228_; 
v_val_2227_ = lean_ctor_get(v_a_2223_, 0);
lean_inc(v_val_2227_);
lean_dec_ref_known(v_a_2223_, 1);
v_declLoc_x3f_2228_ = lean_ctor_get(v_val_2227_, 2);
lean_inc(v_declLoc_x3f_2228_);
lean_dec(v_val_2227_);
if (lean_obj_tag(v_declLoc_x3f_2228_) == 1)
{
lean_object* v_val_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2294_; 
lean_del_object(v___x_2225_);
v_val_2229_ = lean_ctor_get(v_declLoc_x3f_2228_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v_declLoc_x3f_2228_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2231_ = v_declLoc_x3f_2228_;
v_isShared_2232_ = v_isSharedCheck_2294_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_val_2229_);
lean_dec(v_declLoc_x3f_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2294_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v_module_2233_; lean_object* v_range_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2293_; 
v_module_2233_ = lean_ctor_get(v_val_2229_, 0);
v_range_2234_ = lean_ctor_get(v_val_2229_, 1);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_val_2229_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2236_ = v_val_2229_;
v_isShared_2237_ = v_isSharedCheck_2293_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_range_2234_);
lean_inc(v_module_2233_);
lean_dec(v_val_2229_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2293_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v_ref_2238_; lean_object* v___x_2239_; 
v_ref_2238_ = lean_ctor_get(v_a_2217_, 2);
v___x_2239_ = l_Lean_Server_documentUriFromModule_x3f(v_module_2233_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2276_; 
lean_del_object(v___x_2236_);
lean_del_object(v___x_2231_);
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2242_ = v___x_2239_;
v_isShared_2243_ = v_isSharedCheck_2276_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2239_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2276_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
if (lean_obj_tag(v_a_2240_) == 1)
{
lean_object* v_val_2244_; lean_object* v___x_2245_; lean_object* v___y_2247_; uint8_t v___x_2258_; lean_object* v___x_2259_; 
v_val_2244_ = lean_ctor_get(v_a_2240_, 0);
lean_inc(v_val_2244_);
lean_dec_ref_known(v_a_2240_, 1);
v___x_2245_ = l_Lean_DeclarationRange_toLspRange(v_range_2234_);
v___x_2258_ = 1;
v___x_2259_ = l_Lean_Syntax_getRange_x3f(v_stx_2220_, v___x_2258_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v___x_2260_; 
v___x_2260_ = lean_box(0);
v___y_2247_ = v___x_2260_;
goto v___jp_2246_;
}
else
{
lean_object* v_doc_2261_; lean_object* v_val_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2271_; 
v_doc_2261_ = lean_ctor_get(v_a_2214_, 0);
v_val_2262_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2264_ = v___x_2259_;
v_isShared_2265_ = v_isSharedCheck_2271_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_val_2262_);
lean_dec(v___x_2259_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2271_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v_text_2266_; lean_object* v___x_2267_; lean_object* v___x_2269_; 
v_text_2266_ = lean_ctor_get(v_doc_2261_, 3);
lean_inc_ref(v_text_2266_);
v___x_2267_ = l_Lean_Syntax_Range_toLspRange(v_text_2266_, v_val_2262_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2267_);
v___x_2269_ = v___x_2264_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
v___y_2247_ = v___x_2269_;
goto v___jp_2246_;
}
}
}
v___jp_2246_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; uint8_t v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2256_; 
lean_inc_ref(v___x_2245_);
v___x_2248_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2248_, 0, v___y_2247_);
lean_ctor_set(v___x_2248_, 1, v_val_2244_);
lean_ctor_set(v___x_2248_, 2, v___x_2245_);
lean_ctor_set(v___x_2248_, 3, v___x_2245_);
v___x_2249_ = lean_box(0);
v___x_2250_ = 0;
v___x_2251_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2251_, 0, v___x_2248_);
lean_ctor_set(v___x_2251_, 1, v___x_2249_);
lean_ctor_set_uint8(v___x_2251_, sizeof(void*)*2, v___x_2250_);
v___x_2252_ = lean_unsigned_to_nat(1u);
v___x_2253_ = lean_mk_empty_array_with_capacity(v___x_2252_);
v___x_2254_ = lean_array_push(v___x_2253_, v___x_2251_);
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 0, v___x_2254_);
v___x_2256_ = v___x_2242_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2274_; 
lean_dec(v_a_2240_);
lean_dec_ref(v_range_2234_);
v___x_2272_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 0, v___x_2272_);
v___x_2274_ = v___x_2242_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2292_; 
lean_dec_ref(v_range_2234_);
v_a_2277_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2279_ = v___x_2239_;
v_isShared_2280_ = v_isSharedCheck_2292_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2239_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2292_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2281_ = lean_io_error_to_string(v_a_2277_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set_tag(v___x_2231_, 3);
lean_ctor_set(v___x_2231_, 0, v___x_2281_);
v___x_2283_ = v___x_2231_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2284_; lean_object* v___x_2286_; 
v___x_2284_ = l_Lean_MessageData_ofFormat(v___x_2283_);
lean_inc(v_ref_2238_);
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 1, v___x_2284_);
lean_ctor_set(v___x_2236_, 0, v_ref_2238_);
v___x_2286_ = v___x_2236_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_ref_2238_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
lean_object* v___x_2288_; 
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2286_);
v___x_2288_ = v___x_2279_;
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
}
}
}
}
else
{
lean_object* v___x_2295_; lean_object* v___x_2297_; 
lean_dec(v_declLoc_x3f_2228_);
v___x_2295_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2295_);
v___x_2297_ = v___x_2225_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
else
{
lean_object* v___x_2299_; lean_object* v___x_2301_; 
lean_dec(v_a_2223_);
v___x_2299_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2299_);
v___x_2301_ = v___x_2225_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2299_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_locationLinksFromErrorNameInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_eni_2213_ = stack[0].m_obj;
lean_object* v_a_2214_ = stack[1].m_obj;
lean_object* v_a_2215_ = stack[2].m_obj;
lean_object* v_a_2216_ = stack[3].m_obj;
lean_object* v_a_2217_ = stack[4].m_obj;
lean_object* v_a_2218_ = stack[5].m_obj;
lean_object* v_res_2304_;
v_res_2304_ = l_Lean_Server_locationLinksFromErrorNameInfo(v_eni_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
stack->m_obj
 = v_res_2304_;
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromErrorNameInfo___boxed(lean_object* v_eni_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_Server_locationLinksFromErrorNameInfo(v_eni_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
lean_dec_ref(v_a_2306_);
lean_dec_ref(v_eni_2305_);
return v_res_2312_;
}
}
lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(lean_object* v_e_2313_, lean_object* v_a_2314_){
_start:
{
switch(lean_obj_tag(v_e_2313_))
{
case 4:
{
lean_object* v_declName_2316_; lean_object* v___x_2317_; 
v_declName_2316_ = lean_ctor_get(v_e_2313_, 0);
lean_inc(v_declName_2316_);
lean_dec_ref_known(v_e_2313_, 2);
v___x_2317_ = l_Lean_Meta_isInstance___redArg(v_declName_2316_, v_a_2314_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2333_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2333_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2333_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
uint8_t v___x_2322_; 
v___x_2322_ = lean_unbox(v_a_2318_);
lean_dec(v_a_2318_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; lean_object* v___x_2325_; 
lean_dec(v_declName_2316_);
v___x_2323_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v___x_2323_);
v___x_2325_ = v___x_2320_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2327_ = lean_unsigned_to_nat(1u);
v___x_2328_ = lean_mk_empty_array_with_capacity(v___x_2327_);
v___x_2329_ = lean_array_push(v___x_2328_, v_declName_2316_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v___x_2329_);
v___x_2331_ = v___x_2320_;
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
lean_dec(v_declName_2316_);
v_a_2334_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2317_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2317_);
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
case 5:
{
lean_object* v_fn_2342_; lean_object* v_arg_2343_; lean_object* v___x_2344_; 
v_fn_2342_ = lean_ctor_get(v_e_2313_, 0);
lean_inc_ref(v_fn_2342_);
v_arg_2343_ = lean_ctor_get(v_e_2313_, 1);
lean_inc_ref(v_arg_2343_);
lean_dec_ref_known(v_e_2313_, 2);
v___x_2344_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_fn_2342_, v_a_2314_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2346_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2345_);
lean_dec_ref_known(v___x_2344_, 1);
v___x_2346_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_arg_2343_, v_a_2314_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2355_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2349_ = v___x_2346_;
v_isShared_2350_ = v_isSharedCheck_2355_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2346_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2355_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___x_2351_ = l_Array_append___redArg(v_a_2347_, v_a_2345_);
lean_dec(v_a_2345_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v___x_2351_);
v___x_2353_ = v___x_2349_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
else
{
lean_dec(v_a_2345_);
return v___x_2346_;
}
}
else
{
lean_dec_ref(v_arg_2343_);
return v___x_2344_;
}
}
case 10:
{
lean_object* v_expr_2356_; 
v_expr_2356_ = lean_ctor_get(v_e_2313_, 1);
lean_inc_ref(v_expr_2356_);
lean_dec_ref_known(v_e_2313_, 2);
v_e_2313_ = v_expr_2356_;
goto _start;
}
default: 
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_dec_ref(v_e_2313_);
v___x_2358_ = ((lean_object*)(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0));
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
return v___x_2359_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2313_ = stack[0].m_obj;
lean_object* v_a_2314_ = stack[1].m_obj;
lean_object* v_res_2360_;
v_res_2360_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_e_2313_, v_a_2314_);
stack->m_obj
 = v_res_2360_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg___boxed(lean_object* v_e_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_e_2361_, v_a_2362_);
lean_dec(v_a_2362_);
return v_res_2364_;
}
}
lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances(lean_object* v_e_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_e_2365_, v_a_2370_);
return v___x_2372_;
}
}
LEAN_EXPORT void l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2365_ = stack[0].m_obj;
lean_object* v_a_2366_ = stack[1].m_obj;
lean_object* v_a_2367_ = stack[2].m_obj;
lean_object* v_a_2368_ = stack[3].m_obj;
lean_object* v_a_2369_ = stack[4].m_obj;
lean_object* v_a_2370_ = stack[5].m_obj;
lean_object* v_res_2373_;
v_res_2373_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances(v_e_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
stack->m_obj
 = v_res_2373_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___boxed(lean_object* v_e_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances(v_e_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
lean_dec_ref(v_a_2375_);
return v_res_2381_;
}
}
lean_object* l_Lean_Server_locationLinksFromInstanceProjection(lean_object* v_e_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = l_Lean_Expr_getAppFn(v_e_2382_);
v___x_2390_ = l_Lean_Expr_consumeMData(v___x_2389_);
lean_dec_ref(v___x_2389_);
if (lean_obj_tag(v___x_2390_) == 4)
{
lean_object* v_declName_2391_; lean_object* v___x_2392_; 
v_declName_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_declName_2391_);
lean_dec_ref_known(v___x_2390_, 2);
v___x_2392_ = l_Lean_Server_getInstanceProjectionArg_x3f(v_e_2382_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2427_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2395_ = v___x_2392_;
v_isShared_2396_ = v_isSharedCheck_2427_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2427_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
if (lean_obj_tag(v_a_2393_) == 1)
{
lean_object* v_val_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
lean_del_object(v___x_2395_);
v_val_2397_ = lean_ctor_get(v_a_2393_, 0);
lean_inc(v_val_2397_);
lean_dec_ref_known(v_a_2393_, 1);
v___x_2398_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_2399_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_val_2397_, v_a_2387_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; size_t v_sz_2401_; size_t v___x_2402_; lean_object* v___x_2403_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2400_);
lean_dec_ref_known(v___x_2399_, 1);
v_sz_2401_ = lean_array_size(v_a_2400_);
v___x_2402_ = ((size_t)0ULL);
v___x_2403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_a_2400_, v_sz_2401_, v___x_2402_, v___x_2398_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
lean_dec(v_a_2400_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v___x_2405_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref_known(v___x_2403_, 1);
v___x_2405_ = l_Lean_Server_locationLinksFromDecl(v_declName_2391_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2414_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2408_ = v___x_2405_;
v_isShared_2409_ = v_isSharedCheck_2414_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2405_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2414_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2410_; lean_object* v___x_2412_; 
v___x_2410_ = l_Array_append___redArg(v_a_2404_, v_a_2406_);
lean_dec(v_a_2406_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v___x_2410_);
v___x_2412_ = v___x_2408_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2410_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
else
{
lean_dec(v_a_2404_);
return v___x_2405_;
}
}
else
{
lean_dec(v_declName_2391_);
return v___x_2403_;
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_dec(v_declName_2391_);
v_a_2415_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2399_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2399_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
else
{
lean_object* v___x_2423_; lean_object* v___x_2425_; 
lean_dec(v_a_2393_);
lean_dec(v_declName_2391_);
v___x_2423_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2423_);
v___x_2425_ = v___x_2395_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v_declName_2391_);
v_a_2428_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2392_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2392_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
else
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
lean_dec_ref(v___x_2390_);
lean_dec_ref(v_e_2382_);
v___x_2436_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
return v___x_2437_;
}
}
}
LEAN_EXPORT void l_Lean_Server_locationLinksFromInstanceProjection_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2382_ = stack[0].m_obj;
lean_object* v_a_2383_ = stack[1].m_obj;
lean_object* v_a_2384_ = stack[2].m_obj;
lean_object* v_a_2385_ = stack[3].m_obj;
lean_object* v_a_2386_ = stack[4].m_obj;
lean_object* v_a_2387_ = stack[5].m_obj;
lean_object* v_res_2438_;
v_res_2438_ = l_Lean_Server_locationLinksFromInstanceProjection(v_e_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
stack->m_obj
 = v_res_2438_;
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromInstanceProjection___boxed(lean_object* v_e_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_Server_locationLinksFromInstanceProjection(v_e_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec_ref(v_a_2440_);
return v_res_2446_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(lean_object* v_as_2447_, size_t v_sz_2448_, size_t v_i_2449_, lean_object* v_b_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v_newLL_2458_; uint8_t v___x_2463_; 
v___x_2463_ = lean_usize_dec_lt(v_i_2449_, v_sz_2448_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2464_, 0, v_b_2450_);
return v___x_2464_;
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2466_; 
v_a_2465_ = lean_array_uget_borrowed(v_as_2447_, v_i_2449_);
v___x_2466_ = l_Lean_Expr_consumeMData(v_a_2465_);
switch(lean_obj_tag(v___x_2466_))
{
case 4:
{
lean_object* v_declName_2467_; lean_object* v___x_2468_; 
v_declName_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_declName_2467_);
lean_dec_ref_known(v___x_2466_, 2);
v___x_2468_ = l_Lean_Server_locationLinksFromDecl(v_declName_2467_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v___x_2468_, 1);
v_newLL_2458_ = v_a_2469_;
goto v___jp_2457_;
}
else
{
lean_dec_ref(v_b_2450_);
return v___x_2468_;
}
}
case 1:
{
lean_object* v_fvarId_2470_; lean_object* v___x_2471_; 
v_fvarId_2470_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_fvarId_2470_);
lean_dec_ref_known(v___x_2466_, 1);
v___x_2471_ = l_Lean_Server_locationLinksFromBinder___redArg(v_fvarId_2470_, v___y_2451_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref_known(v___x_2471_, 1);
v_newLL_2458_ = v_a_2472_;
goto v___jp_2457_;
}
else
{
lean_dec_ref(v_b_2450_);
return v___x_2471_;
}
}
default: 
{
lean_object* v___x_2473_; 
lean_dec_ref(v___x_2466_);
lean_inc(v_a_2465_);
v___x_2473_ = l_Lean_Server_locationLinksFromInstanceProjection(v_a_2465_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2474_);
lean_dec_ref_known(v___x_2473_, 1);
v_newLL_2458_ = v_a_2474_;
goto v___jp_2457_;
}
else
{
lean_dec_ref(v_b_2450_);
return v___x_2473_;
}
}
}
}
v___jp_2457_:
{
lean_object* v___x_2459_; size_t v___x_2460_; size_t v___x_2461_; 
v___x_2459_ = l_Array_append___redArg(v_b_2450_, v_newLL_2458_);
lean_dec_ref(v_newLL_2458_);
v___x_2460_ = ((size_t)1ULL);
v___x_2461_ = lean_usize_add(v_i_2449_, v___x_2460_);
v_i_2449_ = v___x_2461_;
v_b_2450_ = v___x_2459_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2447_ = stack[0].m_obj;
size_t v_sz_2448_ = stack[1].m_num;
size_t v_i_2449_ = stack[2].m_num;
lean_object* v_b_2450_ = stack[3].m_obj;
lean_object* v___y_2451_ = stack[4].m_obj;
lean_object* v___y_2452_ = stack[5].m_obj;
lean_object* v___y_2453_ = stack[6].m_obj;
lean_object* v___y_2454_ = stack[7].m_obj;
lean_object* v___y_2455_ = stack[8].m_obj;
lean_object* v_res_2475_;
v_res_2475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(v_as_2447_, v_sz_2448_, v_i_2449_, v_b_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
stack->m_obj
 = v_res_2475_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0___boxed(lean_object* v_as_2476_, lean_object* v_sz_2477_, lean_object* v_i_2478_, lean_object* v_b_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
size_t v_sz_boxed_2486_; size_t v_i_boxed_2487_; lean_object* v_res_2488_; 
v_sz_boxed_2486_ = lean_unbox_usize(v_sz_2477_);
lean_dec(v_sz_2477_);
v_i_boxed_2487_ = lean_unbox_usize(v_i_2478_);
lean_dec(v_i_2478_);
v_res_2488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(v_as_2476_, v_sz_boxed_2486_, v_i_boxed_2487_, v_b_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec_ref(v_as_2476_);
return v_res_2488_;
}
}
lean_object* l_Lean_Server_locationLinksFromTermInfo(lean_object* v_ti_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_){
_start:
{
uint8_t v_kind_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v_kind_2496_ = lean_ctor_get_uint8(v_a_2490_, sizeof(void*)*4);
v___x_2497_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_2498_ = l_Lean_Server_GoToKind_determineTargetExprs(v_kind_2496_, v_ti_2489_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; size_t v_sz_2500_; size_t v___x_2501_; lean_object* v___x_2502_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___x_2498_, 1);
v_sz_2500_ = lean_array_size(v_a_2499_);
v___x_2501_ = ((size_t)0ULL);
v___x_2502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(v_a_2499_, v_sz_2500_, v___x_2501_, v___x_2497_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
lean_dec(v_a_2499_);
return v___x_2502_;
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
v_a_2503_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2498_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2498_);
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
LEAN_EXPORT void l_Lean_Server_locationLinksFromTermInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_ti_2489_ = stack[0].m_obj;
lean_object* v_a_2490_ = stack[1].m_obj;
lean_object* v_a_2491_ = stack[2].m_obj;
lean_object* v_a_2492_ = stack[3].m_obj;
lean_object* v_a_2493_ = stack[4].m_obj;
lean_object* v_a_2494_ = stack[5].m_obj;
lean_object* v_res_2511_;
v_res_2511_ = l_Lean_Server_locationLinksFromTermInfo(v_ti_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
stack->m_obj
 = v_res_2511_;
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromTermInfo___boxed(lean_object* v_ti_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_Server_locationLinksFromTermInfo(v_ti_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec_ref(v_a_2513_);
return v_res_2519_;
}
}
lean_object* l_Lean_Server_locationLinksFromDelabTermInfo(lean_object* v_dti_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
lean_object* v_location_x3f_2527_; 
v_location_x3f_2527_ = lean_ctor_get(v_dti_2520_, 1);
lean_inc(v_location_x3f_2527_);
if (lean_obj_tag(v_location_x3f_2527_) == 1)
{
lean_object* v_val_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2597_; 
v_val_2528_ = lean_ctor_get(v_location_x3f_2527_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_location_x3f_2527_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2530_ = v_location_x3f_2527_;
v_isShared_2531_ = v_isSharedCheck_2597_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_val_2528_);
lean_dec(v_location_x3f_2527_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2597_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v_toTermInfo_2532_; lean_object* v_module_2533_; lean_object* v_range_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2596_; 
v_toTermInfo_2532_ = lean_ctor_get(v_dti_2520_, 0);
v_module_2533_ = lean_ctor_get(v_val_2528_, 0);
v_range_2534_ = lean_ctor_get(v_val_2528_, 1);
v_isSharedCheck_2596_ = !lean_is_exclusive(v_val_2528_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2536_ = v_val_2528_;
v_isShared_2537_ = v_isSharedCheck_2596_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_range_2534_);
lean_inc(v_module_2533_);
lean_dec(v_val_2528_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2596_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v_ref_2538_; lean_object* v___x_2539_; 
v_ref_2538_ = lean_ctor_get(v_a_2524_, 2);
v___x_2539_ = l_Lean_Server_documentUriFromModule_x3f(v_module_2533_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2579_; 
lean_del_object(v___x_2536_);
lean_del_object(v___x_2530_);
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2542_ = v___x_2539_;
v_isShared_2543_ = v_isSharedCheck_2579_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2539_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2579_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
if (lean_obj_tag(v_a_2540_) == 1)
{
lean_object* v_val_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2577_; 
v_val_2544_ = lean_ctor_get(v_a_2540_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v_a_2540_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2546_ = v_a_2540_;
v_isShared_2547_ = v_isSharedCheck_2577_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_val_2544_);
lean_dec(v_a_2540_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2577_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2548_; lean_object* v___y_2550_; lean_object* v___x_2562_; 
v___x_2548_ = l_Lean_DeclarationRange_toLspRange(v_range_2534_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set_tag(v___x_2546_, 13);
lean_ctor_set(v___x_2546_, 0, v_dti_2520_);
v___x_2562_ = v___x_2546_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_dti_2520_);
v___x_2562_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2561_;
}
v___jp_2549_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2559_; 
lean_inc_ref(v___x_2548_);
v___x_2551_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2551_, 0, v___y_2550_);
lean_ctor_set(v___x_2551_, 1, v_val_2544_);
lean_ctor_set(v___x_2551_, 2, v___x_2548_);
lean_ctor_set(v___x_2551_, 3, v___x_2548_);
v___x_2552_ = lean_box(0);
v___x_2553_ = 0;
v___x_2554_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2554_, 0, v___x_2551_);
lean_ctor_set(v___x_2554_, 1, v___x_2552_);
lean_ctor_set_uint8(v___x_2554_, sizeof(void*)*2, v___x_2553_);
v___x_2555_ = lean_unsigned_to_nat(1u);
v___x_2556_ = lean_mk_empty_array_with_capacity(v___x_2555_);
v___x_2557_ = lean_array_push(v___x_2556_, v___x_2554_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v___x_2557_);
v___x_2559_ = v___x_2542_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
v_reusejp_2561_:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_Elab_Info_range_x3f(v___x_2562_);
lean_dec_ref(v___x_2562_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v___x_2564_; 
v___x_2564_ = lean_box(0);
v___y_2550_ = v___x_2564_;
goto v___jp_2549_;
}
else
{
lean_object* v_doc_2565_; lean_object* v_val_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2575_; 
v_doc_2565_ = lean_ctor_get(v_a_2521_, 0);
v_val_2566_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2568_ = v___x_2563_;
v_isShared_2569_ = v_isSharedCheck_2575_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_val_2566_);
lean_dec(v___x_2563_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2575_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_text_2570_; lean_object* v___x_2571_; lean_object* v___x_2573_; 
v_text_2570_ = lean_ctor_get(v_doc_2565_, 3);
lean_inc_ref(v_text_2570_);
v___x_2571_ = l_Lean_Syntax_Range_toLspRange(v_text_2570_, v_val_2566_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2571_);
v___x_2573_ = v___x_2568_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2571_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
v___y_2550_ = v___x_2573_;
goto v___jp_2549_;
}
}
}
}
}
}
else
{
lean_object* v___x_2578_; 
lean_inc_ref(v_toTermInfo_2532_);
lean_del_object(v___x_2542_);
lean_dec(v_a_2540_);
lean_dec_ref(v_range_2534_);
lean_dec_ref(v_dti_2520_);
v___x_2578_ = l_Lean_Server_locationLinksFromTermInfo(v_toTermInfo_2532_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
return v___x_2578_;
}
}
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2595_; 
lean_dec_ref(v_range_2534_);
lean_dec_ref(v_dti_2520_);
v_a_2580_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2582_ = v___x_2539_;
v_isShared_2583_ = v_isSharedCheck_2595_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2539_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2595_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2584_ = lean_io_error_to_string(v_a_2580_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set_tag(v___x_2530_, 3);
lean_ctor_set(v___x_2530_, 0, v___x_2584_);
v___x_2586_ = v___x_2530_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
lean_object* v___x_2587_; lean_object* v___x_2589_; 
v___x_2587_ = l_Lean_MessageData_ofFormat(v___x_2586_);
lean_inc(v_ref_2538_);
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 1, v___x_2587_);
lean_ctor_set(v___x_2536_, 0, v_ref_2538_);
v___x_2589_ = v___x_2536_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_ref_2538_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2591_; 
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 0, v___x_2589_);
v___x_2591_ = v___x_2582_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
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
lean_object* v_toTermInfo_2598_; lean_object* v___x_2599_; 
lean_dec(v_location_x3f_2527_);
v_toTermInfo_2598_ = lean_ctor_get(v_dti_2520_, 0);
lean_inc_ref(v_toTermInfo_2598_);
lean_dec_ref(v_dti_2520_);
v___x_2599_ = l_Lean_Server_locationLinksFromTermInfo(v_toTermInfo_2598_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
return v___x_2599_;
}
}
}
LEAN_EXPORT void l_Lean_Server_locationLinksFromDelabTermInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_dti_2520_ = stack[0].m_obj;
lean_object* v_a_2521_ = stack[1].m_obj;
lean_object* v_a_2522_ = stack[2].m_obj;
lean_object* v_a_2523_ = stack[3].m_obj;
lean_object* v_a_2524_ = stack[4].m_obj;
lean_object* v_a_2525_ = stack[5].m_obj;
lean_object* v_res_2600_;
v_res_2600_ = l_Lean_Server_locationLinksFromDelabTermInfo(v_dti_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
stack->m_obj
 = v_res_2600_;
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromDelabTermInfo___boxed(lean_object* v_dti_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Lean_Server_locationLinksFromDelabTermInfo(v_dti_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_);
lean_dec(v_a_2606_);
lean_dec_ref(v_a_2605_);
lean_dec(v_a_2604_);
lean_dec_ref(v_a_2603_);
lean_dec_ref(v_a_2602_);
return v_res_2608_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(lean_object* v_e_2609_, lean_object* v___y_2610_){
_start:
{
uint8_t v___x_2612_; 
v___x_2612_ = l_Lean_Expr_hasMVar(v_e_2609_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; 
v___x_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2613_, 0, v_e_2609_);
return v___x_2613_;
}
else
{
lean_object* v___x_2614_; lean_object* v_mctx_2615_; lean_object* v___x_2616_; lean_object* v_fst_2617_; lean_object* v_snd_2618_; lean_object* v___x_2619_; lean_object* v_cache_2620_; lean_object* v_zetaDeltaFVarIds_2621_; lean_object* v_postponed_2622_; lean_object* v_diag_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2632_; 
v___x_2614_ = lean_st_ref_get(v___y_2610_);
v_mctx_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc_ref(v_mctx_2615_);
lean_dec(v___x_2614_);
v___x_2616_ = l_Lean_instantiateMVarsCore(v_mctx_2615_, v_e_2609_);
v_fst_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_fst_2617_);
v_snd_2618_ = lean_ctor_get(v___x_2616_, 1);
lean_inc(v_snd_2618_);
lean_dec_ref(v___x_2616_);
v___x_2619_ = lean_st_ref_take(v___y_2610_);
v_cache_2620_ = lean_ctor_get(v___x_2619_, 1);
v_zetaDeltaFVarIds_2621_ = lean_ctor_get(v___x_2619_, 2);
v_postponed_2622_ = lean_ctor_get(v___x_2619_, 3);
v_diag_2623_ = lean_ctor_get(v___x_2619_, 4);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2632_ == 0)
{
lean_object* v_unused_2633_; 
v_unused_2633_ = lean_ctor_get(v___x_2619_, 0);
lean_dec(v_unused_2633_);
v___x_2625_ = v___x_2619_;
v_isShared_2626_ = v_isSharedCheck_2632_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_diag_2623_);
lean_inc(v_postponed_2622_);
lean_inc(v_zetaDeltaFVarIds_2621_);
lean_inc(v_cache_2620_);
lean_dec(v___x_2619_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2632_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v_snd_2618_);
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_snd_2618_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v_cache_2620_);
lean_ctor_set(v_reuseFailAlloc_2631_, 2, v_zetaDeltaFVarIds_2621_);
lean_ctor_set(v_reuseFailAlloc_2631_, 3, v_postponed_2622_);
lean_ctor_set(v_reuseFailAlloc_2631_, 4, v_diag_2623_);
v___x_2628_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2629_ = lean_st_ref_put(v___y_2610_, v___x_2628_);
v___x_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2630_, 0, v_fst_2617_);
return v___x_2630_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2609_ = stack[0].m_obj;
lean_object* v___y_2610_ = stack[1].m_obj;
lean_object* v_res_2634_;
v_res_2634_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(v_e_2609_, v___y_2610_);
stack->m_obj
 = v_res_2634_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg___boxed(lean_object* v_e_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(v_e_2635_, v___y_2636_);
lean_dec(v___y_2636_);
return v_res_2638_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0(lean_object* v_e_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(v_e_2639_, v___y_2642_);
return v___x_2646_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2639_ = stack[0].m_obj;
lean_object* v___y_2640_ = stack[1].m_obj;
lean_object* v___y_2641_ = stack[2].m_obj;
lean_object* v___y_2642_ = stack[3].m_obj;
lean_object* v___y_2643_ = stack[4].m_obj;
lean_object* v___y_2644_ = stack[5].m_obj;
lean_object* v_res_2647_;
v_res_2647_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0(v_e_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
stack->m_obj
 = v_res_2647_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___boxed(lean_object* v_e_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0(v_e_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec_ref(v___y_2649_);
return v_res_2655_;
}
}
lean_object* l_Lean_Server_locationLinksFromFieldInfo(lean_object* v_fi_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
uint8_t v_kind_2663_; uint8_t v___x_2664_; uint8_t v___x_2665_; 
v_kind_2663_ = lean_ctor_get_uint8(v_a_2657_, sizeof(void*)*4);
v___x_2664_ = 2;
v___x_2665_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_2663_, v___x_2664_);
if (v___x_2665_ == 0)
{
lean_object* v_projName_2666_; lean_object* v___x_2667_; 
v_projName_2666_ = lean_ctor_get(v_fi_2656_, 0);
lean_inc(v_projName_2666_);
lean_dec_ref(v_fi_2656_);
v___x_2667_ = l_Lean_Server_locationLinksFromDecl(v_projName_2666_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
return v___x_2667_;
}
else
{
lean_object* v_val_2668_; lean_object* v___x_2669_; 
v_val_2668_ = lean_ctor_get(v_fi_2656_, 3);
lean_inc_ref(v_val_2668_);
lean_dec_ref(v_fi_2656_);
lean_inc(v_a_2661_);
lean_inc_ref(v_a_2660_);
lean_inc(v_a_2659_);
lean_inc_ref(v_a_2658_);
v___x_2669_ = lean_infer_type(v_val_2668_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2671_; lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2684_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___x_2669_, 1);
v___x_2671_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(v_a_2670_, v_a_2659_);
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2684_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2684_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2676_ = l_Lean_Expr_getAppFn(v_a_2672_);
lean_dec(v_a_2672_);
v___x_2677_ = l_Lean_Expr_constName_x3f(v___x_2676_);
lean_dec_ref(v___x_2676_);
if (lean_obj_tag(v___x_2677_) == 1)
{
lean_object* v_val_2678_; lean_object* v___x_2679_; 
lean_del_object(v___x_2674_);
v_val_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_val_2678_);
lean_dec_ref_known(v___x_2677_, 1);
v___x_2679_ = l_Lean_Server_locationLinksFromDecl(v_val_2678_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
return v___x_2679_;
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2682_; 
lean_dec(v___x_2677_);
v___x_2680_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2680_);
v___x_2682_ = v___x_2674_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
v_a_2685_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2669_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2669_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_locationLinksFromFieldInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_fi_2656_ = stack[0].m_obj;
lean_object* v_a_2657_ = stack[1].m_obj;
lean_object* v_a_2658_ = stack[2].m_obj;
lean_object* v_a_2659_ = stack[3].m_obj;
lean_object* v_a_2660_ = stack[4].m_obj;
lean_object* v_a_2661_ = stack[5].m_obj;
lean_object* v_res_2693_;
v_res_2693_ = l_Lean_Server_locationLinksFromFieldInfo(v_fi_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
stack->m_obj
 = v_res_2693_;
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromFieldInfo___boxed(lean_object* v_fi_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_Lean_Server_locationLinksFromFieldInfo(v_fi_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec_ref(v_a_2695_);
return v_res_2701_;
}
}
lean_object* l_Lean_Server_locationLinksFromOptionInfo(lean_object* v_i_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v_declName_2709_; lean_object* v___x_2710_; 
v_declName_2709_ = lean_ctor_get(v_i_2702_, 2);
lean_inc(v_declName_2709_);
lean_dec_ref(v_i_2702_);
v___x_2710_ = l_Lean_Server_locationLinksFromDecl(v_declName_2709_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
return v___x_2710_;
}
}
LEAN_EXPORT void l_Lean_Server_locationLinksFromOptionInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_2702_ = stack[0].m_obj;
lean_object* v_a_2703_ = stack[1].m_obj;
lean_object* v_a_2704_ = stack[2].m_obj;
lean_object* v_a_2705_ = stack[3].m_obj;
lean_object* v_a_2706_ = stack[4].m_obj;
lean_object* v_a_2707_ = stack[5].m_obj;
lean_object* v_res_2711_;
v_res_2711_ = l_Lean_Server_locationLinksFromOptionInfo(v_i_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
stack->m_obj
 = v_res_2711_;
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromOptionInfo___boxed(lean_object* v_i_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_Server_locationLinksFromOptionInfo(v_i_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec_ref(v_a_2713_);
return v_res_2719_;
}
}
lean_object* l_Lean_Server_locationLinksFromCommandInfo___redArg(lean_object* v_i_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v_elaborator_2727_; 
v_elaborator_2727_ = lean_ctor_get(v_i_2720_, 0);
if (lean_obj_tag(v_elaborator_2727_) == 1)
{
lean_object* v_pre_2728_; 
v_pre_2728_ = lean_ctor_get(v_elaborator_2727_, 0);
if (lean_obj_tag(v_pre_2728_) == 0)
{
lean_object* v_str_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; 
v_str_2729_ = lean_ctor_get(v_elaborator_2727_, 1);
v___x_2730_ = ((lean_object*)(l_Lean_Server_locationLinksFromImport___redArg___closed__3));
v___x_2731_ = lean_string_dec_eq(v_str_2729_, v___x_2730_);
if (v___x_2731_ == 0)
{
lean_dec_ref(v_i_2720_);
goto v___jp_2724_;
}
else
{
uint8_t v_kind_2732_; uint8_t v___x_2733_; uint8_t v___x_2734_; 
v_kind_2732_ = lean_ctor_get_uint8(v_a_2721_, sizeof(void*)*4);
v___x_2733_ = 2;
v___x_2734_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_2732_, v___x_2733_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; 
v___x_2735_ = l_Lean_Server_locationLinksFromImport___redArg(v_i_2720_, v_a_2721_, v_a_2722_);
return v___x_2735_;
}
else
{
lean_dec_ref(v_i_2720_);
goto v___jp_2724_;
}
}
}
else
{
lean_dec_ref(v_i_2720_);
goto v___jp_2724_;
}
}
else
{
lean_dec_ref(v_i_2720_);
goto v___jp_2724_;
}
v___jp_2724_:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2725_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
return v___x_2726_;
}
}
}
LEAN_EXPORT void l_Lean_Server_locationLinksFromCommandInfo___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_2720_ = stack[0].m_obj;
lean_object* v_a_2721_ = stack[1].m_obj;
lean_object* v_a_2722_ = stack[2].m_obj;
lean_object* v_res_2736_;
v_res_2736_ = l_Lean_Server_locationLinksFromCommandInfo___redArg(v_i_2720_, v_a_2721_, v_a_2722_);
stack->m_obj
 = v_res_2736_;
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromCommandInfo___redArg___boxed(lean_object* v_i_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Lean_Server_locationLinksFromCommandInfo___redArg(v_i_2737_, v_a_2738_, v_a_2739_);
lean_dec_ref(v_a_2739_);
lean_dec_ref(v_a_2738_);
return v_res_2741_;
}
}
lean_object* l_Lean_Server_locationLinksFromCommandInfo(lean_object* v_i_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Lean_Server_locationLinksFromCommandInfo___redArg(v_i_2742_, v_a_2743_, v_a_2746_);
return v___x_2749_;
}
}
LEAN_EXPORT void l_Lean_Server_locationLinksFromCommandInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_2742_ = stack[0].m_obj;
lean_object* v_a_2743_ = stack[1].m_obj;
lean_object* v_a_2744_ = stack[2].m_obj;
lean_object* v_a_2745_ = stack[3].m_obj;
lean_object* v_a_2746_ = stack[4].m_obj;
lean_object* v_a_2747_ = stack[5].m_obj;
lean_object* v_res_2750_;
v_res_2750_ = l_Lean_Server_locationLinksFromCommandInfo(v_i_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
stack->m_obj
 = v_res_2750_;
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksFromCommandInfo___boxed(lean_object* v_i_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_Server_locationLinksFromCommandInfo(v_i_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_);
lean_dec(v_a_2756_);
lean_dec_ref(v_a_2755_);
lean_dec(v_a_2754_);
lean_dec_ref(v_a_2753_);
lean_dec_ref(v_a_2752_);
return v_res_2758_;
}
}
lean_object* l_Lean_Server_locationLinksOfInfo___lam__0(uint8_t v_kind_2759_, lean_object* v_ll_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
uint8_t v___y_2768_; uint8_t v___x_2780_; uint8_t v___x_2781_; 
v___x_2780_ = 0;
v___x_2781_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_2759_, v___x_2780_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v___x_2782_ = lean_array_get_size(v_ll_2760_);
v___x_2783_ = lean_unsigned_to_nat(0u);
v___x_2784_ = lean_nat_dec_eq(v___x_2782_, v___x_2783_);
v___y_2768_ = v___x_2784_;
goto v___jp_2767_;
}
else
{
v___y_2768_ = v___x_2781_;
goto v___jp_2767_;
}
v___jp_2767_:
{
if (v___y_2768_ == 0)
{
lean_object* v___x_2769_; 
v___x_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2769_, 0, v_ll_2760_);
return v___x_2769_;
}
else
{
lean_object* v___x_2770_; 
v___x_2770_ = l_Lean_Server_locationLinksDefault(v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2779_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2773_ = v___x_2770_;
v_isShared_2774_ = v_isSharedCheck_2779_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2770_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2779_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2775_; lean_object* v___x_2777_; 
v___x_2775_ = l_Array_append___redArg(v_ll_2760_, v_a_2771_);
lean_dec(v_a_2771_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 0, v___x_2775_);
v___x_2777_ = v___x_2773_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2775_);
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
lean_dec_ref(v_ll_2760_);
return v___x_2770_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_locationLinksOfInfo___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_kind_2759_ = stack[0].m_num;
lean_object* v_ll_2760_ = stack[1].m_obj;
lean_object* v___y_2761_ = stack[2].m_obj;
lean_object* v___y_2762_ = stack[3].m_obj;
lean_object* v___y_2763_ = stack[4].m_obj;
lean_object* v___y_2764_ = stack[5].m_obj;
lean_object* v___y_2765_ = stack[6].m_obj;
lean_object* v_res_2785_;
v_res_2785_ = l_Lean_Server_locationLinksOfInfo___lam__0(v_kind_2759_, v_ll_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
stack->m_obj
 = v_res_2785_;
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___lam__0___boxed(lean_object* v_kind_2786_, lean_object* v_ll_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
uint8_t v_kind_boxed_2794_; lean_object* v_res_2795_; 
v_kind_boxed_2794_ = lean_unbox(v_kind_2786_);
v_res_2795_ = l_Lean_Server_locationLinksOfInfo___lam__0(v_kind_boxed_2794_, v_ll_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec_ref(v___y_2788_);
return v_res_2795_;
}
}
lean_object* l_Lean_Server_locationLinksOfInfo___lam__1(lean_object* v_info_2796_, lean_object* v___f_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
switch(lean_obj_tag(v_info_2796_))
{
case 1:
{
lean_object* v_i_2804_; lean_object* v___x_2805_; 
v_i_2804_ = lean_ctor_get(v_info_2796_, 0);
lean_inc_ref(v_i_2804_);
lean_dec_ref_known(v_info_2796_, 1);
v___x_2805_ = l_Lean_Server_locationLinksFromTermInfo(v_i_2804_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2807_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___x_2805_, 1);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
lean_inc_ref(v___y_2798_);
v___x_2807_ = lean_apply_7(v___f_2797_, v_a_2806_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, lean_box(0));
return v___x_2807_;
}
else
{
lean_dec_ref(v___f_2797_);
return v___x_2805_;
}
}
case 13:
{
lean_object* v_i_2808_; lean_object* v___x_2809_; 
v_i_2808_ = lean_ctor_get(v_info_2796_, 0);
lean_inc_ref(v_i_2808_);
lean_dec_ref_known(v_info_2796_, 1);
v___x_2809_ = l_Lean_Server_locationLinksFromDelabTermInfo(v_i_2808_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v___x_2811_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2810_);
lean_dec_ref_known(v___x_2809_, 1);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
lean_inc_ref(v___y_2798_);
v___x_2811_ = lean_apply_7(v___f_2797_, v_a_2810_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, lean_box(0));
return v___x_2811_;
}
else
{
lean_dec_ref(v___f_2797_);
return v___x_2809_;
}
}
case 7:
{
lean_object* v_i_2812_; lean_object* v___x_2813_; 
v_i_2812_ = lean_ctor_get(v_info_2796_, 0);
lean_inc_ref(v_i_2812_);
lean_dec_ref_known(v_info_2796_, 1);
v___x_2813_ = l_Lean_Server_locationLinksFromFieldInfo(v_i_2812_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2815_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2813_, 1);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
lean_inc_ref(v___y_2798_);
v___x_2815_ = lean_apply_7(v___f_2797_, v_a_2814_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, lean_box(0));
return v___x_2815_;
}
else
{
lean_dec_ref(v___f_2797_);
return v___x_2813_;
}
}
case 5:
{
lean_object* v_i_2816_; lean_object* v___x_2817_; 
v_i_2816_ = lean_ctor_get(v_info_2796_, 0);
lean_inc_ref(v_i_2816_);
lean_dec_ref_known(v_info_2796_, 1);
v___x_2817_ = l_Lean_Server_locationLinksFromOptionInfo(v_i_2816_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2819_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2818_);
lean_dec_ref_known(v___x_2817_, 1);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
lean_inc_ref(v___y_2798_);
v___x_2819_ = lean_apply_7(v___f_2797_, v_a_2818_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, lean_box(0));
return v___x_2819_;
}
else
{
lean_dec_ref(v___f_2797_);
return v___x_2817_;
}
}
case 3:
{
lean_object* v_i_2820_; lean_object* v___x_2821_; 
v_i_2820_ = lean_ctor_get(v_info_2796_, 0);
lean_inc_ref(v_i_2820_);
lean_dec_ref_known(v_info_2796_, 1);
v___x_2821_ = l_Lean_Server_locationLinksFromCommandInfo___redArg(v_i_2820_, v___y_2798_, v___y_2801_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v___x_2823_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2821_, 1);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
lean_inc_ref(v___y_2798_);
v___x_2823_ = lean_apply_7(v___f_2797_, v_a_2822_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, lean_box(0));
return v___x_2823_;
}
else
{
lean_dec_ref(v___f_2797_);
return v___x_2821_;
}
}
case 6:
{
lean_object* v_i_2824_; lean_object* v___x_2825_; 
v_i_2824_ = lean_ctor_get(v_info_2796_, 0);
lean_inc_ref(v_i_2824_);
lean_dec_ref_known(v_info_2796_, 1);
v___x_2825_ = l_Lean_Server_locationLinksFromErrorNameInfo(v_i_2824_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
lean_dec_ref(v_i_2824_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2827_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2825_, 1);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
lean_inc_ref(v___y_2798_);
v___x_2827_ = lean_apply_7(v___f_2797_, v_a_2826_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, lean_box(0));
return v___x_2827_;
}
else
{
lean_dec_ref(v___f_2797_);
return v___x_2825_;
}
}
case 17:
{
lean_object* v_i_2828_; lean_object* v_name_2829_; lean_object* v___x_2830_; 
v_i_2828_ = lean_ctor_get(v_info_2796_, 0);
lean_inc_ref(v_i_2828_);
lean_dec_ref_known(v_info_2796_, 1);
v_name_2829_ = lean_ctor_get(v_i_2828_, 1);
lean_inc(v_name_2829_);
lean_dec_ref(v_i_2828_);
v___x_2830_ = l_Lean_Server_locationLinksFromDecl(v_name_2829_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2832_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
lean_inc_ref(v___y_2798_);
v___x_2832_ = lean_apply_7(v___f_2797_, v_a_2831_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, lean_box(0));
return v___x_2832_;
}
else
{
lean_dec_ref(v___f_2797_);
return v___x_2830_;
}
}
default: 
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
lean_dec_ref(v_info_2796_);
v___x_2833_ = ((lean_object*)(l_Lean_Server_locationLinksFromDecl___closed__0));
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
lean_inc_ref(v___y_2798_);
v___x_2834_ = lean_apply_7(v___f_2797_, v___x_2833_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, lean_box(0));
return v___x_2834_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_locationLinksOfInfo___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_2796_ = stack[0].m_obj;
lean_object* v___f_2797_ = stack[1].m_obj;
lean_object* v___y_2798_ = stack[2].m_obj;
lean_object* v___y_2799_ = stack[3].m_obj;
lean_object* v___y_2800_ = stack[4].m_obj;
lean_object* v___y_2801_ = stack[5].m_obj;
lean_object* v___y_2802_ = stack[6].m_obj;
lean_object* v_res_2835_;
v_res_2835_ = l_Lean_Server_locationLinksOfInfo___lam__1(v_info_2796_, v___f_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
stack->m_obj
 = v_res_2835_;
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___lam__1___boxed(lean_object* v_info_2836_, lean_object* v___f_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_Server_locationLinksOfInfo___lam__1(v_info_2836_, v___f_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec_ref(v___y_2838_);
return v_res_2844_;
}
}
lean_object* l_Lean_Server_locationLinksOfInfo(lean_object* v_doc_2845_, uint8_t v_kind_2846_, lean_object* v_ictx_2847_, lean_object* v_infoTree_x3f_2848_){
_start:
{
lean_object* v_ctx_2850_; lean_object* v_info_2851_; lean_object* v_children_2852_; lean_object* v___x_2853_; lean_object* v___f_2854_; lean_object* v___y_2855_; lean_object* v___x_2856_; lean_object* v_ctx_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v_ctx_2850_ = lean_ctor_get(v_ictx_2847_, 0);
lean_inc_ref(v_ctx_2850_);
v_info_2851_ = lean_ctor_get(v_ictx_2847_, 1);
lean_inc_ref_n(v_info_2851_, 3);
v_children_2852_ = lean_ctor_get(v_ictx_2847_, 2);
lean_inc_ref(v_children_2852_);
lean_dec_ref(v_ictx_2847_);
v___x_2853_ = lean_box(v_kind_2846_);
v___f_2854_ = lean_alloc_closure((void*)(l_Lean_Server_locationLinksOfInfo___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2854_, 0, v___x_2853_);
v___y_2855_ = lean_alloc_closure((void*)(l_Lean_Server_locationLinksOfInfo___lam__1___boxed), 8, 2);
lean_closure_set(v___y_2855_, 0, v_info_2851_);
lean_closure_set(v___y_2855_, 1, v___f_2854_);
v___x_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2856_, 0, v_info_2851_);
v_ctx_2857_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_ctx_2857_, 0, v_doc_2845_);
lean_ctor_set(v_ctx_2857_, 1, v_infoTree_x3f_2848_);
lean_ctor_set(v_ctx_2857_, 2, v___x_2856_);
lean_ctor_set(v_ctx_2857_, 3, v_children_2852_);
lean_ctor_set_uint8(v_ctx_2857_, sizeof(void*)*4, v_kind_2846_);
v___x_2858_ = l_Lean_Elab_Info_lctx(v_info_2851_);
lean_dec_ref(v_info_2851_);
v___x_2859_ = l_Lean_Server_GoToM_run___redArg(v_ctx_2857_, v_ctx_2850_, v___x_2858_, v___y_2855_);
return v___x_2859_;
}
}
LEAN_EXPORT void l_Lean_Server_locationLinksOfInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_doc_2845_ = stack[0].m_obj;
uint8_t v_kind_2846_ = stack[1].m_num;
lean_object* v_ictx_2847_ = stack[2].m_obj;
lean_object* v_infoTree_x3f_2848_ = stack[3].m_obj;
lean_object* v_res_2860_;
v_res_2860_ = l_Lean_Server_locationLinksOfInfo(v_doc_2845_, v_kind_2846_, v_ictx_2847_, v_infoTree_x3f_2848_);
stack->m_obj
 = v_res_2860_;
}
LEAN_EXPORT lean_object* l_Lean_Server_locationLinksOfInfo___boxed(lean_object* v_doc_2861_, lean_object* v_kind_2862_, lean_object* v_ictx_2863_, lean_object* v_infoTree_x3f_2864_, lean_object* v_a_2865_){
_start:
{
uint8_t v_kind_boxed_2866_; lean_object* v_res_2867_; 
v_kind_boxed_2866_ = lean_unbox(v_kind_2862_);
v_res_2867_ = l_Lean_Server_locationLinksOfInfo(v_doc_2861_, v_kind_boxed_2866_, v_ictx_2863_, v_infoTree_x3f_2864_);
return v_res_2867_;
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
