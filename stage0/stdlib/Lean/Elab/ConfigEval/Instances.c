// Lean compiler output
// Module: Lean.Elab.ConfigEval.Instances
// Imports: public import Lean.Elab.ConfigEval.Basic
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
extern lean_object* l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
lean_object* l_Lean_Expr_nat_x3f(lean_object*);
lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_TSyntax_getNat(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_int_neg_succ_of_nat(lean_object*);
lean_object* l_Lean_Expr_int_x3f(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Array_unzip___redArg(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_name_x3f(lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__6;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__7_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__7_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__9;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__4_value),LEAN_SCALAR_PTR_LITERAL(235, 97, 249, 134, 197, 220, 12, 91)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__10 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__10_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__14 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__14_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__14_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__7_value),LEAN_SCALAR_PTR_LITERAL(160, 214, 196, 140, 104, 187, 164, 111)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__16 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__4_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Elab_ConfigEval_EvalTerm_evalIntStx_spec__0(lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__4;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__5_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__5_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__6_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__7_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__10;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__11 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__11_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__12 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__12_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__13;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "term-_"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__14 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__14_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__14_value),LEAN_SCALAR_PTR_LITERAL(77, 127, 37, 42, 155, 196, 209, 131)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__15 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__14_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__19_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__22_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__23 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__23_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__24 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__24_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doubleQuotedName"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Name"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__4_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(73, 239, 30, 105, 8, 60, 178, 241)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__4_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 202, 7, 33, 103, 74, 114, 212)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term[_]"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(86, 147, 168, 74, 195, 98, 232, 161)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__3_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6;
static const lean_array_object l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__3_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term#[_,]"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 119, 178, 128, 145, 112, 206, 247)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(191, 24, 88, 245, 200, 250, 27, 217)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__9_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(117, 121, 37, 123, 104, 28, 189, 89)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__5(lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "DataValue"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofBool"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 132, 69, 23, 118, 186, 30, 188)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__2_value),LEAN_SCALAR_PTR_LITERAL(251, 23, 12, 160, 15, 148, 79, 170)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__4_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__5_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__4, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__6_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofName"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__7_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 132, 69, 23, 118, 186, 30, 188)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__7_value),LEAN_SCALAR_PTR_LITERAL(99, 144, 20, 164, 82, 146, 48, 233)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ofString"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__9_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 132, 69, 23, 118, 186, 30, 188)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__9_value),LEAN_SCALAR_PTR_LITERAL(218, 187, 198, 144, 107, 222, 189, 173)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__5, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__11 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__11_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofInt"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__12 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__12_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 132, 69, 23, 118, 186, 30, 188)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__12_value),LEAN_SCALAR_PTR_LITERAL(213, 162, 111, 148, 162, 163, 105, 18)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__14 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__14_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 132, 69, 23, 118, 186, 30, 188)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__14_value),LEAN_SCALAR_PTR_LITERAL(231, 117, 125, 112, 51, 55, 57, 204)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instBool;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instNat;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instInt;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instString;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instName;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instProd(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 132, 69, 23, 118, 186, 30, 188)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instDataValue;
static lean_once_cell_t l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__0_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nof type `"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__5_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__0 = (const lean_object*)&l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "negSucc"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 236, 205, 0, 179, 53, 99, 201)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__14_value),LEAN_SCALAR_PTR_LITERAL(192, 66, 133, 102, 95, 170, 134, 92)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Could not evaluate the expression"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(125, 112, 129, 141, 33, 112, 200, 209)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instBool;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instNat;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instInt;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instString;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instName;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instArray(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instDataValue = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__1_value;
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___boxed(lean_object* v_00_u03b1_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0(v_00_u03b1_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
return v_res_26_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_box(0);
v___x_31_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__1));
v___x_32_ = l_Lean_mkConst(v___x_31_, v___x_30_);
return v___x_32_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2);
v___x_34_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__6(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = lean_box(0);
v___x_40_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5));
v___x_41_ = l_Lean_mkConst(v___x_40_, v___x_39_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__9(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_box(0);
v___x_47_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8));
v___x_48_ = l_Lean_mkConst(v___x_47_, v___x_46_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx(lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
uint8_t v___y_71_; lean_object* v___y_72_; uint8_t v_a_101_; uint8_t v_a_104_; lean_object* v___y_107_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v_id_118_; lean_object* v___x_119_; uint8_t v___y_121_; lean_object* v___y_122_; uint8_t v___y_123_; uint8_t v___y_124_; uint8_t v___y_134_; uint8_t v___x_140_; 
lean_inc(v_a_62_);
v___x_116_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_a_62_);
v___x_117_ = l_Lean_Syntax_getId(v___x_116_);
v_id_118_ = l_Lean_Name_eraseMacroScopes(v___x_117_);
lean_dec(v___x_117_);
v___x_119_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__10));
v___x_140_ = lean_name_eq(v_id_118_, v___x_119_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5));
v___x_142_ = lean_name_eq(v_id_118_, v___x_141_);
v___y_134_ = v___x_142_;
goto v___jp_133_;
}
else
{
v___y_134_ = v___x_140_;
goto v___jp_133_;
}
v___jp_70_:
{
lean_object* v___x_73_; lean_object* v_infoState_74_; uint8_t v_enabled_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_73_ = lean_st_ref_get(v_a_68_);
v_infoState_74_ = lean_ctor_get(v___x_73_, 7);
lean_inc_ref(v_infoState_74_);
lean_dec(v___x_73_);
v_enabled_75_ = lean_ctor_get_uint8(v_infoState_74_, sizeof(void*)*3);
lean_dec_ref(v_infoState_74_);
v___x_76_ = lean_box(v___y_71_);
lean_inc_ref(v___y_72_);
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___y_72_);
if (v_enabled_75_ == 0)
{
lean_object* v___x_78_; 
lean_dec(v_a_62_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
else
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; lean_object* v___x_83_; 
v___x_79_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3);
v___x_80_ = lean_box(0);
v___x_81_ = lean_box(0);
v___x_82_ = 0;
lean_inc_ref(v___y_72_);
v___x_83_ = l_Lean_Elab_Term_addTermInfo_x27(v_a_62_, v___y_72_, v___x_79_, v___x_80_, v___x_81_, v___x_82_, v___x_82_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; 
v_unused_91_ = lean_ctor_get(v___x_83_, 0);
lean_dec(v_unused_91_);
v___x_85_ = v___x_83_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_dec(v___x_83_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_77_);
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_77_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
lean_dec_ref_known(v___x_77_, 2);
v_a_92_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___x_83_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_83_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
v___jp_100_:
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__6, &l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__6);
v___y_71_ = v_a_101_;
v___y_72_ = v___x_102_;
goto v___jp_70_;
}
v___jp_103_:
{
if (v_a_104_ == 0)
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__9);
v___y_71_ = v_a_104_;
v___y_72_ = v___x_105_;
goto v___jp_70_;
}
else
{
v_a_101_ = v_a_104_;
goto v___jp_100_;
}
}
v___jp_106_:
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_115_; 
v_a_108_ = lean_ctor_get(v___y_107_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___y_107_);
if (v_isSharedCheck_115_ == 0)
{
v___x_110_ = v___y_107_;
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___y_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_113_; 
if (v_isShared_111_ == 0)
{
v___x_113_ = v___x_110_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
v___jp_120_:
{
if (v___y_124_ == 0)
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15));
lean_inc(v___x_116_);
v___x_126_ = l_Lean_Syntax_isOfKind(v___x_116_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
lean_dec(v___x_116_);
lean_dec(v_a_62_);
v___x_127_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_107_ = v___x_127_;
goto v___jp_106_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = l_Lean_Syntax_getArg(v___x_116_, v___x_128_);
lean_dec(v___x_116_);
v___x_130_ = l_Lean_Syntax_matchesIdent(v___x_129_, v___x_119_);
if (v___x_130_ == 0)
{
uint8_t v___x_131_; 
v___x_131_ = l_Lean_Syntax_matchesIdent(v___x_129_, v___y_122_);
lean_dec(v___x_129_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; 
lean_dec(v_a_62_);
v___x_132_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_107_ = v___x_132_;
goto v___jp_106_;
}
else
{
v_a_104_ = v___x_130_;
goto v___jp_103_;
}
}
else
{
lean_dec(v___x_129_);
v_a_104_ = v___y_123_;
goto v___jp_103_;
}
}
}
else
{
lean_dec(v___x_116_);
v_a_104_ = v___y_121_;
goto v___jp_103_;
}
}
v___jp_133_:
{
uint8_t v___x_135_; 
v___x_135_ = 1;
if (v___y_134_ == 0)
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__16));
v___x_137_ = lean_name_eq(v_id_118_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8));
v___x_139_ = lean_name_eq(v_id_118_, v___x_138_);
lean_dec(v_id_118_);
v___y_121_ = v___y_134_;
v___y_122_ = v___x_136_;
v___y_123_ = v___x_135_;
v___y_124_ = v___x_139_;
goto v___jp_120_;
}
else
{
lean_dec(v_id_118_);
v___y_121_ = v___y_134_;
v___y_122_ = v___x_136_;
v___y_123_ = v___x_135_;
v___y_124_ = v___x_137_;
goto v___jp_120_;
}
}
else
{
lean_dec(v_id_118_);
lean_dec(v___x_116_);
v_a_101_ = v___x_135_;
goto v___jp_100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___boxed(lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx(v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
return v_res_151_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_box(0);
v___x_156_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__1));
v___x_157_ = l_Lean_mkConst(v___x_156_, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2);
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_a_172_; lean_object* v_n_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
lean_inc(v_a_163_);
v_n_200_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_a_163_);
v___x_201_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__5));
lean_inc(v_n_200_);
v___x_202_ = l_Lean_Syntax_isOfKind(v_n_200_, v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
lean_dec(v_n_200_);
lean_dec(v_a_163_);
v___x_203_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v_a_204_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_203_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_203_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
else
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_TSyntax_getNat(v_n_200_);
lean_dec(v_n_200_);
v_a_172_ = v___x_212_;
goto v___jp_171_;
}
v___jp_171_:
{
lean_object* v___x_173_; lean_object* v_infoState_174_; uint8_t v_enabled_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_173_ = lean_st_ref_get(v_a_169_);
v_infoState_174_ = lean_ctor_get(v___x_173_, 7);
lean_inc_ref(v_infoState_174_);
lean_dec(v___x_173_);
v_enabled_175_ = lean_ctor_get_uint8(v_infoState_174_, sizeof(void*)*3);
lean_dec_ref(v_infoState_174_);
lean_inc(v_a_172_);
v___x_176_ = l_Lean_mkNatLit(v_a_172_);
lean_inc_ref(v___x_176_);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v_a_172_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
if (v_enabled_175_ == 0)
{
lean_object* v___x_178_; 
lean_dec_ref(v___x_176_);
lean_dec(v_a_163_);
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; lean_object* v___x_183_; 
v___x_179_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3);
v___x_180_ = lean_box(0);
v___x_181_ = lean_box(0);
v___x_182_ = 0;
v___x_183_ = l_Lean_Elab_Term_addTermInfo_x27(v_a_163_, v___x_176_, v___x_179_, v___x_180_, v___x_181_, v___x_182_, v___x_182_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_190_ == 0)
{
lean_object* v_unused_191_; 
v_unused_191_ = lean_ctor_get(v___x_183_, 0);
lean_dec(v_unused_191_);
v___x_185_ = v___x_183_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_dec(v___x_183_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_177_);
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_177_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec_ref_known(v___x_177_, 2);
v_a_192_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_183_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_183_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___boxed(lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Elab_ConfigEval_EvalTerm_evalIntStx_spec__0(lean_object* v_a_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_nat_to_int(v_a_222_);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = lean_box(0);
v___x_228_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__1));
v___x_229_ = l_Lean_Expr_const___override(v___x_228_, v___x_227_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2);
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__4(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_nat_to_int(v___x_232_);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = l_Lean_Level_ofNat(v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = lean_box(0);
v___x_242_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8);
v___x_243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__10(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_245_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__7));
v___x_246_ = l_Lean_Expr_const___override(v___x_245_, v___x_244_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__13(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_box(0);
v___x_252_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__12));
v___x_253_ = l_Lean_Expr_const___override(v___x_252_, v___x_251_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx(lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v___x_265_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v_a_296_; lean_object* v___y_308_; lean_object* v_n_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_265_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2);
lean_inc(v_a_257_);
v_n_317_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_a_257_);
v___x_318_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__5));
lean_inc(v_n_317_);
v___x_319_ = l_Lean_Syntax_isOfKind(v_n_317_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__15));
lean_inc(v_n_317_);
v___x_321_ = l_Lean_Syntax_isOfKind(v_n_317_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
lean_dec(v_n_317_);
lean_dec(v_a_257_);
v___x_322_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_308_ = v___x_322_;
goto v___jp_307_;
}
else
{
lean_object* v___x_323_; lean_object* v_n_324_; uint8_t v___x_325_; 
v___x_323_ = lean_unsigned_to_nat(1u);
v_n_324_ = l_Lean_Syntax_getArg(v_n_317_, v___x_323_);
lean_dec(v_n_317_);
lean_inc(v_n_324_);
v___x_325_ = l_Lean_Syntax_isOfKind(v_n_324_, v___x_318_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
lean_dec(v_n_324_);
lean_dec(v_a_257_);
v___x_326_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_308_ = v___x_326_;
goto v___jp_307_;
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = l_Lean_TSyntax_getNat(v_n_324_);
lean_dec(v_n_324_);
v___x_328_ = lean_nat_to_int(v___x_327_);
v___x_329_ = lean_int_neg(v___x_328_);
lean_dec(v___x_328_);
v_a_296_ = v___x_329_;
goto v___jp_295_;
}
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = l_Lean_TSyntax_getNat(v_n_317_);
lean_dec(v_n_317_);
v___x_331_ = lean_nat_to_int(v___x_330_);
v_a_296_ = v___x_331_;
goto v___jp_295_;
}
v___jp_266_:
{
lean_object* v___x_269_; lean_object* v_infoState_270_; uint8_t v_enabled_271_; lean_object* v___x_272_; 
v___x_269_ = lean_st_ref_get(v_a_263_);
v_infoState_270_ = lean_ctor_get(v___x_269_, 7);
lean_inc_ref(v_infoState_270_);
lean_dec(v___x_269_);
v_enabled_271_ = lean_ctor_get_uint8(v_infoState_270_, sizeof(void*)*3);
lean_dec_ref(v_infoState_270_);
lean_inc_ref(v___y_268_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___y_267_);
lean_ctor_set(v___x_272_, 1, v___y_268_);
if (v_enabled_271_ == 0)
{
lean_object* v___x_273_; 
lean_dec_ref(v___y_268_);
lean_dec(v_a_257_);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; lean_object* v___x_278_; 
v___x_274_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3);
v___x_275_ = lean_box(0);
v___x_276_ = lean_box(0);
v___x_277_ = 0;
v___x_278_ = l_Lean_Elab_Term_addTermInfo_x27(v_a_257_, v___y_268_, v___x_274_, v___x_275_, v___x_276_, v___x_277_, v___x_277_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; 
v_unused_286_ = lean_ctor_get(v___x_278_, 0);
lean_dec(v_unused_286_);
v___x_280_ = v___x_278_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_dec(v___x_278_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_272_);
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_272_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_dec_ref_known(v___x_272_, 2);
v_a_287_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_278_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_278_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
v___jp_295_:
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__4, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__4_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__4);
v___x_298_ = lean_int_dec_le(v___x_297_, v_a_296_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_299_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__10, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__10_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__10);
v___x_300_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__13, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__13_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__13);
v___x_301_ = lean_int_neg(v_a_296_);
v___x_302_ = l_Int_toNat(v___x_301_);
lean_dec(v___x_301_);
v___x_303_ = l_Lean_instToExprInt_mkNat(v___x_302_);
v___x_304_ = l_Lean_mkApp3(v___x_299_, v___x_265_, v___x_300_, v___x_303_);
v___y_267_ = v_a_296_;
v___y_268_ = v___x_304_;
goto v___jp_266_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = l_Int_toNat(v_a_296_);
v___x_306_ = l_Lean_instToExprInt_mkNat(v___x_305_);
v___y_267_ = v_a_296_;
v___y_268_ = v___x_306_;
goto v___jp_266_;
}
}
v___jp_307_:
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
v_a_309_ = lean_ctor_get(v___y_308_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___y_308_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___y_308_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___y_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___boxed(lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx(v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
return v_res_340_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_box(0);
v___x_345_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__1));
v___x_346_ = l_Lean_mkConst(v___x_345_, v___x_344_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2);
v___x_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx(lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_a_361_; lean_object* v_s_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
lean_inc(v_a_352_);
v_s_389_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_a_352_);
v___x_390_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__5));
lean_inc(v_s_389_);
v___x_391_ = l_Lean_Syntax_isOfKind(v_s_389_, v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec(v_s_389_);
lean_dec(v_a_352_);
v___x_392_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
else
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_TSyntax_getString(v_s_389_);
lean_dec(v_s_389_);
v_a_361_ = v___x_401_;
goto v___jp_360_;
}
v___jp_360_:
{
lean_object* v___x_362_; lean_object* v_infoState_363_; uint8_t v_enabled_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_362_ = lean_st_ref_get(v_a_358_);
v_infoState_363_ = lean_ctor_get(v___x_362_, 7);
lean_inc_ref(v_infoState_363_);
lean_dec(v___x_362_);
v_enabled_364_ = lean_ctor_get_uint8(v_infoState_363_, sizeof(void*)*3);
lean_dec_ref(v_infoState_363_);
lean_inc_ref(v_a_361_);
v___x_365_ = l_Lean_mkStrLit(v_a_361_);
lean_inc_ref(v___x_365_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v_a_361_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
if (v_enabled_364_ == 0)
{
lean_object* v___x_367_; 
lean_dec_ref(v___x_365_);
lean_dec(v_a_352_);
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
return v___x_367_;
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; lean_object* v___x_372_; 
v___x_368_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3);
v___x_369_ = lean_box(0);
v___x_370_ = lean_box(0);
v___x_371_ = 0;
v___x_372_ = l_Lean_Elab_Term_addTermInfo_x27(v_a_352_, v___x_365_, v___x_368_, v___x_369_, v___x_370_, v___x_371_, v___x_371_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; 
v_unused_380_ = lean_ctor_get(v___x_372_, 0);
lean_dec(v_unused_380_);
v___x_374_ = v___x_372_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_dec(v___x_372_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_366_);
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_366_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec_ref_known(v___x_366_, 2);
v_a_381_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_372_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_372_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___boxed(lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx(v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
return v_res_410_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_keys_411_, lean_object* v_i_412_, lean_object* v_k_413_){
_start:
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = lean_array_get_size(v_keys_411_);
v___x_415_ = lean_nat_dec_lt(v_i_412_, v___x_414_);
if (v___x_415_ == 0)
{
lean_dec(v_i_412_);
return v___x_415_;
}
else
{
lean_object* v_k_x27_416_; uint8_t v___x_417_; 
v_k_x27_416_ = lean_array_fget_borrowed(v_keys_411_, v_i_412_);
v___x_417_ = l_Lean_instBEqExtraModUse_beq(v_k_413_, v_k_x27_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_unsigned_to_nat(1u);
v___x_419_ = lean_nat_add(v_i_412_, v___x_418_);
lean_dec(v_i_412_);
v_i_412_ = v___x_419_;
goto _start;
}
else
{
lean_dec(v_i_412_);
return v___x_417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_keys_421_, lean_object* v_i_422_, lean_object* v_k_423_){
_start:
{
uint8_t v_res_424_; lean_object* v_r_425_; 
v_res_424_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_keys_421_, v_i_422_, v_k_423_);
lean_dec_ref(v_k_423_);
lean_dec_ref(v_keys_421_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_426_, size_t v_x_427_, lean_object* v_x_428_){
_start:
{
if (lean_obj_tag(v_x_426_) == 0)
{
lean_object* v_es_429_; lean_object* v___x_430_; size_t v___x_431_; size_t v___x_432_; lean_object* v_j_433_; lean_object* v___x_434_; 
v_es_429_ = lean_ctor_get(v_x_426_, 0);
v___x_430_ = lean_box(2);
v___x_431_ = ((size_t)31ULL);
v___x_432_ = lean_usize_land(v_x_427_, v___x_431_);
v_j_433_ = lean_usize_to_nat(v___x_432_);
v___x_434_ = lean_array_get_borrowed(v___x_430_, v_es_429_, v_j_433_);
lean_dec(v_j_433_);
switch(lean_obj_tag(v___x_434_))
{
case 0:
{
lean_object* v_key_435_; uint8_t v___x_436_; 
v_key_435_ = lean_ctor_get(v___x_434_, 0);
v___x_436_ = l_Lean_instBEqExtraModUse_beq(v_x_428_, v_key_435_);
return v___x_436_;
}
case 1:
{
lean_object* v_node_437_; size_t v___x_438_; size_t v___x_439_; 
v_node_437_ = lean_ctor_get(v___x_434_, 0);
v___x_438_ = ((size_t)5ULL);
v___x_439_ = lean_usize_shift_right(v_x_427_, v___x_438_);
v_x_426_ = v_node_437_;
v_x_427_ = v___x_439_;
goto _start;
}
default: 
{
uint8_t v___x_441_; 
v___x_441_ = 0;
return v___x_441_;
}
}
}
else
{
lean_object* v_ks_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v_ks_442_ = lean_ctor_get(v_x_426_, 0);
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_ks_442_, v___x_443_, v_x_428_);
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
size_t v_x_10397__boxed_448_; uint8_t v_res_449_; lean_object* v_r_450_; 
v_x_10397__boxed_448_ = lean_unbox_usize(v_x_446_);
lean_dec(v_x_446_);
v_res_449_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg(v_x_445_, v_x_10397__boxed_448_, v_x_447_);
lean_dec_ref(v_x_447_);
lean_dec_ref(v_x_445_);
v_r_450_ = lean_box(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg(lean_object* v_x_451_, lean_object* v_x_452_){
_start:
{
uint64_t v___x_453_; size_t v___x_454_; uint8_t v___x_455_; 
v___x_453_ = l_Lean_instHashableExtraModUse_hash(v_x_452_);
v___x_454_ = lean_uint64_to_usize(v___x_453_);
v___x_455_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg(v_x_451_, v___x_454_, v_x_452_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_456_, lean_object* v_x_457_){
_start:
{
uint8_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg(v_x_456_, v_x_457_);
lean_dec_ref(v_x_457_);
lean_dec_ref(v_x_456_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6(lean_object* v_msgData_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v___x_466_; lean_object* v_env_467_; lean_object* v___x_468_; lean_object* v_mctx_469_; lean_object* v_lctx_470_; lean_object* v_options_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_466_ = lean_st_ref_get(v___y_464_);
v_env_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc_ref(v_env_467_);
lean_dec(v___x_466_);
v___x_468_ = lean_st_ref_get(v___y_462_);
v_mctx_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc_ref(v_mctx_469_);
lean_dec(v___x_468_);
v_lctx_470_ = lean_ctor_get(v___y_461_, 2);
v_options_471_ = lean_ctor_get(v___y_463_, 2);
lean_inc_ref(v_options_471_);
lean_inc_ref(v_lctx_470_);
v___x_472_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_472_, 0, v_env_467_);
lean_ctor_set(v___x_472_, 1, v_mctx_469_);
lean_ctor_set(v___x_472_, 2, v_lctx_470_);
lean_ctor_set(v___x_472_, 3, v_options_471_);
v___x_473_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v_msgData_460_);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_msgData_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6(v_msgData_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v_res_481_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_482_; double v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = lean_float_of_nat(v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_487_, lean_object* v_msg_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_ref_494_; lean_object* v___x_495_; lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_540_; 
v_ref_494_ = lean_ctor_get(v___y_491_, 5);
v___x_495_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6(v_msg_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_540_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_540_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_540_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v_traceState_501_; lean_object* v_env_502_; lean_object* v_nextMacroScope_503_; lean_object* v_ngen_504_; lean_object* v_auxDeclNGen_505_; lean_object* v_cache_506_; lean_object* v_messages_507_; lean_object* v_infoState_508_; lean_object* v_snapshotTasks_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_539_; 
v___x_500_ = lean_st_ref_take(v___y_492_);
v_traceState_501_ = lean_ctor_get(v___x_500_, 4);
v_env_502_ = lean_ctor_get(v___x_500_, 0);
v_nextMacroScope_503_ = lean_ctor_get(v___x_500_, 1);
v_ngen_504_ = lean_ctor_get(v___x_500_, 2);
v_auxDeclNGen_505_ = lean_ctor_get(v___x_500_, 3);
v_cache_506_ = lean_ctor_get(v___x_500_, 5);
v_messages_507_ = lean_ctor_get(v___x_500_, 6);
v_infoState_508_ = lean_ctor_get(v___x_500_, 7);
v_snapshotTasks_509_ = lean_ctor_get(v___x_500_, 8);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_539_ == 0)
{
v___x_511_ = v___x_500_;
v_isShared_512_ = v_isSharedCheck_539_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_snapshotTasks_509_);
lean_inc(v_infoState_508_);
lean_inc(v_messages_507_);
lean_inc(v_cache_506_);
lean_inc(v_traceState_501_);
lean_inc(v_auxDeclNGen_505_);
lean_inc(v_ngen_504_);
lean_inc(v_nextMacroScope_503_);
lean_inc(v_env_502_);
lean_dec(v___x_500_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_539_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
uint64_t v_tid_513_; lean_object* v_traces_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_538_; 
v_tid_513_ = lean_ctor_get_uint64(v_traceState_501_, sizeof(void*)*1);
v_traces_514_ = lean_ctor_get(v_traceState_501_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v_traceState_501_);
if (v_isSharedCheck_538_ == 0)
{
v___x_516_ = v_traceState_501_;
v_isShared_517_ = v_isSharedCheck_538_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_traces_514_);
lean_dec(v_traceState_501_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_538_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; double v___x_519_; uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_518_ = lean_box(0);
v___x_519_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_520_ = 0;
v___x_521_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_522_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_522_, 0, v_cls_487_);
lean_ctor_set(v___x_522_, 1, v___x_518_);
lean_ctor_set(v___x_522_, 2, v___x_521_);
lean_ctor_set_float(v___x_522_, sizeof(void*)*3, v___x_519_);
lean_ctor_set_float(v___x_522_, sizeof(void*)*3 + 8, v___x_519_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*3 + 16, v___x_520_);
v___x_523_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_524_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v_a_496_);
lean_ctor_set(v___x_524_, 2, v___x_523_);
lean_inc(v_ref_494_);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v_ref_494_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = l_Lean_PersistentArray_push___redArg(v_traces_514_, v___x_525_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_526_);
v___x_528_ = v___x_516_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_526_);
lean_ctor_set_uint64(v_reuseFailAlloc_537_, sizeof(void*)*1, v_tid_513_);
v___x_528_ = v_reuseFailAlloc_537_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_530_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 4, v___x_528_);
v___x_530_ = v___x_511_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_env_502_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_nextMacroScope_503_);
lean_ctor_set(v_reuseFailAlloc_536_, 2, v_ngen_504_);
lean_ctor_set(v_reuseFailAlloc_536_, 3, v_auxDeclNGen_505_);
lean_ctor_set(v_reuseFailAlloc_536_, 4, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_536_, 5, v_cache_506_);
lean_ctor_set(v_reuseFailAlloc_536_, 6, v_messages_507_);
lean_ctor_set(v_reuseFailAlloc_536_, 7, v_infoState_508_);
lean_ctor_set(v_reuseFailAlloc_536_, 8, v_snapshotTasks_509_);
v___x_530_ = v_reuseFailAlloc_536_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_531_ = lean_st_ref_put(v___y_492_, v___x_530_);
v___x_532_ = lean_box(0);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_532_);
v___x_534_ = v___x_498_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_541_, lean_object* v_msg_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg(v_cls_541_, v_msg_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
return v_res_548_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__1));
v___x_552_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__0));
v___x_553_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_552_, v___x_551_);
return v___x_553_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_554_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
return v___x_558_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4);
v___x_560_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
lean_ctor_set(v___x_560_, 2, v___x_559_);
lean_ctor_set(v___x_560_, 3, v___x_559_);
lean_ctor_set(v___x_560_, 4, v___x_559_);
lean_ctor_set(v___x_560_, 5, v___x_559_);
return v___x_560_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__9));
v___x_566_ = l_Lean_stringToMessageData(v___x_565_);
return v___x_566_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__11));
v___x_569_ = l_Lean_stringToMessageData(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v_cls_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_cls_575_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__8));
v___x_576_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__15));
v___x_577_ = l_Lean_Name_append(v___x_576_, v_cls_575_);
return v___x_577_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__17));
v___x_580_ = l_Lean_stringToMessageData(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__19));
v___x_583_ = l_Lean_stringToMessageData(v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0(lean_object* v_mod_588_, uint8_t v_isMeta_589_, lean_object* v_hint_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v___x_598_; lean_object* v_env_599_; uint8_t v_isExporting_600_; lean_object* v___x_601_; lean_object* v_env_602_; lean_object* v___x_603_; lean_object* v_entry_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_598_ = lean_st_ref_get(v___y_596_);
v_env_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc_ref(v_env_599_);
lean_dec(v___x_598_);
v_isExporting_600_ = lean_ctor_get_uint8(v_env_599_, sizeof(void*)*8);
lean_dec_ref(v_env_599_);
v___x_601_ = lean_st_ref_get(v___y_596_);
v_env_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc_ref(v_env_602_);
lean_dec(v___x_601_);
v___x_603_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2);
lean_inc(v_mod_588_);
v_entry_604_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_604_, 0, v_mod_588_);
lean_ctor_set_uint8(v_entry_604_, sizeof(void*)*1, v_isExporting_600_);
lean_ctor_set_uint8(v_entry_604_, sizeof(void*)*1 + 1, v_isMeta_589_);
v___x_605_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_606_ = lean_box(1);
v___x_607_ = lean_box(0);
v___x_650_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_603_, v___x_605_, v_env_602_, v___x_606_, v___x_607_);
v___x_651_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg(v___x_650_, v_entry_604_);
lean_dec(v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v_options_652_; uint8_t v_hasTrace_653_; 
v_options_652_ = lean_ctor_get(v___y_595_, 2);
v_hasTrace_653_ = lean_ctor_get_uint8(v_options_652_, sizeof(void*)*1);
if (v_hasTrace_653_ == 0)
{
lean_dec(v_hint_590_);
lean_dec(v_mod_588_);
v___y_609_ = v___y_594_;
v___y_610_ = v___y_596_;
goto v___jp_608_;
}
else
{
lean_object* v_inheritedTraceOptions_654_; lean_object* v_cls_655_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___x_675_; uint8_t v___x_676_; 
v_inheritedTraceOptions_654_ = lean_ctor_get(v___y_595_, 13);
v_cls_655_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__8));
v___x_675_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16);
v___x_676_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_654_, v_options_652_, v___x_675_);
if (v___x_676_ == 0)
{
lean_dec(v_hint_590_);
lean_dec(v_mod_588_);
v___y_609_ = v___y_594_;
v___y_610_ = v___y_596_;
goto v___jp_608_;
}
else
{
lean_object* v___x_677_; lean_object* v___y_679_; 
v___x_677_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18);
if (v_isExporting_600_ == 0)
{
lean_object* v___x_686_; 
v___x_686_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__23));
v___y_679_ = v___x_686_;
goto v___jp_678_;
}
else
{
lean_object* v___x_687_; 
v___x_687_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__24));
v___y_679_ = v___x_687_;
goto v___jp_678_;
}
v___jp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
lean_inc_ref(v___y_679_);
v___x_680_ = l_Lean_stringToMessageData(v___y_679_);
v___x_681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_677_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20);
v___x_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
if (v_isMeta_589_ == 0)
{
lean_object* v___x_684_; 
v___x_684_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__21));
v___y_662_ = v___x_683_;
v___y_663_ = v___x_684_;
goto v___jp_661_;
}
else
{
lean_object* v___x_685_; 
v___x_685_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__22));
v___y_662_ = v___x_683_;
v___y_663_ = v___x_685_;
goto v___jp_661_;
}
}
}
v___jp_656_:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v___y_657_);
lean_ctor_set(v___x_659_, 1, v___y_658_);
v___x_660_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg(v_cls_655_, v___x_659_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_dec_ref_known(v___x_660_, 1);
v___y_609_ = v___y_594_;
v___y_610_ = v___y_596_;
goto v___jp_608_;
}
else
{
lean_dec_ref_known(v_entry_604_, 1);
return v___x_660_;
}
}
v___jp_661_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
lean_inc_ref(v___y_663_);
v___x_664_ = l_Lean_stringToMessageData(v___y_663_);
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v___y_662_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10);
v___x_667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = l_Lean_MessageData_ofName(v_mod_588_);
v___x_669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = l_Lean_Name_isAnonymous(v_hint_590_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12);
v___x_672_ = l_Lean_MessageData_ofName(v_hint_590_);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___y_657_ = v___x_669_;
v___y_658_ = v___x_673_;
goto v___jp_656_;
}
else
{
lean_object* v___x_674_; 
lean_dec(v_hint_590_);
v___x_674_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13);
v___y_657_ = v___x_669_;
v___y_658_ = v___x_674_;
goto v___jp_656_;
}
}
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; 
lean_dec_ref_known(v_entry_604_, 1);
lean_dec(v_hint_590_);
lean_dec(v_mod_588_);
v___x_688_ = lean_box(0);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
v___jp_608_:
{
lean_object* v___x_611_; lean_object* v_toEnvExtension_612_; lean_object* v_env_613_; lean_object* v_nextMacroScope_614_; lean_object* v_ngen_615_; lean_object* v_auxDeclNGen_616_; lean_object* v_traceState_617_; lean_object* v_messages_618_; lean_object* v_infoState_619_; lean_object* v_snapshotTasks_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_648_; 
v___x_611_ = lean_st_ref_take(v___y_610_);
v_toEnvExtension_612_ = lean_ctor_get(v___x_605_, 0);
v_env_613_ = lean_ctor_get(v___x_611_, 0);
v_nextMacroScope_614_ = lean_ctor_get(v___x_611_, 1);
v_ngen_615_ = lean_ctor_get(v___x_611_, 2);
v_auxDeclNGen_616_ = lean_ctor_get(v___x_611_, 3);
v_traceState_617_ = lean_ctor_get(v___x_611_, 4);
v_messages_618_ = lean_ctor_get(v___x_611_, 6);
v_infoState_619_ = lean_ctor_get(v___x_611_, 7);
v_snapshotTasks_620_ = lean_ctor_get(v___x_611_, 8);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_648_ == 0)
{
lean_object* v_unused_649_; 
v_unused_649_ = lean_ctor_get(v___x_611_, 5);
lean_dec(v_unused_649_);
v___x_622_ = v___x_611_;
v_isShared_623_ = v_isSharedCheck_648_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_snapshotTasks_620_);
lean_inc(v_infoState_619_);
lean_inc(v_messages_618_);
lean_inc(v_traceState_617_);
lean_inc(v_auxDeclNGen_616_);
lean_inc(v_ngen_615_);
lean_inc(v_nextMacroScope_614_);
lean_inc(v_env_613_);
lean_dec(v___x_611_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_648_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_asyncMode_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
v_asyncMode_624_ = lean_ctor_get(v_toEnvExtension_612_, 2);
v___x_625_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_605_, v_env_613_, v_entry_604_, v_asyncMode_624_, v___x_607_);
v___x_626_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 5, v___x_626_);
lean_ctor_set(v___x_622_, 0, v___x_625_);
v___x_628_ = v___x_622_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_nextMacroScope_614_);
lean_ctor_set(v_reuseFailAlloc_647_, 2, v_ngen_615_);
lean_ctor_set(v_reuseFailAlloc_647_, 3, v_auxDeclNGen_616_);
lean_ctor_set(v_reuseFailAlloc_647_, 4, v_traceState_617_);
lean_ctor_set(v_reuseFailAlloc_647_, 5, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_647_, 6, v_messages_618_);
lean_ctor_set(v_reuseFailAlloc_647_, 7, v_infoState_619_);
lean_ctor_set(v_reuseFailAlloc_647_, 8, v_snapshotTasks_620_);
v___x_628_ = v_reuseFailAlloc_647_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v_mctx_631_; lean_object* v_zetaDeltaFVarIds_632_; lean_object* v_postponed_633_; lean_object* v_diag_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_645_; 
v___x_629_ = lean_st_ref_put(v___y_610_, v___x_628_);
v___x_630_ = lean_st_ref_take(v___y_609_);
v_mctx_631_ = lean_ctor_get(v___x_630_, 0);
v_zetaDeltaFVarIds_632_ = lean_ctor_get(v___x_630_, 2);
v_postponed_633_ = lean_ctor_get(v___x_630_, 3);
v_diag_634_ = lean_ctor_get(v___x_630_, 4);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v___x_630_, 1);
lean_dec(v_unused_646_);
v___x_636_ = v___x_630_;
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_diag_634_);
lean_inc(v_postponed_633_);
lean_inc(v_zetaDeltaFVarIds_632_);
lean_inc(v_mctx_631_);
lean_dec(v___x_630_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_638_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_638_);
v___x_640_ = v___x_636_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_mctx_631_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_zetaDeltaFVarIds_632_);
lean_ctor_set(v_reuseFailAlloc_644_, 3, v_postponed_633_);
lean_ctor_set(v_reuseFailAlloc_644_, 4, v_diag_634_);
v___x_640_ = v_reuseFailAlloc_644_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = lean_st_ref_put(v___y_609_, v___x_640_);
v___x_642_ = lean_box(0);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___boxed(lean_object* v_mod_690_, lean_object* v_isMeta_691_, lean_object* v_hint_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
uint8_t v_isMeta_boxed_700_; lean_object* v_res_701_; 
v_isMeta_boxed_700_ = lean_unbox(v_isMeta_691_);
v_res_701_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0(v_mod_690_, v_isMeta_boxed_700_, v_hint_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1(lean_object* v___x_702_, lean_object* v_declName_703_, lean_object* v_as_704_, size_t v_sz_705_, size_t v_i_706_, lean_object* v_b_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = lean_usize_dec_lt(v_i_706_, v_sz_705_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
lean_dec(v_declName_703_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v_b_707_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; lean_object* v_modules_718_; lean_object* v___x_719_; lean_object* v_a_720_; lean_object* v___x_721_; lean_object* v_toImport_722_; lean_object* v_module_723_; uint8_t v___x_724_; lean_object* v___x_725_; 
v___x_717_ = l_Lean_Environment_header(v___x_702_);
v_modules_718_ = lean_ctor_get(v___x_717_, 3);
lean_inc_ref(v_modules_718_);
lean_dec_ref(v___x_717_);
v___x_719_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_720_ = lean_array_uget_borrowed(v_as_704_, v_i_706_);
v___x_721_ = lean_array_get(v___x_719_, v_modules_718_, v_a_720_);
lean_dec_ref(v_modules_718_);
v_toImport_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc_ref(v_toImport_722_);
lean_dec(v___x_721_);
v_module_723_ = lean_ctor_get(v_toImport_722_, 0);
lean_inc(v_module_723_);
lean_dec_ref(v_toImport_722_);
v___x_724_ = 0;
lean_inc(v_declName_703_);
v___x_725_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0(v_module_723_, v___x_724_, v_declName_703_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v___x_726_; size_t v___x_727_; size_t v___x_728_; 
lean_dec_ref_known(v___x_725_, 1);
v___x_726_ = lean_box(0);
v___x_727_ = ((size_t)1ULL);
v___x_728_ = lean_usize_add(v_i_706_, v___x_727_);
v_i_706_ = v___x_728_;
v_b_707_ = v___x_726_;
goto _start;
}
else
{
lean_dec(v_declName_703_);
return v___x_725_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1___boxed(lean_object* v___x_730_, lean_object* v_declName_731_, lean_object* v_as_732_, lean_object* v_sz_733_, lean_object* v_i_734_, lean_object* v_b_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
size_t v_sz_boxed_743_; size_t v_i_boxed_744_; lean_object* v_res_745_; 
v_sz_boxed_743_ = lean_unbox_usize(v_sz_733_);
lean_dec(v_sz_733_);
v_i_boxed_744_ = lean_unbox_usize(v_i_734_);
lean_dec(v_i_734_);
v_res_745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1(v___x_730_, v_declName_731_, v_as_732_, v_sz_boxed_743_, v_i_boxed_744_, v_b_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec_ref(v_as_732_);
lean_dec_ref(v___x_730_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10_spec__12___redArg(lean_object* v_m_746_, lean_object* v_query_747_, lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v_x_750_){
_start:
{
lean_object* v_zero_751_; uint8_t v_isZero_752_; 
v_zero_751_ = lean_unsigned_to_nat(0u);
v_isZero_752_ = lean_nat_dec_eq(v_x_749_, v_zero_751_);
if (v_isZero_752_ == 1)
{
lean_dec(v_x_750_);
lean_dec(v_x_749_);
if (lean_obj_tag(v_x_748_) == 0)
{
lean_object* v___x_753_; 
v___x_753_ = lean_box(2);
return v___x_753_;
}
else
{
lean_object* v_val_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
v_val_754_ = lean_ctor_get(v_x_748_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v_x_748_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v_x_748_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_val_754_);
lean_dec(v_x_748_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_val_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v_keyArray_762_; lean_object* v_valueArray_763_; lean_object* v___x_764_; uint8_t v_isSome_765_; 
v_keyArray_762_ = lean_ctor_get(v_m_746_, 1);
v_valueArray_763_ = lean_ctor_get(v_m_746_, 2);
v___x_764_ = lean_array_fget_borrowed(v_keyArray_762_, v_x_750_);
v_isSome_765_ = lean_noption_is_some(v___x_764_);
if (v_isSome_765_ == 0)
{
lean_dec(v_x_749_);
if (lean_obj_tag(v_x_748_) == 0)
{
lean_object* v___x_766_; 
v___x_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_766_, 0, v_x_750_);
return v___x_766_;
}
else
{
lean_object* v_val_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec(v_x_750_);
v_val_767_ = lean_ctor_get(v_x_748_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v_x_748_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v_x_748_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_val_767_);
lean_dec(v_x_748_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_val_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
else
{
lean_object* v_one_775_; lean_object* v_n_776_; lean_object* v___y_778_; 
v_one_775_ = lean_unsigned_to_nat(1u);
v_n_776_ = lean_nat_sub(v_x_749_, v_one_775_);
lean_dec(v_x_749_);
if (v_isSome_765_ == 0)
{
goto v___jp_784_;
}
else
{
lean_object* v___x_786_; uint8_t v_isSome_787_; 
v___x_786_ = lean_array_fget_borrowed(v_valueArray_763_, v_x_750_);
v_isSome_787_ = lean_noption_is_some(v___x_786_);
if (v_isSome_787_ == 0)
{
goto v___jp_784_;
}
else
{
lean_object* v_val_788_; uint8_t v___x_789_; 
lean_inc(v___x_764_);
v_val_788_ = lean_noption_get(v___x_764_);
v___x_789_ = lean_name_eq(v_val_788_, v_query_747_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
lean_dec(v_val_788_);
v___x_790_ = lean_array_get_size(v_keyArray_762_);
v___x_791_ = lean_nat_add(v_x_750_, v_one_775_);
lean_dec(v_x_750_);
v___x_792_ = lean_nat_dec_lt(v___x_791_, v___x_790_);
if (v___x_792_ == 0)
{
lean_dec(v___x_791_);
v_x_749_ = v_n_776_;
v_x_750_ = v_zero_751_;
goto _start;
}
else
{
v_x_749_ = v_n_776_;
v_x_750_ = v___x_791_;
goto _start;
}
}
else
{
lean_object* v_val_795_; lean_object* v___x_796_; 
lean_dec(v_n_776_);
lean_dec(v_x_748_);
lean_inc(v___x_786_);
v_val_795_ = lean_noption_get(v___x_786_);
v___x_796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_796_, 0, v_x_750_);
lean_ctor_set(v___x_796_, 1, v_val_788_);
lean_ctor_set(v___x_796_, 2, v_val_795_);
return v___x_796_;
}
}
}
v___jp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_779_ = lean_array_get_size(v_keyArray_762_);
v___x_780_ = lean_nat_add(v_x_750_, v_one_775_);
lean_dec(v_x_750_);
v___x_781_ = lean_nat_dec_lt(v___x_780_, v___x_779_);
if (v___x_781_ == 0)
{
lean_dec(v___x_780_);
v_x_748_ = v___y_778_;
v_x_749_ = v_n_776_;
v_x_750_ = v_zero_751_;
goto _start;
}
else
{
v_x_748_ = v___y_778_;
v_x_749_ = v_n_776_;
v_x_750_ = v___x_780_;
goto _start;
}
}
v___jp_784_:
{
if (lean_obj_tag(v_x_748_) == 0)
{
lean_object* v___x_785_; 
lean_inc(v_x_750_);
v___x_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_785_, 0, v_x_750_);
v___y_778_ = v___x_785_;
goto v___jp_777_;
}
else
{
v___y_778_ = v_x_748_;
goto v___jp_777_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10_spec__12___redArg___boxed(lean_object* v_m_797_, lean_object* v_query_798_, lean_object* v_x_799_, lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10_spec__12___redArg(v_m_797_, v_query_798_, v_x_799_, v_x_800_, v_x_801_);
lean_dec(v_query_798_);
lean_dec_ref(v_m_797_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10___redArg(lean_object* v_m_803_, lean_object* v_query_804_){
_start:
{
lean_object* v_keyArray_805_; lean_object* v___x_806_; uint64_t v___y_808_; 
v_keyArray_805_ = lean_ctor_get(v_m_803_, 1);
v___x_806_ = lean_array_get_size(v_keyArray_805_);
if (lean_obj_tag(v_query_804_) == 0)
{
uint64_t v___x_823_; 
v___x_823_ = 1723ULL;
v___y_808_ = v___x_823_;
goto v___jp_807_;
}
else
{
uint64_t v_hash_824_; 
v_hash_824_ = lean_ctor_get_uint64(v_query_804_, sizeof(void*)*2);
v___y_808_ = v_hash_824_;
goto v___jp_807_;
}
v___jp_807_:
{
uint64_t v___x_809_; uint64_t v___x_810_; uint64_t v_fold_811_; uint64_t v___x_812_; uint64_t v___x_813_; uint64_t v___x_814_; size_t v___x_815_; size_t v___x_816_; size_t v___x_817_; size_t v___x_818_; size_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_809_ = 32ULL;
v___x_810_ = lean_uint64_shift_right(v___y_808_, v___x_809_);
v_fold_811_ = lean_uint64_xor(v___y_808_, v___x_810_);
v___x_812_ = 16ULL;
v___x_813_ = lean_uint64_shift_right(v_fold_811_, v___x_812_);
v___x_814_ = lean_uint64_xor(v_fold_811_, v___x_813_);
v___x_815_ = lean_uint64_to_usize(v___x_814_);
v___x_816_ = lean_usize_of_nat(v___x_806_);
v___x_817_ = ((size_t)1ULL);
v___x_818_ = lean_usize_sub(v___x_816_, v___x_817_);
v___x_819_ = lean_usize_land(v___x_815_, v___x_818_);
v___x_820_ = lean_usize_to_nat(v___x_819_);
v___x_821_ = lean_box(0);
v___x_822_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10_spec__12___redArg(v_m_803_, v_query_804_, v___x_821_, v___x_806_, v___x_820_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v_m_825_, lean_object* v_query_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10___redArg(v_m_825_, v_query_826_);
lean_dec(v_query_826_);
lean_dec_ref(v_m_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(lean_object* v_m_828_, lean_object* v_query_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10___redArg(v_m_828_, v_query_829_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_index_831_; lean_object* v_key_832_; lean_object* v_value_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
v_index_831_ = lean_ctor_get(v___x_830_, 0);
v_key_832_ = lean_ctor_get(v___x_830_, 1);
v_value_833_ = lean_ctor_get(v___x_830_, 2);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_830_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_value_833_);
lean_inc(v_key_832_);
lean_inc(v_index_831_);
lean_dec(v___x_830_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_index_831_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_key_832_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v_value_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
else
{
lean_object* v___x_841_; 
lean_dec(v___x_830_);
v___x_841_ = lean_box(1);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_m_842_, lean_object* v_query_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(v_m_842_, v_query_843_);
lean_dec(v_query_843_);
lean_dec_ref(v_m_842_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg(lean_object* v_m_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(v_m_845_, v_a_846_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_value_848_; lean_object* v___x_849_; 
v_value_848_ = lean_ctor_get(v___x_847_, 2);
lean_inc(v_value_848_);
lean_dec_ref_known(v___x_847_, 3);
v___x_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_849_, 0, v_value_848_);
return v___x_849_;
}
else
{
lean_object* v___x_850_; 
v___x_850_ = lean_box(0);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___boxed(lean_object* v_m_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg(v_m_851_, v_a_852_);
lean_dec(v_a_852_);
lean_dec_ref(v_m_851_);
return v_res_853_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_856_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__1));
v___x_857_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__0));
v___x_858_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_857_, v___x_856_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0(lean_object* v_declName_861_, uint8_t v_isMeta_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; lean_object* v_env_874_; lean_object* v___y_876_; lean_object* v___x_889_; 
v___x_870_ = lean_st_ref_get(v___y_868_);
v_env_874_ = lean_ctor_get(v___x_870_, 0);
lean_inc_ref(v_env_874_);
lean_dec(v___x_870_);
v___x_889_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_874_, v_declName_861_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_dec_ref(v_env_874_);
lean_dec(v_declName_861_);
goto v___jp_871_;
}
else
{
lean_object* v_val_890_; lean_object* v___x_891_; lean_object* v_modules_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v_val_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_val_890_);
lean_dec_ref_known(v___x_889_, 1);
v___x_891_ = l_Lean_Environment_header(v_env_874_);
v_modules_892_ = lean_ctor_get(v___x_891_, 3);
lean_inc_ref(v_modules_892_);
lean_dec_ref(v___x_891_);
v___x_893_ = lean_array_get_size(v_modules_892_);
v___x_894_ = lean_nat_dec_lt(v_val_890_, v___x_893_);
if (v___x_894_ == 0)
{
lean_dec_ref(v_modules_892_);
lean_dec(v_val_890_);
lean_dec_ref(v_env_874_);
lean_dec(v_declName_861_);
goto v___jp_871_;
}
else
{
lean_object* v___x_895_; lean_object* v_env_896_; lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___y_900_; 
v___x_895_ = lean_st_ref_get(v___y_868_);
v_env_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc_ref(v_env_896_);
lean_dec(v___x_895_);
v___x_897_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2);
v___x_898_ = lean_array_fget(v_modules_892_, v_val_890_);
lean_dec(v_val_890_);
lean_dec_ref(v_modules_892_);
if (v_isMeta_862_ == 0)
{
lean_dec_ref(v_env_896_);
v___y_900_ = v_isMeta_862_;
goto v___jp_899_;
}
else
{
uint8_t v___x_911_; 
lean_inc(v_declName_861_);
v___x_911_ = l_Lean_isMarkedMeta(v_env_896_, v_declName_861_);
if (v___x_911_ == 0)
{
v___y_900_ = v_isMeta_862_;
goto v___jp_899_;
}
else
{
uint8_t v___x_912_; 
v___x_912_ = 0;
v___y_900_ = v___x_912_;
goto v___jp_899_;
}
}
v___jp_899_:
{
lean_object* v_toImport_901_; lean_object* v_module_902_; lean_object* v___x_903_; 
v_toImport_901_ = lean_ctor_get(v___x_898_, 0);
lean_inc_ref(v_toImport_901_);
lean_dec(v___x_898_);
v_module_902_ = lean_ctor_get(v_toImport_901_, 0);
lean_inc(v_module_902_);
lean_dec_ref(v_toImport_901_);
lean_inc(v_declName_861_);
v___x_903_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0(v_module_902_, v___y_900_, v_declName_861_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
lean_dec_ref_known(v___x_903_, 1);
v___x_904_ = l_Lean_indirectModUseExt;
v___x_905_ = lean_box(1);
v___x_906_ = lean_box(0);
lean_inc_ref(v_env_874_);
v___x_907_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_897_, v___x_904_, v_env_874_, v___x_905_, v___x_906_);
v___x_908_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg(v___x_907_, v_declName_861_);
lean_dec(v___x_907_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v___x_909_; 
v___x_909_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__3));
v___y_876_ = v___x_909_;
goto v___jp_875_;
}
else
{
lean_object* v_val_910_; 
v_val_910_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_val_910_);
lean_dec_ref_known(v___x_908_, 1);
v___y_876_ = v_val_910_;
goto v___jp_875_;
}
}
else
{
lean_dec_ref(v_env_874_);
lean_dec(v_declName_861_);
return v___x_903_;
}
}
}
}
v___jp_871_:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = lean_box(0);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
v___jp_875_:
{
lean_object* v___x_877_; size_t v_sz_878_; size_t v___x_879_; lean_object* v___x_880_; 
v___x_877_ = lean_box(0);
v_sz_878_ = lean_array_size(v___y_876_);
v___x_879_ = ((size_t)0ULL);
v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1(v_env_874_, v_declName_861_, v___y_876_, v_sz_878_, v___x_879_, v___x_877_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec_ref(v___y_876_);
lean_dec_ref(v_env_874_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_887_ == 0)
{
lean_object* v_unused_888_; 
v_unused_888_ = lean_ctor_get(v___x_880_, 0);
lean_dec(v_unused_888_);
v___x_882_ = v___x_880_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_dec(v___x_880_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_877_);
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_877_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
else
{
return v___x_880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___boxed(lean_object* v_declName_913_, lean_object* v_isMeta_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
uint8_t v_isMeta_boxed_922_; lean_object* v_res_923_; 
v_isMeta_boxed_922_ = lean_unbox(v_isMeta_914_);
v_res_923_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0(v_declName_913_, v_isMeta_boxed_922_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0(lean_object* v___x_924_, lean_object* v___x_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_924_, v___x_925_, v___y_930_, v___y_931_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; uint8_t v___x_935_; lean_object* v___x_936_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc_n(v_a_934_, 2);
lean_dec_ref_known(v___x_933_, 1);
v___x_935_ = 0;
v___x_936_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0(v_a_934_, v___x_935_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; 
v_unused_944_ = lean_ctor_get(v___x_936_, 0);
lean_dec(v_unused_944_);
v___x_938_ = v___x_936_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_dec(v___x_936_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v_a_934_);
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_934_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec(v_a_934_);
v_a_945_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_936_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_936_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0___boxed(lean_object* v___x_953_, lean_object* v___x_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0(v___x_953_, v___x_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0(lean_object* v___y_963_, uint8_t v_isExporting_964_, lean_object* v___x_965_, lean_object* v___y_966_, lean_object* v___x_967_, lean_object* v_a_x3f_968_){
_start:
{
lean_object* v___x_970_; lean_object* v_env_971_; lean_object* v_nextMacroScope_972_; lean_object* v_ngen_973_; lean_object* v_auxDeclNGen_974_; lean_object* v_traceState_975_; lean_object* v_messages_976_; lean_object* v_infoState_977_; lean_object* v_snapshotTasks_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1003_; 
v___x_970_ = lean_st_ref_take(v___y_963_);
v_env_971_ = lean_ctor_get(v___x_970_, 0);
v_nextMacroScope_972_ = lean_ctor_get(v___x_970_, 1);
v_ngen_973_ = lean_ctor_get(v___x_970_, 2);
v_auxDeclNGen_974_ = lean_ctor_get(v___x_970_, 3);
v_traceState_975_ = lean_ctor_get(v___x_970_, 4);
v_messages_976_ = lean_ctor_get(v___x_970_, 6);
v_infoState_977_ = lean_ctor_get(v___x_970_, 7);
v_snapshotTasks_978_ = lean_ctor_get(v___x_970_, 8);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; 
v_unused_1004_ = lean_ctor_get(v___x_970_, 5);
lean_dec(v_unused_1004_);
v___x_980_ = v___x_970_;
v_isShared_981_ = v_isSharedCheck_1003_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_snapshotTasks_978_);
lean_inc(v_infoState_977_);
lean_inc(v_messages_976_);
lean_inc(v_traceState_975_);
lean_inc(v_auxDeclNGen_974_);
lean_inc(v_ngen_973_);
lean_inc(v_nextMacroScope_972_);
lean_inc(v_env_971_);
lean_dec(v___x_970_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1003_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = l_Lean_Environment_setExporting(v_env_971_, v_isExporting_964_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 5, v___x_965_);
lean_ctor_set(v___x_980_, 0, v___x_982_);
v___x_984_ = v___x_980_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_nextMacroScope_972_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v_ngen_973_);
lean_ctor_set(v_reuseFailAlloc_1002_, 3, v_auxDeclNGen_974_);
lean_ctor_set(v_reuseFailAlloc_1002_, 4, v_traceState_975_);
lean_ctor_set(v_reuseFailAlloc_1002_, 5, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_1002_, 6, v_messages_976_);
lean_ctor_set(v_reuseFailAlloc_1002_, 7, v_infoState_977_);
lean_ctor_set(v_reuseFailAlloc_1002_, 8, v_snapshotTasks_978_);
v___x_984_ = v_reuseFailAlloc_1002_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v_mctx_987_; lean_object* v_zetaDeltaFVarIds_988_; lean_object* v_postponed_989_; lean_object* v_diag_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1000_; 
v___x_985_ = lean_st_ref_put(v___y_963_, v___x_984_);
v___x_986_ = lean_st_ref_take(v___y_966_);
v_mctx_987_ = lean_ctor_get(v___x_986_, 0);
v_zetaDeltaFVarIds_988_ = lean_ctor_get(v___x_986_, 2);
v_postponed_989_ = lean_ctor_get(v___x_986_, 3);
v_diag_990_ = lean_ctor_get(v___x_986_, 4);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; 
v_unused_1001_ = lean_ctor_get(v___x_986_, 1);
lean_dec(v_unused_1001_);
v___x_992_ = v___x_986_;
v_isShared_993_ = v_isSharedCheck_1000_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_diag_990_);
lean_inc(v_postponed_989_);
lean_inc(v_zetaDeltaFVarIds_988_);
lean_inc(v_mctx_987_);
lean_dec(v___x_986_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1000_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 1, v___x_967_);
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_mctx_987_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_zetaDeltaFVarIds_988_);
lean_ctor_set(v_reuseFailAlloc_999_, 3, v_postponed_989_);
lean_ctor_set(v_reuseFailAlloc_999_, 4, v_diag_990_);
v___x_995_ = v_reuseFailAlloc_999_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = lean_st_ref_put(v___y_966_, v___x_995_);
v___x_997_ = lean_box(0);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v___y_1005_, lean_object* v_isExporting_1006_, lean_object* v___x_1007_, lean_object* v___y_1008_, lean_object* v___x_1009_, lean_object* v_a_x3f_1010_, lean_object* v___y_1011_){
_start:
{
uint8_t v_isExporting_boxed_1012_; lean_object* v_res_1013_; 
v_isExporting_boxed_1012_ = lean_unbox(v_isExporting_1006_);
v_res_1013_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0(v___y_1005_, v_isExporting_boxed_1012_, v___x_1007_, v___y_1008_, v___x_1009_, v_a_x3f_1010_);
lean_dec(v_a_x3f_1010_);
lean_dec(v___y_1008_);
lean_dec(v___y_1005_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg(lean_object* v_x_1014_, uint8_t v_isExporting_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; lean_object* v_env_1024_; uint8_t v_isExporting_1025_; lean_object* v___x_1091_; uint8_t v_isModule_1092_; 
v___x_1023_ = lean_st_ref_get(v___y_1021_);
v_env_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc_ref(v_env_1024_);
lean_dec(v___x_1023_);
v_isExporting_1025_ = lean_ctor_get_uint8(v_env_1024_, sizeof(void*)*8);
v___x_1091_ = l_Lean_Environment_header(v_env_1024_);
lean_dec_ref(v_env_1024_);
v_isModule_1092_ = lean_ctor_get_uint8(v___x_1091_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1091_);
if (v_isModule_1092_ == 0)
{
lean_object* v___x_1093_; 
lean_inc(v___y_1021_);
lean_inc_ref(v___y_1020_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
v___x_1093_ = lean_apply_7(v_x_1014_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, lean_box(0));
return v___x_1093_;
}
else
{
if (v_isExporting_1025_ == 0)
{
if (v_isExporting_1015_ == 0)
{
lean_object* v___x_1094_; 
lean_inc(v___y_1021_);
lean_inc_ref(v___y_1020_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
v___x_1094_ = lean_apply_7(v_x_1014_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, lean_box(0));
return v___x_1094_;
}
else
{
goto v___jp_1026_;
}
}
else
{
if (v_isExporting_1015_ == 0)
{
goto v___jp_1026_;
}
else
{
lean_object* v___x_1095_; 
lean_inc(v___y_1021_);
lean_inc_ref(v___y_1020_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
v___x_1095_ = lean_apply_7(v_x_1014_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, lean_box(0));
return v___x_1095_;
}
}
}
v___jp_1026_:
{
lean_object* v___x_1027_; lean_object* v_env_1028_; lean_object* v_nextMacroScope_1029_; lean_object* v_ngen_1030_; lean_object* v_auxDeclNGen_1031_; lean_object* v_traceState_1032_; lean_object* v_messages_1033_; lean_object* v_infoState_1034_; lean_object* v_snapshotTasks_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1089_; 
v___x_1027_ = lean_st_ref_take(v___y_1021_);
v_env_1028_ = lean_ctor_get(v___x_1027_, 0);
v_nextMacroScope_1029_ = lean_ctor_get(v___x_1027_, 1);
v_ngen_1030_ = lean_ctor_get(v___x_1027_, 2);
v_auxDeclNGen_1031_ = lean_ctor_get(v___x_1027_, 3);
v_traceState_1032_ = lean_ctor_get(v___x_1027_, 4);
v_messages_1033_ = lean_ctor_get(v___x_1027_, 6);
v_infoState_1034_ = lean_ctor_get(v___x_1027_, 7);
v_snapshotTasks_1035_ = lean_ctor_get(v___x_1027_, 8);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; 
v_unused_1090_ = lean_ctor_get(v___x_1027_, 5);
lean_dec(v_unused_1090_);
v___x_1037_ = v___x_1027_;
v_isShared_1038_ = v_isSharedCheck_1089_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_snapshotTasks_1035_);
lean_inc(v_infoState_1034_);
lean_inc(v_messages_1033_);
lean_inc(v_traceState_1032_);
lean_inc(v_auxDeclNGen_1031_);
lean_inc(v_ngen_1030_);
lean_inc(v_nextMacroScope_1029_);
lean_inc(v_env_1028_);
lean_dec(v___x_1027_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1089_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1039_ = l_Lean_Environment_setExporting(v_env_1028_, v_isExporting_1015_);
v___x_1040_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 5, v___x_1040_);
lean_ctor_set(v___x_1037_, 0, v___x_1039_);
v___x_1042_ = v___x_1037_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_nextMacroScope_1029_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_ngen_1030_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v_auxDeclNGen_1031_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v_traceState_1032_);
lean_ctor_set(v_reuseFailAlloc_1088_, 5, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1088_, 6, v_messages_1033_);
lean_ctor_set(v_reuseFailAlloc_1088_, 7, v_infoState_1034_);
lean_ctor_set(v_reuseFailAlloc_1088_, 8, v_snapshotTasks_1035_);
v___x_1042_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v_mctx_1045_; lean_object* v_zetaDeltaFVarIds_1046_; lean_object* v_postponed_1047_; lean_object* v_diag_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1086_; 
v___x_1043_ = lean_st_ref_put(v___y_1021_, v___x_1042_);
v___x_1044_ = lean_st_ref_take(v___y_1019_);
v_mctx_1045_ = lean_ctor_get(v___x_1044_, 0);
v_zetaDeltaFVarIds_1046_ = lean_ctor_get(v___x_1044_, 2);
v_postponed_1047_ = lean_ctor_get(v___x_1044_, 3);
v_diag_1048_ = lean_ctor_get(v___x_1044_, 4);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; 
v_unused_1087_ = lean_ctor_get(v___x_1044_, 1);
lean_dec(v_unused_1087_);
v___x_1050_ = v___x_1044_;
v_isShared_1051_ = v_isSharedCheck_1086_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_diag_1048_);
lean_inc(v_postponed_1047_);
lean_inc(v_zetaDeltaFVarIds_1046_);
lean_inc(v_mctx_1045_);
lean_dec(v___x_1044_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1086_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1052_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v___x_1052_);
v___x_1054_ = v___x_1050_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_mctx_1045_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v_zetaDeltaFVarIds_1046_);
lean_ctor_set(v_reuseFailAlloc_1085_, 3, v_postponed_1047_);
lean_ctor_set(v_reuseFailAlloc_1085_, 4, v_diag_1048_);
v___x_1054_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; lean_object* v_r_1056_; 
v___x_1055_ = lean_st_ref_put(v___y_1019_, v___x_1054_);
lean_inc(v___y_1021_);
lean_inc_ref(v___y_1020_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
v_r_1056_ = lean_apply_7(v_x_1014_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, lean_box(0));
if (lean_obj_tag(v_r_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1073_; 
v_a_1057_ = lean_ctor_get(v_r_1056_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_r_1056_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1059_ = v_r_1056_;
v_isShared_1060_ = v_isSharedCheck_1073_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v_r_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1073_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
lean_inc(v_a_1057_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set_tag(v___x_1059_, 1);
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
v___x_1063_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0(v___y_1021_, v_isExporting_1025_, v___x_1040_, v___y_1019_, v___x_1052_, v___x_1062_);
lean_dec_ref(v___x_1062_);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; 
v_unused_1071_ = lean_ctor_get(v___x_1063_, 0);
lean_dec(v_unused_1071_);
v___x_1065_ = v___x_1063_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_dec(v___x_1063_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v_a_1057_);
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1057_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
v_a_1074_ = lean_ctor_get(v_r_1056_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v_r_1056_, 1);
v___x_1075_ = lean_box(0);
v___x_1076_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0(v___y_1021_, v_isExporting_1025_, v___x_1040_, v___y_1019_, v___x_1052_, v___x_1075_);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v___x_1076_, 0);
lean_dec(v_unused_1084_);
v___x_1078_ = v___x_1076_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_dec(v___x_1076_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set_tag(v___x_1078_, 1);
lean_ctor_set(v___x_1078_, 0, v_a_1074_);
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1074_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___boxed(lean_object* v_x_1096_, lean_object* v_isExporting_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
uint8_t v_isExporting_boxed_1105_; lean_object* v_res_1106_; 
v_isExporting_boxed_1105_ = lean_unbox(v_isExporting_1097_);
v_res_1106_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg(v_x_1096_, v_isExporting_boxed_1105_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg(lean_object* v_x_1107_, uint8_t v_when_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
if (v_when_1108_ == 0)
{
lean_object* v___x_1116_; 
lean_inc(v___y_1114_);
lean_inc_ref(v___y_1113_);
lean_inc(v___y_1112_);
lean_inc_ref(v___y_1111_);
lean_inc(v___y_1110_);
lean_inc_ref(v___y_1109_);
v___x_1116_ = lean_apply_7(v_x_1107_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, lean_box(0));
return v___x_1116_;
}
else
{
uint8_t v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = 0;
v___x_1118_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg(v_x_1107_, v___x_1117_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
return v___x_1118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg___boxed(lean_object* v_x_1119_, lean_object* v_when_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
uint8_t v_when_boxed_1128_; lean_object* v_res_1129_; 
v_when_boxed_1128_ = lean_unbox(v_when_1120_);
v_res_1129_ = l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg(v_x_1119_, v_when_boxed_1128_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1(lean_object* v___x_1131_, lean_object* v___x_1132_, lean_object* v_____r_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1141_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12));
v___x_1142_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13));
v___x_1143_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___closed__0));
v___x_1144_ = l_Lean_Name_mkStr4(v___x_1131_, v___x_1141_, v___x_1142_, v___x_1143_);
lean_inc(v___x_1132_);
v___x_1145_ = l_Lean_Syntax_isOfKind(v___x_1132_, v___x_1144_);
lean_dec(v___x_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; 
lean_dec(v___x_1132_);
v___x_1146_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___f_1150_; lean_object* v___x_1151_; 
v___x_1147_ = lean_unsigned_to_nat(2u);
v___x_1148_ = l_Lean_Syntax_getArg(v___x_1132_, v___x_1147_);
lean_dec(v___x_1132_);
v___x_1149_ = lean_box(0);
v___f_1150_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1150_, 0, v___x_1148_);
lean_closure_set(v___f_1150_, 1, v___x_1149_);
v___x_1151_ = l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg(v___f_1150_, v___x_1145_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___boxed(lean_object* v___x_1152_, lean_object* v___x_1153_, lean_object* v_____r_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1(v___x_1152_, v___x_1153_, v_____r_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
return v_res_1162_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1167_ = lean_box(0);
v___x_1168_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1));
v___x_1169_ = l_Lean_mkConst(v___x_1168_, v___x_1167_);
return v___x_1169_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2);
v___x_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx(lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_fileName_1186_; lean_object* v_fileMap_1187_; lean_object* v_options_1188_; lean_object* v_currRecDepth_1189_; lean_object* v_maxRecDepth_1190_; lean_object* v_ref_1191_; lean_object* v_currNamespace_1192_; lean_object* v_openDecls_1193_; lean_object* v_initHeartbeats_1194_; lean_object* v_maxHeartbeats_1195_; lean_object* v_quotContext_1196_; lean_object* v_currMacroScope_1197_; uint8_t v_diag_1198_; lean_object* v_cancelTk_x3f_1199_; uint8_t v_suppressElabErrors_1200_; lean_object* v_inheritedTraceOptions_1201_; lean_object* v___x_1202_; lean_object* v_a_1204_; lean_object* v___y_1233_; lean_object* v___x_1243_; lean_object* v_ref_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
v_fileName_1186_ = lean_ctor_get(v_a_1183_, 0);
v_fileMap_1187_ = lean_ctor_get(v_a_1183_, 1);
v_options_1188_ = lean_ctor_get(v_a_1183_, 2);
v_currRecDepth_1189_ = lean_ctor_get(v_a_1183_, 3);
v_maxRecDepth_1190_ = lean_ctor_get(v_a_1183_, 4);
v_ref_1191_ = lean_ctor_get(v_a_1183_, 5);
v_currNamespace_1192_ = lean_ctor_get(v_a_1183_, 6);
v_openDecls_1193_ = lean_ctor_get(v_a_1183_, 7);
v_initHeartbeats_1194_ = lean_ctor_get(v_a_1183_, 8);
v_maxHeartbeats_1195_ = lean_ctor_get(v_a_1183_, 9);
v_quotContext_1196_ = lean_ctor_get(v_a_1183_, 10);
v_currMacroScope_1197_ = lean_ctor_get(v_a_1183_, 11);
v_diag_1198_ = lean_ctor_get_uint8(v_a_1183_, sizeof(void*)*14);
v_cancelTk_x3f_1199_ = lean_ctor_get(v_a_1183_, 12);
v_suppressElabErrors_1200_ = lean_ctor_get_uint8(v_a_1183_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1201_ = lean_ctor_get(v_a_1183_, 13);
v___x_1202_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11));
lean_inc(v_a_1178_);
v___x_1243_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_a_1178_);
v_ref_1244_ = l_Lean_replaceRef(v_a_1178_, v_ref_1191_);
lean_inc_ref(v_inheritedTraceOptions_1201_);
lean_inc(v_cancelTk_x3f_1199_);
lean_inc(v_currMacroScope_1197_);
lean_inc(v_quotContext_1196_);
lean_inc(v_maxHeartbeats_1195_);
lean_inc(v_initHeartbeats_1194_);
lean_inc(v_openDecls_1193_);
lean_inc(v_currNamespace_1192_);
lean_inc(v_maxRecDepth_1190_);
lean_inc(v_currRecDepth_1189_);
lean_inc_ref(v_options_1188_);
lean_inc_ref(v_fileMap_1187_);
lean_inc_ref(v_fileName_1186_);
v___x_1245_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1245_, 0, v_fileName_1186_);
lean_ctor_set(v___x_1245_, 1, v_fileMap_1187_);
lean_ctor_set(v___x_1245_, 2, v_options_1188_);
lean_ctor_set(v___x_1245_, 3, v_currRecDepth_1189_);
lean_ctor_set(v___x_1245_, 4, v_maxRecDepth_1190_);
lean_ctor_set(v___x_1245_, 5, v_ref_1244_);
lean_ctor_set(v___x_1245_, 6, v_currNamespace_1192_);
lean_ctor_set(v___x_1245_, 7, v_openDecls_1193_);
lean_ctor_set(v___x_1245_, 8, v_initHeartbeats_1194_);
lean_ctor_set(v___x_1245_, 9, v_maxHeartbeats_1195_);
lean_ctor_set(v___x_1245_, 10, v_quotContext_1196_);
lean_ctor_set(v___x_1245_, 11, v_currMacroScope_1197_);
lean_ctor_set(v___x_1245_, 12, v_cancelTk_x3f_1199_);
lean_ctor_set(v___x_1245_, 13, v_inheritedTraceOptions_1201_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*14, v_diag_1198_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*14 + 1, v_suppressElabErrors_1200_);
v___x_1246_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5));
lean_inc(v___x_1243_);
v___x_1247_ = l_Lean_Syntax_isOfKind(v___x_1243_, v___x_1246_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = lean_box(0);
v___x_1249_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1(v___x_1202_, v___x_1243_, v___x_1248_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v___x_1245_, v_a_1184_);
lean_dec_ref_known(v___x_1245_, 14);
v___y_1233_ = v___x_1249_;
goto v___jp_1232_;
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = l_Lean_Syntax_getArg(v___x_1243_, v___x_1250_);
v___x_1252_ = l_Lean_Syntax_isNameLit_x3f(v___x_1251_);
lean_dec(v___x_1251_);
if (lean_obj_tag(v___x_1252_) == 1)
{
lean_object* v_val_1253_; 
lean_dec_ref_known(v___x_1245_, 14);
lean_dec(v___x_1243_);
v_val_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_val_1253_);
lean_dec_ref_known(v___x_1252_, 1);
v_a_1204_ = v_val_1253_;
goto v___jp_1203_;
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_dec(v___x_1252_);
v___x_1254_ = lean_box(0);
v___x_1255_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1(v___x_1202_, v___x_1243_, v___x_1254_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v___x_1245_, v_a_1184_);
lean_dec_ref_known(v___x_1245_, 14);
v___y_1233_ = v___x_1255_;
goto v___jp_1232_;
}
}
v___jp_1203_:
{
lean_object* v___x_1205_; lean_object* v_infoState_1206_; uint8_t v_enabled_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1205_ = lean_st_ref_get(v_a_1184_);
v_infoState_1206_ = lean_ctor_get(v___x_1205_, 7);
lean_inc_ref(v_infoState_1206_);
lean_dec(v___x_1205_);
v_enabled_1207_ = lean_ctor_get_uint8(v_infoState_1206_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1206_);
lean_inc(v_a_1204_);
v___x_1208_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_1204_);
lean_inc_ref(v___x_1208_);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v_a_1204_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
if (v_enabled_1207_ == 0)
{
lean_object* v___x_1210_; 
lean_dec_ref(v___x_1208_);
lean_dec(v_a_1178_);
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
return v___x_1210_;
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; lean_object* v___x_1215_; 
v___x_1211_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3);
v___x_1212_ = lean_box(0);
v___x_1213_ = lean_box(0);
v___x_1214_ = 0;
v___x_1215_ = l_Lean_Elab_Term_addTermInfo_x27(v_a_1178_, v___x_1208_, v___x_1211_, v___x_1212_, v___x_1213_, v___x_1214_, v___x_1214_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v___x_1215_, 0);
lean_dec(v_unused_1223_);
v___x_1217_ = v___x_1215_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_dec(v___x_1215_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1209_);
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1209_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec_ref_known(v___x_1209_, 2);
v_a_1224_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1215_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1215_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
}
v___jp_1232_:
{
if (lean_obj_tag(v___y_1233_) == 0)
{
lean_object* v_a_1234_; 
v_a_1234_ = lean_ctor_get(v___y_1233_, 0);
lean_inc(v_a_1234_);
lean_dec_ref_known(v___y_1233_, 1);
v_a_1204_ = v_a_1234_;
goto v___jp_1203_;
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec(v_a_1178_);
v_a_1235_ = lean_ctor_get(v___y_1233_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___y_1233_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___y_1233_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___y_1233_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___boxed(lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx(v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4(lean_object* v_00_u03b1_1265_, lean_object* v_x_1266_, uint8_t v_isExporting_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg(v_x_1266_, v_isExporting_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1276_, lean_object* v_x_1277_, lean_object* v_isExporting_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
uint8_t v_isExporting_boxed_1286_; lean_object* v_res_1287_; 
v_isExporting_boxed_1286_ = lean_unbox(v_isExporting_1278_);
v_res_1287_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4(v_00_u03b1_1276_, v_x_1277_, v_isExporting_boxed_1286_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1(lean_object* v_00_u03b1_1288_, lean_object* v_x_1289_, uint8_t v_when_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg(v_x_1289_, v_when_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___boxed(lean_object* v_00_u03b1_1299_, lean_object* v_x_1300_, lean_object* v_when_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
uint8_t v_when_boxed_1309_; lean_object* v_res_1310_; 
v_when_boxed_1309_ = lean_unbox(v_when_1301_);
v_res_1310_ = l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1(v_00_u03b1_1299_, v_x_1300_, v_when_boxed_1309_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2(lean_object* v_00_u03b2_1311_, lean_object* v_m_1312_, lean_object* v_a_1313_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg(v_m_1312_, v_a_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1315_, lean_object* v_m_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2(v_00_u03b2_1315_, v_m_1316_, v_a_1317_);
lean_dec(v_a_1317_);
lean_dec_ref(v_m_1316_);
return v_res_1318_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1319_, lean_object* v_x_1320_, lean_object* v_x_1321_){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg(v_x_1320_, v_x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1323_, lean_object* v_x_1324_, lean_object* v_x_1325_){
_start:
{
uint8_t v_res_1326_; lean_object* v_r_1327_; 
v_res_1326_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1(v_00_u03b2_1323_, v_x_1324_, v_x_1325_);
lean_dec_ref(v_x_1325_);
lean_dec_ref(v_x_1324_);
v_r_1327_ = lean_box(v_res_1326_);
return v_r_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2(lean_object* v_cls_1328_, lean_object* v_msg_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg(v_cls_1328_, v_msg_1329_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1338_, lean_object* v_msg_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2(v_cls_1338_, v_msg_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1348_, lean_object* v_m_1349_, lean_object* v_query_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(v_m_1349_, v_query_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1352_, lean_object* v_m_1353_, lean_object* v_query_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5(v_00_u03b2_1352_, v_m_1353_, v_query_1354_);
lean_dec(v_query_1354_);
lean_dec_ref(v_m_1353_);
return v_res_1355_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1356_, lean_object* v_x_1357_, size_t v_x_1358_, lean_object* v_x_1359_){
_start:
{
uint8_t v___x_1360_; 
v___x_1360_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg(v_x_1357_, v_x_1358_, v_x_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1361_, lean_object* v_x_1362_, lean_object* v_x_1363_, lean_object* v_x_1364_){
_start:
{
size_t v_x_11801__boxed_1365_; uint8_t v_res_1366_; lean_object* v_r_1367_; 
v_x_11801__boxed_1365_ = lean_unbox_usize(v_x_1363_);
lean_dec(v_x_1363_);
v_res_1366_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_1361_, v_x_1362_, v_x_11801__boxed_1365_, v_x_1364_);
lean_dec_ref(v_x_1364_);
lean_dec_ref(v_x_1362_);
v_r_1367_ = lean_box(v_res_1366_);
return v_r_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_1368_, lean_object* v_m_1369_, lean_object* v_query_1370_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10___redArg(v_m_1369_, v_query_1370_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10___boxed(lean_object* v_00_u03b2_1372_, lean_object* v_m_1373_, lean_object* v_query_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10(v_00_u03b2_1372_, v_m_1373_, v_query_1374_);
lean_dec(v_query_1374_);
lean_dec_ref(v_m_1373_);
return v_res_1375_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_1376_, lean_object* v_keys_1377_, lean_object* v_vals_1378_, lean_object* v_heq_1379_, lean_object* v_i_1380_, lean_object* v_k_1381_){
_start:
{
uint8_t v___x_1382_; 
v___x_1382_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_keys_1377_, v_i_1380_, v_k_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1383_, lean_object* v_keys_1384_, lean_object* v_vals_1385_, lean_object* v_heq_1386_, lean_object* v_i_1387_, lean_object* v_k_1388_){
_start:
{
uint8_t v_res_1389_; lean_object* v_r_1390_; 
v_res_1389_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7(v_00_u03b2_1383_, v_keys_1384_, v_vals_1385_, v_heq_1386_, v_i_1387_, v_k_1388_);
lean_dec_ref(v_k_1388_);
lean_dec_ref(v_vals_1385_);
lean_dec_ref(v_keys_1384_);
v_r_1390_ = lean_box(v_res_1389_);
return v_r_1390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10_spec__12(lean_object* v_00_u03b2_1391_, lean_object* v_m_1392_, lean_object* v_query_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_, lean_object* v_x_1396_, lean_object* v_x_1397_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10_spec__12___redArg(v_m_1392_, v_query_1393_, v_x_1394_, v_x_1395_, v_x_1396_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10_spec__12___boxed(lean_object* v_00_u03b2_1399_, lean_object* v_m_1400_, lean_object* v_query_1401_, lean_object* v_x_1402_, lean_object* v_x_1403_, lean_object* v_x_1404_, lean_object* v_x_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5_spec__10_spec__12(v_00_u03b2_1399_, v_m_1400_, v_query_1401_, v_x_1402_, v_x_1403_, v_x_1404_, v_x_1405_);
lean_dec(v_query_1401_);
lean_dec_ref(v_m_1400_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(lean_object* v_ev_1408_, lean_object* v___x_1409_, lean_object* v___x_1410_, lean_object* v_typeExpr_1411_, lean_object* v_stx_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1420_; 
lean_inc(v___y_1418_);
lean_inc_ref(v___y_1417_);
lean_inc(v___y_1416_);
lean_inc_ref(v___y_1415_);
lean_inc(v___y_1414_);
lean_inc_ref(v___y_1413_);
v___x_1420_ = lean_apply_8(v_ev_1408_, v_stx_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, lean_box(0));
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1442_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1442_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1442_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v_fst_1425_; lean_object* v_snd_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1441_; 
v_fst_1425_ = lean_ctor_get(v_a_1421_, 0);
v_snd_1426_ = lean_ctor_get(v_a_1421_, 1);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_a_1421_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1428_ = v_a_1421_;
v_isShared_1429_ = v_isSharedCheck_1441_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_snd_1426_);
lean_inc(v_fst_1425_);
lean_dec(v_a_1421_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1441_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1430_, 0, v_fst_1425_);
v___x_1431_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0));
v___x_1432_ = l_Lean_Name_mkStr2(v___x_1409_, v___x_1431_);
v___x_1433_ = l_Lean_Expr_const___override(v___x_1432_, v___x_1410_);
v___x_1434_ = l_Lean_mkAppB(v___x_1433_, v_typeExpr_1411_, v_snd_1426_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 1, v___x_1434_);
lean_ctor_set(v___x_1428_, 0, v___x_1430_);
v___x_1436_ = v___x_1428_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1438_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1436_);
v___x_1438_ = v___x_1423_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec_ref(v_typeExpr_1411_);
lean_dec(v___x_1410_);
lean_dec_ref(v___x_1409_);
v_a_1443_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1420_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1420_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___boxed(lean_object* v_ev_1451_, lean_object* v___x_1452_, lean_object* v___x_1453_, lean_object* v_typeExpr_1454_, lean_object* v_stx_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1451_, v___x_1452_, v___x_1453_, v_typeExpr_1454_, v_stx_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
return v_res_1463_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1468_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__1));
v___x_1469_ = l_Lean_Expr_const___override(v___x_1468_, v___x_1467_);
return v___x_1469_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1484_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1485_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8));
v___x_1486_ = l_Lean_Expr_const___override(v___x_1485_, v___x_1484_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(lean_object* v_typeExpr_1487_, lean_object* v_ev_1488_, lean_object* v_stx_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v_a_1504_; lean_object* v_snd_1505_; lean_object* v___y_1531_; lean_object* v___x_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1497_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0));
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1500_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2);
lean_inc_ref(v_typeExpr_1487_);
v___x_1501_ = l_Lean_Expr_app___override(v___x_1500_, v_typeExpr_1487_);
v___x_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
lean_inc(v_stx_1489_);
v___x_1534_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_1489_);
v___x_1535_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__4));
v___x_1536_ = l_Lean_Syntax_matchesIdent(v___x_1534_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_object* v_fileName_1537_; lean_object* v_fileMap_1538_; lean_object* v_options_1539_; lean_object* v_currRecDepth_1540_; lean_object* v_maxRecDepth_1541_; lean_object* v_ref_1542_; lean_object* v_currNamespace_1543_; lean_object* v_openDecls_1544_; lean_object* v_initHeartbeats_1545_; lean_object* v_maxHeartbeats_1546_; lean_object* v_quotContext_1547_; lean_object* v_currMacroScope_1548_; uint8_t v_diag_1549_; lean_object* v_cancelTk_x3f_1550_; uint8_t v_suppressElabErrors_1551_; lean_object* v_inheritedTraceOptions_1552_; lean_object* v_ref_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v_fileName_1537_ = lean_ctor_get(v_a_1494_, 0);
v_fileMap_1538_ = lean_ctor_get(v_a_1494_, 1);
v_options_1539_ = lean_ctor_get(v_a_1494_, 2);
v_currRecDepth_1540_ = lean_ctor_get(v_a_1494_, 3);
v_maxRecDepth_1541_ = lean_ctor_get(v_a_1494_, 4);
v_ref_1542_ = lean_ctor_get(v_a_1494_, 5);
v_currNamespace_1543_ = lean_ctor_get(v_a_1494_, 6);
v_openDecls_1544_ = lean_ctor_get(v_a_1494_, 7);
v_initHeartbeats_1545_ = lean_ctor_get(v_a_1494_, 8);
v_maxHeartbeats_1546_ = lean_ctor_get(v_a_1494_, 9);
v_quotContext_1547_ = lean_ctor_get(v_a_1494_, 10);
v_currMacroScope_1548_ = lean_ctor_get(v_a_1494_, 11);
v_diag_1549_ = lean_ctor_get_uint8(v_a_1494_, sizeof(void*)*14);
v_cancelTk_x3f_1550_ = lean_ctor_get(v_a_1494_, 12);
v_suppressElabErrors_1551_ = lean_ctor_get_uint8(v_a_1494_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1552_ = lean_ctor_get(v_a_1494_, 13);
v_ref_1553_ = l_Lean_replaceRef(v_stx_1489_, v_ref_1542_);
lean_inc_ref(v_inheritedTraceOptions_1552_);
lean_inc(v_cancelTk_x3f_1550_);
lean_inc(v_currMacroScope_1548_);
lean_inc(v_quotContext_1547_);
lean_inc(v_maxHeartbeats_1546_);
lean_inc(v_initHeartbeats_1545_);
lean_inc(v_openDecls_1544_);
lean_inc(v_currNamespace_1543_);
lean_inc(v_maxRecDepth_1541_);
lean_inc(v_currRecDepth_1540_);
lean_inc_ref(v_options_1539_);
lean_inc_ref(v_fileMap_1538_);
lean_inc_ref(v_fileName_1537_);
v___x_1554_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1554_, 0, v_fileName_1537_);
lean_ctor_set(v___x_1554_, 1, v_fileMap_1538_);
lean_ctor_set(v___x_1554_, 2, v_options_1539_);
lean_ctor_set(v___x_1554_, 3, v_currRecDepth_1540_);
lean_ctor_set(v___x_1554_, 4, v_maxRecDepth_1541_);
lean_ctor_set(v___x_1554_, 5, v_ref_1553_);
lean_ctor_set(v___x_1554_, 6, v_currNamespace_1543_);
lean_ctor_set(v___x_1554_, 7, v_openDecls_1544_);
lean_ctor_set(v___x_1554_, 8, v_initHeartbeats_1545_);
lean_ctor_set(v___x_1554_, 9, v_maxHeartbeats_1546_);
lean_ctor_set(v___x_1554_, 10, v_quotContext_1547_);
lean_ctor_set(v___x_1554_, 11, v_currMacroScope_1548_);
lean_ctor_set(v___x_1554_, 12, v_cancelTk_x3f_1550_);
lean_ctor_set(v___x_1554_, 13, v_inheritedTraceOptions_1552_);
lean_ctor_set_uint8(v___x_1554_, sizeof(void*)*14, v_diag_1549_);
lean_ctor_set_uint8(v___x_1554_, sizeof(void*)*14 + 1, v_suppressElabErrors_1551_);
v___x_1555_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15));
lean_inc(v___x_1534_);
v___x_1556_ = l_Lean_Syntax_isOfKind(v___x_1534_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1557_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6));
lean_inc(v___x_1534_);
v___x_1558_ = l_Lean_Syntax_isOfKind(v___x_1534_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1488_, v___x_1497_, v___x_1499_, v_typeExpr_1487_, v___x_1534_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v___x_1554_, v_a_1495_);
lean_dec_ref_known(v___x_1554_, 14);
v___y_1531_ = v___x_1559_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; 
v___x_1560_ = l_Lean_Syntax_getArg(v___x_1534_, v___x_1498_);
v___x_1561_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__7));
v___x_1562_ = l_Lean_Syntax_matchesIdent(v___x_1560_, v___x_1561_);
if (v___x_1562_ == 0)
{
uint8_t v___x_1563_; 
lean_inc(v___x_1560_);
v___x_1563_ = l_Lean_Syntax_isOfKind(v___x_1560_, v___x_1555_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; 
lean_dec(v___x_1560_);
v___x_1564_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1488_, v___x_1497_, v___x_1499_, v_typeExpr_1487_, v___x_1534_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v___x_1554_, v_a_1495_);
lean_dec_ref_known(v___x_1554_, 14);
v___y_1531_ = v___x_1564_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1565_ = lean_unsigned_to_nat(1u);
v___x_1566_ = l_Lean_Syntax_getArg(v___x_1560_, v___x_1565_);
lean_dec(v___x_1560_);
v___x_1567_ = l_Lean_Syntax_matchesIdent(v___x_1566_, v___x_1561_);
lean_dec(v___x_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1488_, v___x_1497_, v___x_1499_, v_typeExpr_1487_, v___x_1534_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v___x_1554_, v_a_1495_);
lean_dec_ref_known(v___x_1554_, 14);
v___y_1531_ = v___x_1568_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1569_ = l_Lean_Syntax_getArg(v___x_1534_, v___x_1565_);
lean_inc(v___x_1569_);
v___x_1570_ = l_Lean_Syntax_matchesNull(v___x_1569_, v___x_1565_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; 
lean_dec(v___x_1569_);
v___x_1571_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1488_, v___x_1497_, v___x_1499_, v_typeExpr_1487_, v___x_1534_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v___x_1554_, v_a_1495_);
lean_dec_ref_known(v___x_1554_, 14);
v___y_1531_ = v___x_1571_;
goto v___jp_1530_;
}
else
{
lean_object* v_stx_1572_; lean_object* v___x_1573_; 
lean_dec(v___x_1534_);
v_stx_1572_ = l_Lean_Syntax_getArg(v___x_1569_, v___x_1498_);
lean_dec(v___x_1569_);
v___x_1573_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1488_, v___x_1497_, v___x_1499_, v_typeExpr_1487_, v_stx_1572_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v___x_1554_, v_a_1495_);
lean_dec_ref_known(v___x_1554_, 14);
v___y_1531_ = v___x_1573_;
goto v___jp_1530_;
}
}
}
}
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v___x_1574_ = lean_unsigned_to_nat(1u);
v___x_1575_ = l_Lean_Syntax_getArg(v___x_1534_, v___x_1574_);
lean_inc(v___x_1575_);
v___x_1576_ = l_Lean_Syntax_matchesNull(v___x_1575_, v___x_1574_);
if (v___x_1576_ == 0)
{
uint8_t v___x_1577_; 
lean_inc(v___x_1560_);
v___x_1577_ = l_Lean_Syntax_isOfKind(v___x_1560_, v___x_1555_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; 
lean_dec(v___x_1575_);
lean_dec(v___x_1560_);
v___x_1578_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1488_, v___x_1497_, v___x_1499_, v_typeExpr_1487_, v___x_1534_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v___x_1554_, v_a_1495_);
lean_dec_ref_known(v___x_1554_, 14);
v___y_1531_ = v___x_1578_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1579_ = l_Lean_Syntax_getArg(v___x_1560_, v___x_1574_);
lean_dec(v___x_1560_);
v___x_1580_ = l_Lean_Syntax_matchesIdent(v___x_1579_, v___x_1561_);
lean_dec(v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; 
lean_dec(v___x_1575_);
v___x_1581_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1488_, v___x_1497_, v___x_1499_, v_typeExpr_1487_, v___x_1534_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v___x_1554_, v_a_1495_);
lean_dec_ref_known(v___x_1554_, 14);
v___y_1531_ = v___x_1581_;
goto v___jp_1530_;
}
else
{
if (v___x_1576_ == 0)
{
lean_object* v___x_1582_; 
lean_dec(v___x_1575_);
v___x_1582_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1488_, v___x_1497_, v___x_1499_, v_typeExpr_1487_, v___x_1534_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v___x_1554_, v_a_1495_);
lean_dec_ref_known(v___x_1554_, 14);
v___y_1531_ = v___x_1582_;
goto v___jp_1530_;
}
else
{
lean_object* v_stx_1583_; lean_object* v___x_1584_; 
lean_dec(v___x_1534_);
v_stx_1583_ = l_Lean_Syntax_getArg(v___x_1575_, v___x_1498_);
lean_dec(v___x_1575_);
v___x_1584_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1488_, v___x_1497_, v___x_1499_, v_typeExpr_1487_, v_stx_1583_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v___x_1554_, v_a_1495_);
lean_dec_ref_known(v___x_1554_, 14);
v___y_1531_ = v___x_1584_;
goto v___jp_1530_;
}
}
}
}
else
{
lean_object* v_stx_1585_; lean_object* v___x_1586_; 
lean_dec(v___x_1560_);
lean_dec(v___x_1534_);
v_stx_1585_ = l_Lean_Syntax_getArg(v___x_1575_, v___x_1498_);
lean_dec(v___x_1575_);
v___x_1586_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1488_, v___x_1497_, v___x_1499_, v_typeExpr_1487_, v_stx_1585_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v___x_1554_, v_a_1495_);
lean_dec_ref_known(v___x_1554_, 14);
v___y_1531_ = v___x_1586_;
goto v___jp_1530_;
}
}
}
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v___x_1587_ = lean_unsigned_to_nat(1u);
v___x_1588_ = l_Lean_Syntax_getArg(v___x_1534_, v___x_1587_);
v___x_1589_ = l_Lean_Syntax_matchesIdent(v___x_1588_, v___x_1535_);
lean_dec(v___x_1588_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1488_, v___x_1497_, v___x_1499_, v_typeExpr_1487_, v___x_1534_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v___x_1554_, v_a_1495_);
lean_dec_ref_known(v___x_1554_, 14);
v___y_1531_ = v___x_1590_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
lean_dec_ref_known(v___x_1554_, 14);
lean_dec(v___x_1534_);
lean_dec_ref(v_ev_1488_);
v___x_1591_ = lean_box(0);
v___x_1592_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9);
v___x_1593_ = l_Lean_Expr_app___override(v___x_1592_, v_typeExpr_1487_);
lean_inc_ref(v___x_1593_);
v___x_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1591_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v_a_1504_ = v___x_1594_;
v_snd_1505_ = v___x_1593_;
goto v___jp_1503_;
}
}
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec(v___x_1534_);
lean_dec_ref(v_ev_1488_);
v___x_1595_ = lean_box(0);
v___x_1596_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9);
v___x_1597_ = l_Lean_Expr_app___override(v___x_1596_, v_typeExpr_1487_);
lean_inc_ref(v___x_1597_);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1595_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v_a_1504_ = v___x_1598_;
v_snd_1505_ = v___x_1597_;
goto v___jp_1503_;
}
v___jp_1503_:
{
lean_object* v___x_1506_; lean_object* v_infoState_1507_; uint8_t v_enabled_1508_; 
v___x_1506_ = lean_st_ref_get(v_a_1495_);
v_infoState_1507_ = lean_ctor_get(v___x_1506_, 7);
lean_inc_ref(v_infoState_1507_);
lean_dec(v___x_1506_);
v_enabled_1508_ = lean_ctor_get_uint8(v_infoState_1507_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1507_);
if (v_enabled_1508_ == 0)
{
lean_object* v___x_1509_; 
lean_dec_ref(v_snd_1505_);
lean_dec_ref_known(v___x_1502_, 1);
lean_dec(v_stx_1489_);
v___x_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1509_, 0, v_a_1504_);
return v___x_1509_;
}
else
{
lean_object* v___x_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; lean_object* v___x_1513_; 
v___x_1510_ = lean_box(0);
v___x_1511_ = lean_box(0);
v___x_1512_ = 0;
v___x_1513_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_1489_, v_snd_1505_, v___x_1502_, v___x_1510_, v___x_1511_, v___x_1512_, v___x_1512_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1520_ == 0)
{
lean_object* v_unused_1521_; 
v_unused_1521_ = lean_ctor_get(v___x_1513_, 0);
lean_dec(v_unused_1521_);
v___x_1515_ = v___x_1513_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_dec(v___x_1513_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v_a_1504_);
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1504_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec_ref(v_a_1504_);
v_a_1522_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1513_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1513_);
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
}
v___jp_1530_:
{
if (lean_obj_tag(v___y_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v_snd_1533_; 
v_a_1532_ = lean_ctor_get(v___y_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___y_1531_, 1);
v_snd_1533_ = lean_ctor_get(v_a_1532_, 1);
lean_inc(v_snd_1533_);
v_a_1504_ = v_a_1532_;
v_snd_1505_ = v_snd_1533_;
goto v___jp_1503_;
}
else
{
lean_dec_ref_known(v___x_1502_, 1);
lean_dec(v_stx_1489_);
return v___y_1531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___boxed(lean_object* v_typeExpr_1599_, lean_object* v_ev_1600_, lean_object* v_stx_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(v_typeExpr_1599_, v_ev_1600_, v_stx_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx(lean_object* v_00_u03b1_1610_, lean_object* v_typeExpr_1611_, lean_object* v_ev_1612_, lean_object* v_stx_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(v_typeExpr_1611_, v_ev_1612_, v_stx_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___boxed(lean_object* v_00_u03b1_1622_, lean_object* v_typeExpr_1623_, lean_object* v_ev_1624_, lean_object* v_stx_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx(v_00_u03b1_1622_, v_typeExpr_1623_, v_ev_1624_, v_stx_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(lean_object* v_ev_1634_, size_t v_sz_1635_, size_t v_i_1636_, lean_object* v_bs_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
uint8_t v___x_1645_; 
v___x_1645_ = lean_usize_dec_lt(v_i_1636_, v_sz_1635_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; 
lean_dec_ref(v_ev_1634_);
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v_bs_1637_);
return v___x_1646_;
}
else
{
lean_object* v_v_1647_; lean_object* v___x_1648_; 
v_v_1647_ = lean_array_uget_borrowed(v_bs_1637_, v_i_1636_);
lean_inc_ref(v_ev_1634_);
lean_inc(v___y_1643_);
lean_inc_ref(v___y_1642_);
lean_inc(v___y_1641_);
lean_inc_ref(v___y_1640_);
lean_inc(v___y_1639_);
lean_inc_ref(v___y_1638_);
lean_inc(v_v_1647_);
v___x_1648_ = lean_apply_8(v_ev_1634_, v_v_1647_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, lean_box(0));
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1650_; lean_object* v_bs_x27_1651_; size_t v___x_1652_; size_t v___x_1653_; lean_object* v___x_1654_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v___x_1650_ = lean_unsigned_to_nat(0u);
v_bs_x27_1651_ = lean_array_uset(v_bs_1637_, v_i_1636_, v___x_1650_);
v___x_1652_ = ((size_t)1ULL);
v___x_1653_ = lean_usize_add(v_i_1636_, v___x_1652_);
v___x_1654_ = lean_array_uset(v_bs_x27_1651_, v_i_1636_, v_a_1649_);
v_i_1636_ = v___x_1653_;
v_bs_1637_ = v___x_1654_;
goto _start;
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec_ref(v_bs_1637_);
lean_dec_ref(v_ev_1634_);
v_a_1656_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1648_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1648_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg___boxed(lean_object* v_ev_1664_, lean_object* v_sz_1665_, lean_object* v_i_1666_, lean_object* v_bs_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
size_t v_sz_boxed_1675_; size_t v_i_boxed_1676_; lean_object* v_res_1677_; 
v_sz_boxed_1675_ = lean_unbox_usize(v_sz_1665_);
lean_dec(v_sz_1665_);
v_i_boxed_1676_ = lean_unbox_usize(v_i_1666_);
lean_dec(v_i_1666_);
v_res_1677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(v_ev_1664_, v_sz_boxed_1675_, v_i_boxed_1676_, v_bs_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(uint8_t v___x_1678_, lean_object* v_as_1679_, size_t v_i_1680_, size_t v_stop_1681_, lean_object* v_b_1682_){
_start:
{
lean_object* v___y_1684_; uint8_t v___x_1688_; 
v___x_1688_ = lean_usize_dec_eq(v_i_1680_, v_stop_1681_);
if (v___x_1688_ == 0)
{
lean_object* v_fst_1689_; uint8_t v___x_1690_; 
v_fst_1689_ = lean_ctor_get(v_b_1682_, 0);
v___x_1690_ = lean_unbox(v_fst_1689_);
if (v___x_1690_ == 0)
{
lean_object* v_snd_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1699_; 
v_snd_1691_ = lean_ctor_get(v_b_1682_, 1);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_b_1682_);
if (v_isSharedCheck_1699_ == 0)
{
lean_object* v_unused_1700_; 
v_unused_1700_ = lean_ctor_get(v_b_1682_, 0);
lean_dec(v_unused_1700_);
v___x_1693_ = v_b_1682_;
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_snd_1691_);
lean_dec(v_b_1682_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1695_ = lean_box(v___x_1678_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1695_);
v___x_1697_ = v___x_1693_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_snd_1691_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
v___y_1684_ = v___x_1697_;
goto v___jp_1683_;
}
}
}
else
{
lean_object* v_snd_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1711_; 
v_snd_1701_ = lean_ctor_get(v_b_1682_, 1);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_b_1682_);
if (v_isSharedCheck_1711_ == 0)
{
lean_object* v_unused_1712_; 
v_unused_1712_ = lean_ctor_get(v_b_1682_, 0);
lean_dec(v_unused_1712_);
v___x_1703_ = v_b_1682_;
v_isShared_1704_ = v_isSharedCheck_1711_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_snd_1701_);
lean_dec(v_b_1682_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1711_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1705_ = lean_array_uget_borrowed(v_as_1679_, v_i_1680_);
lean_inc(v___x_1705_);
v___x_1706_ = lean_array_push(v_snd_1701_, v___x_1705_);
v___x_1707_ = lean_box(v___x_1688_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 1, v___x_1706_);
lean_ctor_set(v___x_1703_, 0, v___x_1707_);
v___x_1709_ = v___x_1703_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v___x_1706_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
v___y_1684_ = v___x_1709_;
goto v___jp_1683_;
}
}
}
}
else
{
return v_b_1682_;
}
v___jp_1683_:
{
size_t v___x_1685_; size_t v___x_1686_; 
v___x_1685_ = ((size_t)1ULL);
v___x_1686_ = lean_usize_add(v_i_1680_, v___x_1685_);
v_i_1680_ = v___x_1686_;
v_b_1682_ = v___y_1684_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3___boxed(lean_object* v___x_1713_, lean_object* v_as_1714_, lean_object* v_i_1715_, lean_object* v_stop_1716_, lean_object* v_b_1717_){
_start:
{
uint8_t v___x_1716__boxed_1718_; size_t v_i_boxed_1719_; size_t v_stop_boxed_1720_; lean_object* v_res_1721_; 
v___x_1716__boxed_1718_ = lean_unbox(v___x_1713_);
v_i_boxed_1719_ = lean_unbox_usize(v_i_1715_);
lean_dec(v_i_1715_);
v_stop_boxed_1720_ = lean_unbox_usize(v_stop_1716_);
lean_dec(v_stop_1716_);
v_res_1721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_1716__boxed_1718_, v_as_1714_, v_i_boxed_1719_, v_stop_boxed_1720_, v_b_1717_);
lean_dec_ref(v_as_1714_);
return v_res_1721_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1727_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2));
v___x_1729_ = l_Lean_Expr_const___override(v___x_1728_, v___x_1727_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2(lean_object* v_typeExpr_1730_, lean_object* v_as_1731_, size_t v_i_1732_, size_t v_stop_1733_, lean_object* v_b_1734_){
_start:
{
uint8_t v___x_1735_; 
v___x_1735_ = lean_usize_dec_eq(v_i_1732_, v_stop_1733_);
if (v___x_1735_ == 0)
{
size_t v___x_1736_; size_t v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1736_ = ((size_t)1ULL);
v___x_1737_ = lean_usize_sub(v_i_1732_, v___x_1736_);
v___x_1738_ = lean_array_uget_borrowed(v_as_1731_, v___x_1737_);
v___x_1739_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3);
lean_inc(v___x_1738_);
lean_inc_ref(v_typeExpr_1730_);
v___x_1740_ = l_Lean_mkApp3(v___x_1739_, v_typeExpr_1730_, v___x_1738_, v_b_1734_);
v_i_1732_ = v___x_1737_;
v_b_1734_ = v___x_1740_;
goto _start;
}
else
{
lean_dec_ref(v_typeExpr_1730_);
return v_b_1734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___boxed(lean_object* v_typeExpr_1742_, lean_object* v_as_1743_, lean_object* v_i_1744_, lean_object* v_stop_1745_, lean_object* v_b_1746_){
_start:
{
size_t v_i_boxed_1747_; size_t v_stop_boxed_1748_; lean_object* v_res_1749_; 
v_i_boxed_1747_ = lean_unbox_usize(v_i_1744_);
lean_dec(v_i_1744_);
v_stop_boxed_1748_ = lean_unbox_usize(v_stop_1745_);
lean_dec(v_stop_1745_);
v_res_1749_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2(v_typeExpr_1742_, v_as_1743_, v_i_boxed_1747_, v_stop_boxed_1748_, v_b_1746_);
lean_dec_ref(v_as_1743_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0(size_t v_sz_1750_, size_t v_i_1751_, lean_object* v_bs_1752_){
_start:
{
uint8_t v___x_1753_; 
v___x_1753_ = lean_usize_dec_lt(v_i_1751_, v_sz_1750_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1754_, 0, v_bs_1752_);
return v___x_1754_;
}
else
{
lean_object* v_v_1755_; lean_object* v___x_1756_; lean_object* v_bs_x27_1757_; size_t v___x_1758_; size_t v___x_1759_; lean_object* v___x_1760_; 
v_v_1755_ = lean_array_uget(v_bs_1752_, v_i_1751_);
v___x_1756_ = lean_unsigned_to_nat(0u);
v_bs_x27_1757_ = lean_array_uset(v_bs_1752_, v_i_1751_, v___x_1756_);
v___x_1758_ = ((size_t)1ULL);
v___x_1759_ = lean_usize_add(v_i_1751_, v___x_1758_);
v___x_1760_ = lean_array_uset(v_bs_x27_1757_, v_i_1751_, v_v_1755_);
v_i_1751_ = v___x_1759_;
v_bs_1752_ = v___x_1760_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0___boxed(lean_object* v_sz_1762_, lean_object* v_i_1763_, lean_object* v_bs_1764_){
_start:
{
size_t v_sz_boxed_1765_; size_t v_i_boxed_1766_; lean_object* v_res_1767_; 
v_sz_boxed_1765_ = lean_unbox_usize(v_sz_1762_);
lean_dec(v_sz_1762_);
v_i_boxed_1766_ = lean_unbox_usize(v_i_1763_);
lean_dec(v_i_1763_);
v_res_1767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0(v_sz_boxed_1765_, v_i_boxed_1766_, v_bs_1764_);
return v_res_1767_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1771_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__0));
v___x_1772_ = l_Lean_Expr_const___override(v___x_1771_, v___x_1770_);
return v___x_1772_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1780_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1781_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5));
v___x_1782_ = l_Lean_Expr_const___override(v___x_1781_, v___x_1780_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(lean_object* v_typeExpr_1785_, lean_object* v_ev_1786_, lean_object* v_stx_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v_fileName_1795_; lean_object* v_fileMap_1796_; lean_object* v_options_1797_; lean_object* v_currRecDepth_1798_; lean_object* v_maxRecDepth_1799_; lean_object* v_ref_1800_; lean_object* v_currNamespace_1801_; lean_object* v_openDecls_1802_; lean_object* v_initHeartbeats_1803_; lean_object* v_maxHeartbeats_1804_; lean_object* v_quotContext_1805_; lean_object* v_currMacroScope_1806_; uint8_t v_diag_1807_; lean_object* v_cancelTk_x3f_1808_; uint8_t v_suppressElabErrors_1809_; lean_object* v_inheritedTraceOptions_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v_a_1816_; lean_object* v_snd_1817_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v_fileName_1795_ = lean_ctor_get(v_a_1792_, 0);
v_fileMap_1796_ = lean_ctor_get(v_a_1792_, 1);
v_options_1797_ = lean_ctor_get(v_a_1792_, 2);
v_currRecDepth_1798_ = lean_ctor_get(v_a_1792_, 3);
v_maxRecDepth_1799_ = lean_ctor_get(v_a_1792_, 4);
v_ref_1800_ = lean_ctor_get(v_a_1792_, 5);
v_currNamespace_1801_ = lean_ctor_get(v_a_1792_, 6);
v_openDecls_1802_ = lean_ctor_get(v_a_1792_, 7);
v_initHeartbeats_1803_ = lean_ctor_get(v_a_1792_, 8);
v_maxHeartbeats_1804_ = lean_ctor_get(v_a_1792_, 9);
v_quotContext_1805_ = lean_ctor_get(v_a_1792_, 10);
v_currMacroScope_1806_ = lean_ctor_get(v_a_1792_, 11);
v_diag_1807_ = lean_ctor_get_uint8(v_a_1792_, sizeof(void*)*14);
v_cancelTk_x3f_1808_ = lean_ctor_get(v_a_1792_, 12);
v_suppressElabErrors_1809_ = lean_ctor_get_uint8(v_a_1792_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1810_ = lean_ctor_get(v_a_1792_, 13);
v___x_1811_ = lean_unsigned_to_nat(0u);
v___x_1812_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1);
lean_inc_ref(v_typeExpr_1785_);
v___x_1813_ = l_Lean_Expr_app___override(v___x_1812_, v_typeExpr_1785_);
v___x_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
lean_inc(v_stx_1787_);
v___x_1849_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_1787_);
v___x_1850_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__3));
lean_inc(v___x_1849_);
v___x_1851_ = l_Lean_Syntax_isOfKind(v___x_1849_, v___x_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; 
lean_dec(v___x_1849_);
lean_dec_ref_known(v___x_1814_, 1);
lean_dec(v_stx_1787_);
lean_dec_ref(v_ev_1786_);
lean_dec_ref(v_typeExpr_1785_);
v___x_1852_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_1848_ = v___x_1852_;
goto v___jp_1847_;
}
else
{
lean_object* v_ref_1853_; lean_object* v___x_1854_; lean_object* v___y_1856_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v_ref_1853_ = l_Lean_replaceRef(v_stx_1787_, v_ref_1800_);
lean_inc_ref(v_inheritedTraceOptions_1810_);
lean_inc(v_cancelTk_x3f_1808_);
lean_inc(v_currMacroScope_1806_);
lean_inc(v_quotContext_1805_);
lean_inc(v_maxHeartbeats_1804_);
lean_inc(v_initHeartbeats_1803_);
lean_inc(v_openDecls_1802_);
lean_inc(v_currNamespace_1801_);
lean_inc(v_maxRecDepth_1799_);
lean_inc(v_currRecDepth_1798_);
lean_inc_ref(v_options_1797_);
lean_inc_ref(v_fileMap_1796_);
lean_inc_ref(v_fileName_1795_);
v___x_1854_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1854_, 0, v_fileName_1795_);
lean_ctor_set(v___x_1854_, 1, v_fileMap_1796_);
lean_ctor_set(v___x_1854_, 2, v_options_1797_);
lean_ctor_set(v___x_1854_, 3, v_currRecDepth_1798_);
lean_ctor_set(v___x_1854_, 4, v_maxRecDepth_1799_);
lean_ctor_set(v___x_1854_, 5, v_ref_1853_);
lean_ctor_set(v___x_1854_, 6, v_currNamespace_1801_);
lean_ctor_set(v___x_1854_, 7, v_openDecls_1802_);
lean_ctor_set(v___x_1854_, 8, v_initHeartbeats_1803_);
lean_ctor_set(v___x_1854_, 9, v_maxHeartbeats_1804_);
lean_ctor_set(v___x_1854_, 10, v_quotContext_1805_);
lean_ctor_set(v___x_1854_, 11, v_currMacroScope_1806_);
lean_ctor_set(v___x_1854_, 12, v_cancelTk_x3f_1808_);
lean_ctor_set(v___x_1854_, 13, v_inheritedTraceOptions_1810_);
lean_ctor_set_uint8(v___x_1854_, sizeof(void*)*14, v_diag_1807_);
lean_ctor_set_uint8(v___x_1854_, sizeof(void*)*14 + 1, v_suppressElabErrors_1809_);
v___x_1882_ = lean_unsigned_to_nat(1u);
v___x_1883_ = l_Lean_Syntax_getArg(v___x_1849_, v___x_1882_);
lean_dec(v___x_1849_);
v___x_1884_ = l_Lean_Syntax_getArgs(v___x_1883_);
lean_dec(v___x_1883_);
v___x_1885_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__7));
v___x_1886_ = lean_array_get_size(v___x_1884_);
v___x_1887_ = lean_nat_dec_lt(v___x_1811_, v___x_1886_);
if (v___x_1887_ == 0)
{
lean_dec_ref(v___x_1884_);
v___y_1856_ = v___x_1885_;
goto v___jp_1855_;
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1888_ = lean_box(v___x_1851_);
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
lean_ctor_set(v___x_1889_, 1, v___x_1885_);
v___x_1890_ = lean_nat_dec_le(v___x_1886_, v___x_1886_);
if (v___x_1890_ == 0)
{
if (v___x_1887_ == 0)
{
lean_dec_ref_known(v___x_1889_, 2);
lean_dec_ref(v___x_1884_);
v___y_1856_ = v___x_1885_;
goto v___jp_1855_;
}
else
{
size_t v___x_1891_; size_t v___x_1892_; lean_object* v___x_1893_; lean_object* v_snd_1894_; 
v___x_1891_ = ((size_t)0ULL);
v___x_1892_ = lean_usize_of_nat(v___x_1886_);
v___x_1893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_1851_, v___x_1884_, v___x_1891_, v___x_1892_, v___x_1889_);
lean_dec_ref(v___x_1884_);
v_snd_1894_ = lean_ctor_get(v___x_1893_, 1);
lean_inc(v_snd_1894_);
lean_dec_ref(v___x_1893_);
v___y_1856_ = v_snd_1894_;
goto v___jp_1855_;
}
}
else
{
size_t v___x_1895_; size_t v___x_1896_; lean_object* v___x_1897_; lean_object* v_snd_1898_; 
v___x_1895_ = ((size_t)0ULL);
v___x_1896_ = lean_usize_of_nat(v___x_1886_);
v___x_1897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_1851_, v___x_1884_, v___x_1895_, v___x_1896_, v___x_1889_);
lean_dec_ref(v___x_1884_);
v_snd_1898_ = lean_ctor_get(v___x_1897_, 1);
lean_inc(v_snd_1898_);
lean_dec_ref(v___x_1897_);
v___y_1856_ = v_snd_1898_;
goto v___jp_1855_;
}
}
v___jp_1855_:
{
size_t v_sz_1857_; size_t v___x_1858_; lean_object* v___x_1859_; 
v_sz_1857_ = lean_array_size(v___y_1856_);
v___x_1858_ = ((size_t)0ULL);
v___x_1859_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0(v_sz_1857_, v___x_1858_, v___y_1856_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v___x_1860_; 
lean_dec_ref_known(v___x_1854_, 14);
lean_dec_ref_known(v___x_1814_, 1);
lean_dec(v_stx_1787_);
lean_dec_ref(v_ev_1786_);
lean_dec_ref(v_typeExpr_1785_);
v___x_1860_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_1848_ = v___x_1860_;
goto v___jp_1847_;
}
else
{
lean_object* v_val_1861_; size_t v_sz_1862_; lean_object* v___x_1863_; 
v_val_1861_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_val_1861_);
lean_dec_ref_known(v___x_1859_, 1);
v_sz_1862_ = lean_array_size(v_val_1861_);
v___x_1863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(v_ev_1786_, v_sz_1862_, v___x_1858_, v_val_1861_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v___x_1854_, v_a_1793_);
lean_dec_ref_known(v___x_1854_, 14);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1865_; lean_object* v_fst_1866_; lean_object* v_snd_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1863_, 1);
v___x_1865_ = l_Array_unzip___redArg(v_a_1864_);
lean_dec(v_a_1864_);
v_fst_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_fst_1866_);
v_snd_1867_ = lean_ctor_get(v___x_1865_, 1);
lean_inc(v_snd_1867_);
lean_dec_ref(v___x_1865_);
v___x_1868_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6, &l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6);
lean_inc_ref(v_typeExpr_1785_);
v___x_1869_ = l_Lean_Expr_app___override(v___x_1868_, v_typeExpr_1785_);
v___x_1870_ = lean_array_get_size(v_snd_1867_);
v___x_1871_ = lean_nat_dec_lt(v___x_1811_, v___x_1870_);
if (v___x_1871_ == 0)
{
lean_dec(v_snd_1867_);
lean_dec_ref(v_typeExpr_1785_);
v___y_1843_ = v_fst_1866_;
v___y_1844_ = v___x_1869_;
goto v___jp_1842_;
}
else
{
size_t v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = lean_usize_of_nat(v___x_1870_);
v___x_1873_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2(v_typeExpr_1785_, v_snd_1867_, v___x_1872_, v___x_1858_, v___x_1869_);
lean_dec(v_snd_1867_);
v___y_1843_ = v_fst_1866_;
v___y_1844_ = v___x_1873_;
goto v___jp_1842_;
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec_ref_known(v___x_1814_, 1);
lean_dec(v_stx_1787_);
lean_dec_ref(v_typeExpr_1785_);
v_a_1874_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1863_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1863_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
}
}
v___jp_1815_:
{
lean_object* v___x_1818_; lean_object* v_infoState_1819_; uint8_t v_enabled_1820_; 
v___x_1818_ = lean_st_ref_get(v_a_1793_);
v_infoState_1819_ = lean_ctor_get(v___x_1818_, 7);
lean_inc_ref(v_infoState_1819_);
lean_dec(v___x_1818_);
v_enabled_1820_ = lean_ctor_get_uint8(v_infoState_1819_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1819_);
if (v_enabled_1820_ == 0)
{
lean_object* v___x_1821_; 
lean_dec_ref(v_snd_1817_);
lean_dec_ref_known(v___x_1814_, 1);
lean_dec(v_stx_1787_);
v___x_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1821_, 0, v_a_1816_);
return v___x_1821_;
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; lean_object* v___x_1825_; 
v___x_1822_ = lean_box(0);
v___x_1823_ = lean_box(0);
v___x_1824_ = 0;
v___x_1825_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_1787_, v_snd_1817_, v___x_1814_, v___x_1822_, v___x_1823_, v___x_1824_, v___x_1824_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1832_ == 0)
{
lean_object* v_unused_1833_; 
v_unused_1833_ = lean_ctor_get(v___x_1825_, 0);
lean_dec(v_unused_1833_);
v___x_1827_ = v___x_1825_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_dec(v___x_1825_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v_a_1816_);
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1816_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec_ref(v_a_1816_);
v_a_1834_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1825_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1825_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
}
v___jp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = lean_array_to_list(v___y_1843_);
lean_inc_ref(v___y_1844_);
v___x_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
lean_ctor_set(v___x_1846_, 1, v___y_1844_);
v_a_1816_ = v___x_1846_;
v_snd_1817_ = v___y_1844_;
goto v___jp_1815_;
}
v___jp_1847_:
{
return v___y_1848_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___boxed(lean_object* v_typeExpr_1899_, lean_object* v_ev_1900_, lean_object* v_stx_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(v_typeExpr_1899_, v_ev_1900_, v_stx_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx(lean_object* v_00_u03b1_1910_, lean_object* v_typeExpr_1911_, lean_object* v_ev_1912_, lean_object* v_stx_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(v_typeExpr_1911_, v_ev_1912_, v_stx_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___boxed(lean_object* v_00_u03b1_1922_, lean_object* v_typeExpr_1923_, lean_object* v_ev_1924_, lean_object* v_stx_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx(v_00_u03b1_1922_, v_typeExpr_1923_, v_ev_1924_, v_stx_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
lean_dec(v_a_1927_);
lean_dec_ref(v_a_1926_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1(lean_object* v_00_u03b1_1934_, lean_object* v_ev_1935_, size_t v_sz_1936_, size_t v_i_1937_, lean_object* v_bs_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(v_ev_1935_, v_sz_1936_, v_i_1937_, v_bs_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___boxed(lean_object* v_00_u03b1_1947_, lean_object* v_ev_1948_, lean_object* v_sz_1949_, lean_object* v_i_1950_, lean_object* v_bs_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
size_t v_sz_boxed_1959_; size_t v_i_boxed_1960_; lean_object* v_res_1961_; 
v_sz_boxed_1959_ = lean_unbox_usize(v_sz_1949_);
lean_dec(v_sz_1949_);
v_i_boxed_1960_ = lean_unbox_usize(v_i_1950_);
lean_dec(v_i_1950_);
v_res_1961_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1(v_00_u03b1_1947_, v_ev_1948_, v_sz_boxed_1959_, v_i_boxed_1960_, v_bs_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0(lean_object* v_typeExpr_1962_, lean_object* v_as_1963_, size_t v_i_1964_, size_t v_stop_1965_, lean_object* v_b_1966_){
_start:
{
uint8_t v___x_1967_; 
v___x_1967_ = lean_usize_dec_eq(v_i_1964_, v_stop_1965_);
if (v___x_1967_ == 0)
{
size_t v___x_1968_; size_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1968_ = ((size_t)1ULL);
v___x_1969_ = lean_usize_sub(v_i_1964_, v___x_1968_);
v___x_1970_ = lean_array_uget_borrowed(v_as_1963_, v___x_1969_);
v___x_1971_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3);
lean_inc(v___x_1970_);
lean_inc_ref(v_typeExpr_1962_);
v___x_1972_ = l_Lean_mkApp3(v___x_1971_, v_typeExpr_1962_, v___x_1970_, v_b_1966_);
v_i_1964_ = v___x_1969_;
v_b_1966_ = v___x_1972_;
goto _start;
}
else
{
lean_dec_ref(v_typeExpr_1962_);
return v_b_1966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0___boxed(lean_object* v_typeExpr_1974_, lean_object* v_as_1975_, lean_object* v_i_1976_, lean_object* v_stop_1977_, lean_object* v_b_1978_){
_start:
{
size_t v_i_boxed_1979_; size_t v_stop_boxed_1980_; lean_object* v_res_1981_; 
v_i_boxed_1979_ = lean_unbox_usize(v_i_1976_);
lean_dec(v_i_1976_);
v_stop_boxed_1980_ = lean_unbox_usize(v_stop_1977_);
lean_dec(v_stop_1977_);
v_res_1981_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0(v_typeExpr_1974_, v_as_1975_, v_i_boxed_1979_, v_stop_boxed_1980_, v_b_1978_);
lean_dec_ref(v_as_1975_);
return v_res_1981_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2(void){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1985_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1986_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__1));
v___x_1987_ = l_Lean_Expr_const___override(v___x_1986_, v___x_1985_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg(lean_object* v_typeExpr_1992_, lean_object* v_ev_1993_, lean_object* v_stx_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v_fileName_2002_; lean_object* v_fileMap_2003_; lean_object* v_options_2004_; lean_object* v_currRecDepth_2005_; lean_object* v_maxRecDepth_2006_; lean_object* v_ref_2007_; lean_object* v_currNamespace_2008_; lean_object* v_openDecls_2009_; lean_object* v_initHeartbeats_2010_; lean_object* v_maxHeartbeats_2011_; lean_object* v_quotContext_2012_; lean_object* v_currMacroScope_2013_; uint8_t v_diag_2014_; lean_object* v_cancelTk_x3f_2015_; uint8_t v_suppressElabErrors_2016_; lean_object* v_inheritedTraceOptions_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v_a_2024_; lean_object* v_snd_2025_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v_fileName_2002_ = lean_ctor_get(v_a_1999_, 0);
v_fileMap_2003_ = lean_ctor_get(v_a_1999_, 1);
v_options_2004_ = lean_ctor_get(v_a_1999_, 2);
v_currRecDepth_2005_ = lean_ctor_get(v_a_1999_, 3);
v_maxRecDepth_2006_ = lean_ctor_get(v_a_1999_, 4);
v_ref_2007_ = lean_ctor_get(v_a_1999_, 5);
v_currNamespace_2008_ = lean_ctor_get(v_a_1999_, 6);
v_openDecls_2009_ = lean_ctor_get(v_a_1999_, 7);
v_initHeartbeats_2010_ = lean_ctor_get(v_a_1999_, 8);
v_maxHeartbeats_2011_ = lean_ctor_get(v_a_1999_, 9);
v_quotContext_2012_ = lean_ctor_get(v_a_1999_, 10);
v_currMacroScope_2013_ = lean_ctor_get(v_a_1999_, 11);
v_diag_2014_ = lean_ctor_get_uint8(v_a_1999_, sizeof(void*)*14);
v_cancelTk_x3f_2015_ = lean_ctor_get(v_a_1999_, 12);
v_suppressElabErrors_2016_ = lean_ctor_get_uint8(v_a_1999_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2017_ = lean_ctor_get(v_a_1999_, 13);
v___x_2018_ = lean_unsigned_to_nat(0u);
v___x_2019_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_2020_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2);
lean_inc_ref(v_typeExpr_1992_);
v___x_2021_ = l_Lean_Expr_app___override(v___x_2020_, v_typeExpr_1992_);
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
lean_inc(v_stx_1994_);
v___x_2061_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_1994_);
v___x_2062_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__5));
lean_inc(v___x_2061_);
v___x_2063_ = l_Lean_Syntax_isOfKind(v___x_2061_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; 
lean_dec(v___x_2061_);
lean_dec_ref_known(v___x_2022_, 1);
lean_dec(v_stx_1994_);
lean_dec_ref(v_ev_1993_);
lean_dec_ref(v_typeExpr_1992_);
v___x_2064_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2060_ = v___x_2064_;
goto v___jp_2059_;
}
else
{
lean_object* v_ref_2065_; lean_object* v___x_2066_; lean_object* v___y_2068_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; 
v_ref_2065_ = l_Lean_replaceRef(v_stx_1994_, v_ref_2007_);
lean_inc_ref(v_inheritedTraceOptions_2017_);
lean_inc(v_cancelTk_x3f_2015_);
lean_inc(v_currMacroScope_2013_);
lean_inc(v_quotContext_2012_);
lean_inc(v_maxHeartbeats_2011_);
lean_inc(v_initHeartbeats_2010_);
lean_inc(v_openDecls_2009_);
lean_inc(v_currNamespace_2008_);
lean_inc(v_maxRecDepth_2006_);
lean_inc(v_currRecDepth_2005_);
lean_inc_ref(v_options_2004_);
lean_inc_ref(v_fileMap_2003_);
lean_inc_ref(v_fileName_2002_);
v___x_2066_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2066_, 0, v_fileName_2002_);
lean_ctor_set(v___x_2066_, 1, v_fileMap_2003_);
lean_ctor_set(v___x_2066_, 2, v_options_2004_);
lean_ctor_set(v___x_2066_, 3, v_currRecDepth_2005_);
lean_ctor_set(v___x_2066_, 4, v_maxRecDepth_2006_);
lean_ctor_set(v___x_2066_, 5, v_ref_2065_);
lean_ctor_set(v___x_2066_, 6, v_currNamespace_2008_);
lean_ctor_set(v___x_2066_, 7, v_openDecls_2009_);
lean_ctor_set(v___x_2066_, 8, v_initHeartbeats_2010_);
lean_ctor_set(v___x_2066_, 9, v_maxHeartbeats_2011_);
lean_ctor_set(v___x_2066_, 10, v_quotContext_2012_);
lean_ctor_set(v___x_2066_, 11, v_currMacroScope_2013_);
lean_ctor_set(v___x_2066_, 12, v_cancelTk_x3f_2015_);
lean_ctor_set(v___x_2066_, 13, v_inheritedTraceOptions_2017_);
lean_ctor_set_uint8(v___x_2066_, sizeof(void*)*14, v_diag_2014_);
lean_ctor_set_uint8(v___x_2066_, sizeof(void*)*14 + 1, v_suppressElabErrors_2016_);
v___x_2095_ = lean_unsigned_to_nat(1u);
v___x_2096_ = l_Lean_Syntax_getArg(v___x_2061_, v___x_2095_);
lean_dec(v___x_2061_);
v___x_2097_ = l_Lean_Syntax_getArgs(v___x_2096_);
lean_dec(v___x_2096_);
v___x_2098_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__7));
v___x_2099_ = lean_array_get_size(v___x_2097_);
v___x_2100_ = lean_nat_dec_lt(v___x_2018_, v___x_2099_);
if (v___x_2100_ == 0)
{
lean_dec_ref(v___x_2097_);
v___y_2068_ = v___x_2098_;
goto v___jp_2067_;
}
else
{
lean_object* v___x_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2101_ = lean_box(v___x_2063_);
v___x_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
lean_ctor_set(v___x_2102_, 1, v___x_2098_);
v___x_2103_ = lean_nat_dec_le(v___x_2099_, v___x_2099_);
if (v___x_2103_ == 0)
{
if (v___x_2100_ == 0)
{
lean_dec_ref_known(v___x_2102_, 2);
lean_dec_ref(v___x_2097_);
v___y_2068_ = v___x_2098_;
goto v___jp_2067_;
}
else
{
size_t v___x_2104_; size_t v___x_2105_; lean_object* v___x_2106_; lean_object* v_snd_2107_; 
v___x_2104_ = ((size_t)0ULL);
v___x_2105_ = lean_usize_of_nat(v___x_2099_);
v___x_2106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_2063_, v___x_2097_, v___x_2104_, v___x_2105_, v___x_2102_);
lean_dec_ref(v___x_2097_);
v_snd_2107_ = lean_ctor_get(v___x_2106_, 1);
lean_inc(v_snd_2107_);
lean_dec_ref(v___x_2106_);
v___y_2068_ = v_snd_2107_;
goto v___jp_2067_;
}
}
else
{
size_t v___x_2108_; size_t v___x_2109_; lean_object* v___x_2110_; lean_object* v_snd_2111_; 
v___x_2108_ = ((size_t)0ULL);
v___x_2109_ = lean_usize_of_nat(v___x_2099_);
v___x_2110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_2063_, v___x_2097_, v___x_2108_, v___x_2109_, v___x_2102_);
lean_dec_ref(v___x_2097_);
v_snd_2111_ = lean_ctor_get(v___x_2110_, 1);
lean_inc(v_snd_2111_);
lean_dec_ref(v___x_2110_);
v___y_2068_ = v_snd_2111_;
goto v___jp_2067_;
}
}
v___jp_2067_:
{
size_t v_sz_2069_; size_t v___x_2070_; lean_object* v___x_2071_; 
v_sz_2069_ = lean_array_size(v___y_2068_);
v___x_2070_ = ((size_t)0ULL);
v___x_2071_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0(v_sz_2069_, v___x_2070_, v___y_2068_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v___x_2072_; 
lean_dec_ref_known(v___x_2066_, 14);
lean_dec_ref_known(v___x_2022_, 1);
lean_dec(v_stx_1994_);
lean_dec_ref(v_ev_1993_);
lean_dec_ref(v_typeExpr_1992_);
v___x_2072_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2060_ = v___x_2072_;
goto v___jp_2059_;
}
else
{
lean_object* v_val_2073_; size_t v_sz_2074_; lean_object* v___x_2075_; 
v_val_2073_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_val_2073_);
lean_dec_ref_known(v___x_2071_, 1);
v_sz_2074_ = lean_array_size(v_val_2073_);
v___x_2075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(v_ev_1993_, v_sz_2074_, v___x_2070_, v_val_2073_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v___x_2066_, v_a_2000_);
lean_dec_ref_known(v___x_2066_, 14);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2077_; lean_object* v_fst_2078_; lean_object* v_snd_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2075_, 1);
v___x_2077_ = l_Array_unzip___redArg(v_a_2076_);
lean_dec(v_a_2076_);
v_fst_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_fst_2078_);
v_snd_2079_ = lean_ctor_get(v___x_2077_, 1);
lean_inc(v_snd_2079_);
lean_dec_ref(v___x_2077_);
v___x_2080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0));
v___x_2081_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6, &l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6);
lean_inc_ref(v_typeExpr_1992_);
v___x_2082_ = l_Lean_Expr_app___override(v___x_2081_, v_typeExpr_1992_);
v___x_2083_ = lean_array_get_size(v_snd_2079_);
v___x_2084_ = lean_nat_dec_lt(v___x_2018_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_dec(v_snd_2079_);
v___y_2051_ = v_fst_2078_;
v___y_2052_ = v___x_2080_;
v___y_2053_ = v___x_2082_;
goto v___jp_2050_;
}
else
{
size_t v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_usize_of_nat(v___x_2083_);
lean_inc_ref(v_typeExpr_1992_);
v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0(v_typeExpr_1992_, v_snd_2079_, v___x_2085_, v___x_2070_, v___x_2082_);
lean_dec(v_snd_2079_);
v___y_2051_ = v_fst_2078_;
v___y_2052_ = v___x_2080_;
v___y_2053_ = v___x_2086_;
goto v___jp_2050_;
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec_ref_known(v___x_2022_, 1);
lean_dec(v_stx_1994_);
lean_dec_ref(v_typeExpr_1992_);
v_a_2087_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2075_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2075_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
}
}
v___jp_2023_:
{
lean_object* v___x_2026_; lean_object* v_infoState_2027_; uint8_t v_enabled_2028_; 
v___x_2026_ = lean_st_ref_get(v_a_2000_);
v_infoState_2027_ = lean_ctor_get(v___x_2026_, 7);
lean_inc_ref(v_infoState_2027_);
lean_dec(v___x_2026_);
v_enabled_2028_ = lean_ctor_get_uint8(v_infoState_2027_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2027_);
if (v_enabled_2028_ == 0)
{
lean_object* v___x_2029_; 
lean_dec_ref(v_snd_2025_);
lean_dec_ref_known(v___x_2022_, 1);
lean_dec(v_stx_1994_);
v___x_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2029_, 0, v_a_2024_);
return v___x_2029_;
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; lean_object* v___x_2033_; 
v___x_2030_ = lean_box(0);
v___x_2031_ = lean_box(0);
v___x_2032_ = 0;
v___x_2033_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_1994_, v_snd_2025_, v___x_2022_, v___x_2030_, v___x_2031_, v___x_2032_, v___x_2032_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2040_ == 0)
{
lean_object* v_unused_2041_; 
v_unused_2041_ = lean_ctor_get(v___x_2033_, 0);
lean_dec(v_unused_2041_);
v___x_2035_ = v___x_2033_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_dec(v___x_2033_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v_a_2024_);
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2024_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec_ref(v_a_2024_);
v_a_2042_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2033_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2033_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
v___jp_2050_:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2054_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__3));
lean_inc_ref(v___y_2052_);
v___x_2055_ = l_Lean_Name_mkStr2(v___y_2052_, v___x_2054_);
v___x_2056_ = l_Lean_Expr_const___override(v___x_2055_, v___x_2019_);
v___x_2057_ = l_Lean_mkAppB(v___x_2056_, v_typeExpr_1992_, v___y_2053_);
lean_inc_ref(v___x_2057_);
v___x_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___y_2051_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
v_a_2024_ = v___x_2058_;
v_snd_2025_ = v___x_2057_;
goto v___jp_2023_;
}
v___jp_2059_:
{
return v___y_2060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___boxed(lean_object* v_typeExpr_2112_, lean_object* v_ev_2113_, lean_object* v_stx_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg(v_typeExpr_2112_, v_ev_2113_, v_stx_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx(lean_object* v_00_u03b1_2123_, lean_object* v_typeExpr_2124_, lean_object* v_ev_2125_, lean_object* v_stx_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg(v_typeExpr_2124_, v_ev_2125_, v_stx_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___boxed(lean_object* v_00_u03b1_2135_, lean_object* v_typeExpr_2136_, lean_object* v_ev_2137_, lean_object* v_stx_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx(v_00_u03b1_2135_, v_typeExpr_2136_, v_ev_2137_, v_stx_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
lean_dec(v_a_2144_);
lean_dec_ref(v_a_2143_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
return v_res_2146_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2150_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_2151_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8);
v___x_2152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
lean_ctor_set(v___x_2152_, 1, v___x_2150_);
return v___x_2152_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2153_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2);
v___x_2154_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__1));
v___x_2155_ = l_Lean_Expr_const___override(v___x_2154_, v___x_2153_);
return v___x_2155_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2175_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2);
v___x_2176_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11));
v___x_2177_ = l_Lean_Expr_const___override(v___x_2176_, v___x_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg(lean_object* v_typeExpr_2178_, lean_object* v_typeExpr_x27_2179_, lean_object* v_ev_2180_, lean_object* v_ev_x27_2181_, lean_object* v_stx_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v_fileName_2190_; lean_object* v_fileMap_2191_; lean_object* v_options_2192_; lean_object* v_currRecDepth_2193_; lean_object* v_maxRecDepth_2194_; lean_object* v_ref_2195_; lean_object* v_currNamespace_2196_; lean_object* v_openDecls_2197_; lean_object* v_initHeartbeats_2198_; lean_object* v_maxHeartbeats_2199_; lean_object* v_quotContext_2200_; lean_object* v_currMacroScope_2201_; uint8_t v_diag_2202_; lean_object* v_cancelTk_x3f_2203_; uint8_t v_suppressElabErrors_2204_; lean_object* v_inheritedTraceOptions_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v_a_2211_; lean_object* v_snd_2212_; lean_object* v___y_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; 
v_fileName_2190_ = lean_ctor_get(v_a_2187_, 0);
v_fileMap_2191_ = lean_ctor_get(v_a_2187_, 1);
v_options_2192_ = lean_ctor_get(v_a_2187_, 2);
v_currRecDepth_2193_ = lean_ctor_get(v_a_2187_, 3);
v_maxRecDepth_2194_ = lean_ctor_get(v_a_2187_, 4);
v_ref_2195_ = lean_ctor_get(v_a_2187_, 5);
v_currNamespace_2196_ = lean_ctor_get(v_a_2187_, 6);
v_openDecls_2197_ = lean_ctor_get(v_a_2187_, 7);
v_initHeartbeats_2198_ = lean_ctor_get(v_a_2187_, 8);
v_maxHeartbeats_2199_ = lean_ctor_get(v_a_2187_, 9);
v_quotContext_2200_ = lean_ctor_get(v_a_2187_, 10);
v_currMacroScope_2201_ = lean_ctor_get(v_a_2187_, 11);
v_diag_2202_ = lean_ctor_get_uint8(v_a_2187_, sizeof(void*)*14);
v_cancelTk_x3f_2203_ = lean_ctor_get(v_a_2187_, 12);
v_suppressElabErrors_2204_ = lean_ctor_get_uint8(v_a_2187_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2205_ = lean_ctor_get(v_a_2187_, 13);
v___x_2206_ = lean_unsigned_to_nat(0u);
v___x_2207_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3);
lean_inc_ref(v_typeExpr_x27_2179_);
lean_inc_ref(v_typeExpr_2178_);
v___x_2208_ = l_Lean_mkAppB(v___x_2207_, v_typeExpr_2178_, v_typeExpr_x27_2179_);
v___x_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
lean_inc(v_stx_2182_);
v___x_2239_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_2182_);
v___x_2240_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5));
lean_inc(v___x_2239_);
v___x_2241_ = l_Lean_Syntax_isOfKind(v___x_2239_, v___x_2240_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; 
lean_dec(v___x_2239_);
lean_dec_ref_known(v___x_2209_, 1);
lean_dec(v_stx_2182_);
lean_dec_ref(v_ev_x27_2181_);
lean_dec_ref(v_ev_2180_);
lean_dec_ref(v_typeExpr_x27_2179_);
lean_dec_ref(v_typeExpr_2178_);
v___x_2242_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2238_ = v___x_2242_;
goto v___jp_2237_;
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; 
v___x_2243_ = l_Lean_Syntax_getArg(v___x_2239_, v___x_2206_);
v___x_2244_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7));
lean_inc(v___x_2243_);
v___x_2245_ = l_Lean_Syntax_isOfKind(v___x_2243_, v___x_2244_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; 
lean_dec(v___x_2243_);
lean_dec(v___x_2239_);
lean_dec_ref_known(v___x_2209_, 1);
lean_dec(v_stx_2182_);
lean_dec_ref(v_ev_x27_2181_);
lean_dec_ref(v_ev_2180_);
lean_dec_ref(v_typeExpr_x27_2179_);
lean_dec_ref(v_typeExpr_2178_);
v___x_2246_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2238_ = v___x_2246_;
goto v___jp_2237_;
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; uint8_t v___x_2250_; 
v___x_2247_ = lean_unsigned_to_nat(1u);
v___x_2248_ = l_Lean_Syntax_getArg(v___x_2243_, v___x_2247_);
lean_dec(v___x_2243_);
v___x_2249_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__9));
lean_inc(v___x_2248_);
v___x_2250_ = l_Lean_Syntax_isOfKind(v___x_2248_, v___x_2249_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; 
lean_dec(v___x_2248_);
lean_dec(v___x_2239_);
lean_dec_ref_known(v___x_2209_, 1);
lean_dec(v_stx_2182_);
lean_dec_ref(v_ev_x27_2181_);
lean_dec_ref(v_ev_2180_);
lean_dec_ref(v_typeExpr_x27_2179_);
lean_dec_ref(v_typeExpr_2178_);
v___x_2251_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2238_ = v___x_2251_;
goto v___jp_2237_;
}
else
{
lean_object* v___x_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; 
v___x_2252_ = l_Lean_Syntax_getArg(v___x_2248_, v___x_2206_);
lean_dec(v___x_2248_);
v___x_2253_ = lean_box(0);
v___x_2254_ = l_Lean_Syntax_matchesIdent(v___x_2252_, v___x_2253_);
lean_dec(v___x_2252_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; 
lean_dec(v___x_2239_);
lean_dec_ref_known(v___x_2209_, 1);
lean_dec(v_stx_2182_);
lean_dec_ref(v_ev_x27_2181_);
lean_dec_ref(v_ev_2180_);
lean_dec_ref(v_typeExpr_x27_2179_);
lean_dec_ref(v_typeExpr_2178_);
v___x_2255_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2238_ = v___x_2255_;
goto v___jp_2237_;
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; uint8_t v___x_2258_; 
v___x_2256_ = l_Lean_Syntax_getArg(v___x_2239_, v___x_2247_);
lean_dec(v___x_2239_);
v___x_2257_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_2256_);
v___x_2258_ = l_Lean_Syntax_matchesNull(v___x_2256_, v___x_2257_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; 
lean_dec(v___x_2256_);
lean_dec_ref_known(v___x_2209_, 1);
lean_dec(v_stx_2182_);
lean_dec_ref(v_ev_x27_2181_);
lean_dec_ref(v_ev_2180_);
lean_dec_ref(v_typeExpr_x27_2179_);
lean_dec_ref(v_typeExpr_2178_);
v___x_2259_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2238_ = v___x_2259_;
goto v___jp_2237_;
}
else
{
lean_object* v___x_2260_; lean_object* v___x_2261_; uint8_t v___x_2262_; 
v___x_2260_ = lean_unsigned_to_nat(2u);
v___x_2261_ = l_Lean_Syntax_getArg(v___x_2256_, v___x_2260_);
lean_inc(v___x_2261_);
v___x_2262_ = l_Lean_Syntax_matchesNull(v___x_2261_, v___x_2247_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; 
lean_dec(v___x_2261_);
lean_dec(v___x_2256_);
lean_dec_ref_known(v___x_2209_, 1);
lean_dec(v_stx_2182_);
lean_dec_ref(v_ev_x27_2181_);
lean_dec_ref(v_ev_2180_);
lean_dec_ref(v_typeExpr_x27_2179_);
lean_dec_ref(v_typeExpr_2178_);
v___x_2263_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2238_ = v___x_2263_;
goto v___jp_2237_;
}
else
{
lean_object* v_ref_2264_; lean_object* v___x_2265_; lean_object* v_x_2266_; lean_object* v___x_2267_; 
v_ref_2264_ = l_Lean_replaceRef(v_stx_2182_, v_ref_2195_);
lean_inc_ref(v_inheritedTraceOptions_2205_);
lean_inc(v_cancelTk_x3f_2203_);
lean_inc(v_currMacroScope_2201_);
lean_inc(v_quotContext_2200_);
lean_inc(v_maxHeartbeats_2199_);
lean_inc(v_initHeartbeats_2198_);
lean_inc(v_openDecls_2197_);
lean_inc(v_currNamespace_2196_);
lean_inc(v_maxRecDepth_2194_);
lean_inc(v_currRecDepth_2193_);
lean_inc_ref(v_options_2192_);
lean_inc_ref(v_fileMap_2191_);
lean_inc_ref(v_fileName_2190_);
v___x_2265_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2265_, 0, v_fileName_2190_);
lean_ctor_set(v___x_2265_, 1, v_fileMap_2191_);
lean_ctor_set(v___x_2265_, 2, v_options_2192_);
lean_ctor_set(v___x_2265_, 3, v_currRecDepth_2193_);
lean_ctor_set(v___x_2265_, 4, v_maxRecDepth_2194_);
lean_ctor_set(v___x_2265_, 5, v_ref_2264_);
lean_ctor_set(v___x_2265_, 6, v_currNamespace_2196_);
lean_ctor_set(v___x_2265_, 7, v_openDecls_2197_);
lean_ctor_set(v___x_2265_, 8, v_initHeartbeats_2198_);
lean_ctor_set(v___x_2265_, 9, v_maxHeartbeats_2199_);
lean_ctor_set(v___x_2265_, 10, v_quotContext_2200_);
lean_ctor_set(v___x_2265_, 11, v_currMacroScope_2201_);
lean_ctor_set(v___x_2265_, 12, v_cancelTk_x3f_2203_);
lean_ctor_set(v___x_2265_, 13, v_inheritedTraceOptions_2205_);
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*14, v_diag_2202_);
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*14 + 1, v_suppressElabErrors_2204_);
v_x_2266_ = l_Lean_Syntax_getArg(v___x_2256_, v___x_2206_);
lean_dec(v___x_2256_);
lean_inc(v_a_2188_);
lean_inc_ref(v___x_2265_);
lean_inc(v_a_2186_);
lean_inc_ref(v_a_2185_);
lean_inc(v_a_2184_);
lean_inc_ref(v_a_2183_);
v___x_2267_ = lean_apply_8(v_ev_2180_, v_x_2266_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v___x_2265_, v_a_2188_, lean_box(0));
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v_fst_2269_; lean_object* v_snd_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2299_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2268_);
lean_dec_ref_known(v___x_2267_, 1);
v_fst_2269_ = lean_ctor_get(v_a_2268_, 0);
v_snd_2270_ = lean_ctor_get(v_a_2268_, 1);
v_isSharedCheck_2299_ = !lean_is_exclusive(v_a_2268_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2272_ = v_a_2268_;
v_isShared_2273_ = v_isSharedCheck_2299_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_snd_2270_);
lean_inc(v_fst_2269_);
lean_dec(v_a_2268_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2299_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v_x_x27_2274_; lean_object* v___x_2275_; 
v_x_x27_2274_ = l_Lean_Syntax_getArg(v___x_2261_, v___x_2206_);
lean_dec(v___x_2261_);
lean_inc(v_a_2188_);
lean_inc(v_a_2186_);
lean_inc_ref(v_a_2185_);
lean_inc(v_a_2184_);
lean_inc_ref(v_a_2183_);
v___x_2275_ = lean_apply_8(v_ev_x27_2181_, v_x_x27_2274_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v___x_2265_, v_a_2188_, lean_box(0));
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; lean_object* v_fst_2277_; lean_object* v_snd_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2290_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref_known(v___x_2275_, 1);
v_fst_2277_ = lean_ctor_get(v_a_2276_, 0);
v_snd_2278_ = lean_ctor_get(v_a_2276_, 1);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_a_2276_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2280_ = v_a_2276_;
v_isShared_2281_ = v_isSharedCheck_2290_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_snd_2278_);
lean_inc(v_fst_2277_);
lean_dec(v_a_2276_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2290_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 1, v_fst_2277_);
lean_ctor_set(v___x_2280_, 0, v_fst_2269_);
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_fst_2269_);
lean_ctor_set(v_reuseFailAlloc_2289_, 1, v_fst_2277_);
v___x_2283_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2284_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12, &l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12);
v___x_2285_ = l_Lean_mkApp4(v___x_2284_, v_typeExpr_2178_, v_typeExpr_x27_2179_, v_snd_2270_, v_snd_2278_);
lean_inc_ref(v___x_2285_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 1, v___x_2285_);
lean_ctor_set(v___x_2272_, 0, v___x_2283_);
v___x_2287_ = v___x_2272_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2283_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
v_a_2211_ = v___x_2287_;
v_snd_2212_ = v___x_2285_;
goto v___jp_2210_;
}
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_del_object(v___x_2272_);
lean_dec(v_snd_2270_);
lean_dec(v_fst_2269_);
lean_dec_ref_known(v___x_2209_, 1);
lean_dec(v_stx_2182_);
lean_dec_ref(v_typeExpr_x27_2179_);
lean_dec_ref(v_typeExpr_2178_);
v_a_2291_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2275_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2275_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_dec_ref_known(v___x_2265_, 14);
lean_dec(v___x_2261_);
lean_dec_ref_known(v___x_2209_, 1);
lean_dec(v_stx_2182_);
lean_dec_ref(v_ev_x27_2181_);
lean_dec_ref(v_typeExpr_x27_2179_);
lean_dec_ref(v_typeExpr_2178_);
v_a_2300_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2267_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2267_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
}
}
}
}
v___jp_2210_:
{
lean_object* v___x_2213_; lean_object* v_infoState_2214_; uint8_t v_enabled_2215_; 
v___x_2213_ = lean_st_ref_get(v_a_2188_);
v_infoState_2214_ = lean_ctor_get(v___x_2213_, 7);
lean_inc_ref(v_infoState_2214_);
lean_dec(v___x_2213_);
v_enabled_2215_ = lean_ctor_get_uint8(v_infoState_2214_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2214_);
if (v_enabled_2215_ == 0)
{
lean_object* v___x_2216_; 
lean_dec_ref(v_snd_2212_);
lean_dec_ref_known(v___x_2209_, 1);
lean_dec(v_stx_2182_);
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v_a_2211_);
return v___x_2216_;
}
else
{
lean_object* v___x_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; lean_object* v___x_2220_; 
v___x_2217_ = lean_box(0);
v___x_2218_ = lean_box(0);
v___x_2219_ = 0;
v___x_2220_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_2182_, v_snd_2212_, v___x_2209_, v___x_2217_, v___x_2218_, v___x_2219_, v___x_2219_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2227_ == 0)
{
lean_object* v_unused_2228_; 
v_unused_2228_ = lean_ctor_get(v___x_2220_, 0);
lean_dec(v_unused_2228_);
v___x_2222_ = v___x_2220_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_dec(v___x_2220_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v_a_2211_);
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2211_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_dec_ref(v_a_2211_);
v_a_2229_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2220_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2220_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
v___jp_2237_:
{
return v___y_2238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___boxed(lean_object* v_typeExpr_2308_, lean_object* v_typeExpr_x27_2309_, lean_object* v_ev_2310_, lean_object* v_ev_x27_2311_, lean_object* v_stx_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg(v_typeExpr_2308_, v_typeExpr_x27_2309_, v_ev_2310_, v_ev_x27_2311_, v_stx_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx(lean_object* v_00_u03b1_2321_, lean_object* v_00_u03b1_x27_2322_, lean_object* v_typeExpr_2323_, lean_object* v_typeExpr_x27_2324_, lean_object* v_ev_2325_, lean_object* v_ev_x27_2326_, lean_object* v_stx_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg(v_typeExpr_2323_, v_typeExpr_x27_2324_, v_ev_2325_, v_ev_x27_2326_, v_stx_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___boxed(lean_object* v_00_u03b1_2336_, lean_object* v_00_u03b1_x27_2337_, lean_object* v_typeExpr_2338_, lean_object* v_typeExpr_x27_2339_, lean_object* v_ev_2340_, lean_object* v_ev_x27_2341_, lean_object* v_stx_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx(v_00_u03b1_2336_, v_00_u03b1_x27_2337_, v_typeExpr_2338_, v_typeExpr_x27_2339_, v_ev_2340_, v_ev_x27_2341_, v_stx_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
lean_dec(v_a_2346_);
lean_dec_ref(v_a_2345_);
lean_dec(v_a_2344_);
lean_dec_ref(v_a_2343_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_object* v_00_u03b1_2351_, lean_object* v_c_2352_, lean_object* v_f_2353_, lean_object* v_x_2354_){
_start:
{
lean_object* v_fst_2355_; lean_object* v_snd_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2367_; 
v_fst_2355_ = lean_ctor_get(v_x_2354_, 0);
v_snd_2356_ = lean_ctor_get(v_x_2354_, 1);
v_isSharedCheck_2367_ = !lean_is_exclusive(v_x_2354_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2358_ = v_x_2354_;
v_isShared_2359_ = v_isSharedCheck_2367_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_snd_2356_);
lean_inc(v_fst_2355_);
lean_dec(v_x_2354_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2367_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2360_ = lean_apply_1(v_f_2353_, v_fst_2355_);
v___x_2361_ = lean_box(0);
v___x_2362_ = l_Lean_Expr_const___override(v_c_2352_, v___x_2361_);
v___x_2363_ = l_Lean_Expr_app___override(v___x_2362_, v_snd_2356_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 1, v___x_2363_);
lean_ctor_set(v___x_2358_, 0, v___x_2360_);
v___x_2365_ = v___x_2358_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2360_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1(uint8_t v_v_2368_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2369_, 0, v_v_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1___boxed(lean_object* v_v_2370_){
_start:
{
uint8_t v_v_boxed_2371_; lean_object* v_res_2372_; 
v_v_boxed_2371_ = lean_unbox(v_v_2370_);
v_res_2372_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1(v_v_boxed_2371_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__2(lean_object* v_v_2373_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2374_, 0, v_v_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__3(lean_object* v_v_2375_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v_v_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__4(lean_object* v_v_2377_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2378_, 0, v_v_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__5(lean_object* v_v_2379_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2380_, 0, v_v_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx(lean_object* v_stx_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v___y_2421_; lean_object* v___y_2422_; uint8_t v___y_2423_; lean_object* v___x_2434_; 
v___x_2434_ = l_Lean_Meta_saveState___redArg(v_a_2416_, v_a_2418_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2436_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref_known(v___x_2434_, 1);
lean_inc(v_stx_2412_);
v___x_2436_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx(v_stx_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2447_; 
lean_dec(v_a_2435_);
lean_dec(v_stx_2412_);
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2439_ = v___x_2436_;
v_isShared_2440_ = v_isSharedCheck_2447_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2447_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___f_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2445_; 
v___f_2441_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__1));
v___x_2442_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3));
v___x_2443_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_box(0), v___x_2442_, v___f_2441_, v_a_2437_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2443_);
v___x_2445_ = v___x_2439_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2443_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2635_; 
v_a_2448_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2450_ = v___x_2436_;
v_isShared_2451_ = v_isSharedCheck_2635_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2436_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2635_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___f_2452_; lean_object* v___f_2453_; lean_object* v___f_2454_; lean_object* v___y_2456_; lean_object* v___y_2457_; uint8_t v___y_2458_; lean_object* v___y_2500_; lean_object* v___y_2501_; uint8_t v___y_2502_; lean_object* v___f_2543_; lean_object* v___y_2545_; lean_object* v___y_2546_; uint8_t v___y_2547_; lean_object* v___x_2589_; 
v___f_2452_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__4));
v___f_2453_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__5));
v___f_2454_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__6));
v___f_2543_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__11));
lean_inc(v_a_2448_);
if (v_isShared_2451_ == 0)
{
v___x_2589_ = v___x_2450_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2448_);
v___x_2589_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2588_;
}
v___jp_2455_:
{
if (v___y_2458_ == 0)
{
lean_object* v___x_2459_; 
lean_dec_ref(v___y_2457_);
v___x_2459_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2456_, v_a_2416_, v_a_2418_);
lean_dec_ref(v___y_2456_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v___x_2460_; 
lean_dec_ref_known(v___x_2459_, 1);
v___x_2460_ = l_Lean_Meta_saveState___redArg(v_a_2416_, v_a_2418_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2462_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2461_);
lean_dec_ref_known(v___x_2460_, 1);
v___x_2462_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx(v_stx_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v_a_2461_);
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2465_ = v___x_2462_;
v_isShared_2466_ = v_isSharedCheck_2472_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2462_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2472_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2467_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8));
v___x_2468_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_box(0), v___x_2467_, v___f_2454_, v_a_2463_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 0, v___x_2468_);
v___x_2470_ = v___x_2465_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2482_; 
v_a_2473_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2475_ = v___x_2462_;
v_isShared_2476_ = v_isSharedCheck_2482_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2462_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2482_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
lean_inc(v_a_2473_);
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
uint8_t v___x_2479_; 
v___x_2479_ = l_Lean_Exception_isInterrupt(v_a_2473_);
if (v___x_2479_ == 0)
{
uint8_t v___x_2480_; 
v___x_2480_ = l_Lean_Exception_isRuntime(v_a_2473_);
v___y_2421_ = v_a_2461_;
v___y_2422_ = v___x_2478_;
v___y_2423_ = v___x_2480_;
goto v___jp_2420_;
}
else
{
lean_dec(v_a_2473_);
v___y_2421_ = v_a_2461_;
v___y_2422_ = v___x_2478_;
v___y_2423_ = v___x_2479_;
goto v___jp_2420_;
}
}
}
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v_stx_2412_);
v_a_2483_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2460_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2460_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec(v_stx_2412_);
v_a_2491_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2459_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2459_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
else
{
lean_dec_ref(v___y_2456_);
lean_dec(v_stx_2412_);
return v___y_2457_;
}
}
v___jp_2499_:
{
if (v___y_2502_ == 0)
{
lean_object* v___x_2503_; 
lean_dec_ref(v___y_2500_);
v___x_2503_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2501_, v_a_2416_, v_a_2418_);
lean_dec_ref(v___y_2501_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v___x_2504_; 
lean_dec_ref_known(v___x_2503_, 1);
v___x_2504_ = l_Lean_Meta_saveState___redArg(v_a_2416_, v_a_2418_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2506_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2504_, 1);
lean_inc(v_stx_2412_);
v___x_2506_ = l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx(v_stx_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2516_; 
lean_dec(v_a_2505_);
lean_dec(v_stx_2412_);
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2509_ = v___x_2506_;
v_isShared_2510_ = v_isSharedCheck_2516_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2506_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2516_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2514_; 
v___x_2511_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10));
v___x_2512_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_box(0), v___x_2511_, v___f_2453_, v_a_2507_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 0, v___x_2512_);
v___x_2514_ = v___x_2509_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2512_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2526_; 
v_a_2517_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2519_ = v___x_2506_;
v_isShared_2520_ = v_isSharedCheck_2526_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2506_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2526_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
lean_inc(v_a_2517_);
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
uint8_t v___x_2523_; 
v___x_2523_ = l_Lean_Exception_isInterrupt(v_a_2517_);
if (v___x_2523_ == 0)
{
uint8_t v___x_2524_; 
v___x_2524_ = l_Lean_Exception_isRuntime(v_a_2517_);
v___y_2456_ = v_a_2505_;
v___y_2457_ = v___x_2522_;
v___y_2458_ = v___x_2524_;
goto v___jp_2455_;
}
else
{
lean_dec(v_a_2517_);
v___y_2456_ = v_a_2505_;
v___y_2457_ = v___x_2522_;
v___y_2458_ = v___x_2523_;
goto v___jp_2455_;
}
}
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec(v_stx_2412_);
v_a_2527_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2504_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2504_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec(v_stx_2412_);
v_a_2535_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2503_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2503_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
else
{
lean_dec_ref(v___y_2501_);
lean_dec(v_stx_2412_);
return v___y_2500_;
}
}
v___jp_2544_:
{
if (v___y_2547_ == 0)
{
lean_object* v___x_2548_; 
lean_dec_ref(v___y_2545_);
v___x_2548_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2546_, v_a_2416_, v_a_2418_);
lean_dec_ref(v___y_2546_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v___x_2549_; 
lean_dec_ref_known(v___x_2548_, 1);
v___x_2549_ = l_Lean_Meta_saveState___redArg(v_a_2416_, v_a_2418_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2551_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref_known(v___x_2549_, 1);
lean_inc(v_stx_2412_);
v___x_2551_ = l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx(v_stx_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2561_; 
lean_dec(v_a_2550_);
lean_dec(v_stx_2412_);
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2554_ = v___x_2551_;
v_isShared_2555_ = v_isSharedCheck_2561_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2561_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2559_; 
v___x_2556_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13));
v___x_2557_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_box(0), v___x_2556_, v___f_2543_, v_a_2552_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v___x_2557_);
v___x_2559_ = v___x_2554_;
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
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2571_; 
v_a_2562_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2564_ = v___x_2551_;
v_isShared_2565_ = v_isSharedCheck_2571_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2551_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2571_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
lean_inc(v_a_2562_);
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
uint8_t v___x_2568_; 
v___x_2568_ = l_Lean_Exception_isInterrupt(v_a_2562_);
if (v___x_2568_ == 0)
{
uint8_t v___x_2569_; 
v___x_2569_ = l_Lean_Exception_isRuntime(v_a_2562_);
v___y_2500_ = v___x_2567_;
v___y_2501_ = v_a_2550_;
v___y_2502_ = v___x_2569_;
goto v___jp_2499_;
}
else
{
lean_dec(v_a_2562_);
v___y_2500_ = v___x_2567_;
v___y_2501_ = v_a_2550_;
v___y_2502_ = v___x_2568_;
goto v___jp_2499_;
}
}
}
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec(v_stx_2412_);
v_a_2572_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2549_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2549_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_dec(v_stx_2412_);
v_a_2580_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2548_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2548_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
else
{
lean_dec_ref(v___y_2546_);
lean_dec(v_stx_2412_);
return v___y_2545_;
}
}
v_reusejp_2588_:
{
uint8_t v___y_2591_; uint8_t v___x_2632_; 
v___x_2632_ = l_Lean_Exception_isInterrupt(v_a_2448_);
if (v___x_2632_ == 0)
{
uint8_t v___x_2633_; 
v___x_2633_ = l_Lean_Exception_isRuntime(v_a_2448_);
v___y_2591_ = v___x_2633_;
goto v___jp_2590_;
}
else
{
lean_dec(v_a_2448_);
v___y_2591_ = v___x_2632_;
goto v___jp_2590_;
}
v___jp_2590_:
{
if (v___y_2591_ == 0)
{
lean_object* v___x_2592_; 
lean_dec_ref(v___x_2589_);
v___x_2592_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2435_, v_a_2416_, v_a_2418_);
lean_dec(v_a_2435_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v___x_2593_; 
lean_dec_ref_known(v___x_2592_, 1);
v___x_2593_ = l_Lean_Meta_saveState___redArg(v_a_2416_, v_a_2418_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2595_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
lean_inc(v_stx_2412_);
v___x_2595_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(v_stx_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2605_; 
lean_dec(v_a_2594_);
lean_dec(v_stx_2412_);
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2598_ = v___x_2595_;
v_isShared_2599_ = v_isSharedCheck_2605_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2595_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2605_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2603_; 
v___x_2600_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15));
v___x_2601_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_box(0), v___x_2600_, v___f_2452_, v_a_2596_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2601_);
v___x_2603_ = v___x_2598_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2615_; 
v_a_2606_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2608_ = v___x_2595_;
v_isShared_2609_ = v_isSharedCheck_2615_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2595_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2615_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
lean_inc(v_a_2606_);
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
uint8_t v___x_2612_; 
v___x_2612_ = l_Lean_Exception_isInterrupt(v_a_2606_);
if (v___x_2612_ == 0)
{
uint8_t v___x_2613_; 
v___x_2613_ = l_Lean_Exception_isRuntime(v_a_2606_);
v___y_2545_ = v___x_2611_;
v___y_2546_ = v_a_2594_;
v___y_2547_ = v___x_2613_;
goto v___jp_2544_;
}
else
{
lean_dec(v_a_2606_);
v___y_2545_ = v___x_2611_;
v___y_2546_ = v_a_2594_;
v___y_2547_ = v___x_2612_;
goto v___jp_2544_;
}
}
}
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec(v_stx_2412_);
v_a_2616_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2593_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2593_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec(v_stx_2412_);
v_a_2624_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2592_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2592_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
else
{
lean_dec(v_a_2435_);
lean_dec(v_stx_2412_);
return v___x_2589_;
}
}
}
}
}
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
lean_dec(v_stx_2412_);
v_a_2636_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2434_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2434_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
v___jp_2420_:
{
if (v___y_2423_ == 0)
{
lean_object* v___x_2424_; 
lean_dec_ref(v___y_2422_);
v___x_2424_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2421_, v_a_2416_, v_a_2418_);
lean_dec_ref(v___y_2421_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v___x_2425_; 
lean_dec_ref_known(v___x_2424_, 1);
v___x_2425_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
return v___x_2425_;
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
v_a_2426_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2424_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2424_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
else
{
lean_dec_ref(v___y_2421_);
return v___y_2422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___boxed(lean_object* v_stx_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx(v_stx_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
return v_res_2652_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1(void){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2654_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2);
v___x_2655_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__0));
v___x_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
lean_ctor_set(v___x_2656_, 1, v___x_2654_);
return v___x_2656_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instBool(void){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1);
return v___x_2657_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1(void){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2659_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2);
v___x_2660_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__0));
v___x_2661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2660_);
lean_ctor_set(v___x_2661_, 1, v___x_2659_);
return v___x_2661_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instNat(void){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1);
return v___x_2662_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2664_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2);
v___x_2665_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__0));
v___x_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
lean_ctor_set(v___x_2666_, 1, v___x_2664_);
return v___x_2666_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instInt(void){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1);
return v___x_2667_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1(void){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2669_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2);
v___x_2670_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__0));
v___x_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
lean_ctor_set(v___x_2671_, 1, v___x_2669_);
return v___x_2671_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instString(void){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1);
return v___x_2672_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1(void){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2674_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2);
v___x_2675_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__0));
v___x_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2675_);
lean_ctor_set(v___x_2676_, 1, v___x_2674_);
return v___x_2676_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instName(void){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instOption___redArg(lean_object* v_inst_2678_){
_start:
{
lean_object* v_evalTerm_2679_; lean_object* v_typeExpr_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2690_; 
v_evalTerm_2679_ = lean_ctor_get(v_inst_2678_, 0);
v_typeExpr_2680_ = lean_ctor_get(v_inst_2678_, 1);
v_isSharedCheck_2690_ = !lean_is_exclusive(v_inst_2678_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2682_ = v_inst_2678_;
v_isShared_2683_ = v_isSharedCheck_2690_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_typeExpr_2680_);
lean_inc(v_evalTerm_2679_);
lean_dec(v_inst_2678_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2690_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; 
lean_inc_ref(v_typeExpr_2680_);
v___x_2684_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___boxed), 11, 3);
lean_closure_set(v___x_2684_, 0, lean_box(0));
lean_closure_set(v___x_2684_, 1, v_typeExpr_2680_);
lean_closure_set(v___x_2684_, 2, v_evalTerm_2679_);
v___x_2685_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2);
v___x_2686_ = l_Lean_Expr_app___override(v___x_2685_, v_typeExpr_2680_);
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 1, v___x_2686_);
lean_ctor_set(v___x_2682_, 0, v___x_2684_);
v___x_2688_ = v___x_2682_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2684_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instOption(lean_object* v_00_u03b1_2691_, lean_object* v_inst_2692_){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_Lean_Elab_ConfigEval_EvalTerm_instOption___redArg(v_inst_2692_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instList___redArg(lean_object* v_inst_2694_){
_start:
{
lean_object* v_evalTerm_2695_; lean_object* v_typeExpr_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2706_; 
v_evalTerm_2695_ = lean_ctor_get(v_inst_2694_, 0);
v_typeExpr_2696_ = lean_ctor_get(v_inst_2694_, 1);
v_isSharedCheck_2706_ = !lean_is_exclusive(v_inst_2694_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2698_ = v_inst_2694_;
v_isShared_2699_ = v_isSharedCheck_2706_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_typeExpr_2696_);
lean_inc(v_evalTerm_2695_);
lean_dec(v_inst_2694_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2706_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2704_; 
lean_inc_ref(v_typeExpr_2696_);
v___x_2700_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___boxed), 11, 3);
lean_closure_set(v___x_2700_, 0, lean_box(0));
lean_closure_set(v___x_2700_, 1, v_typeExpr_2696_);
lean_closure_set(v___x_2700_, 2, v_evalTerm_2695_);
v___x_2701_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1);
v___x_2702_ = l_Lean_Expr_app___override(v___x_2701_, v_typeExpr_2696_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 1, v___x_2702_);
lean_ctor_set(v___x_2698_, 0, v___x_2700_);
v___x_2704_ = v___x_2698_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instList(lean_object* v_00_u03b1_2707_, lean_object* v_inst_2708_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_Elab_ConfigEval_EvalTerm_instList___redArg(v_inst_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instArray___redArg(lean_object* v_inst_2710_){
_start:
{
lean_object* v_evalTerm_2711_; lean_object* v_typeExpr_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2722_; 
v_evalTerm_2711_ = lean_ctor_get(v_inst_2710_, 0);
v_typeExpr_2712_ = lean_ctor_get(v_inst_2710_, 1);
v_isSharedCheck_2722_ = !lean_is_exclusive(v_inst_2710_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2714_ = v_inst_2710_;
v_isShared_2715_ = v_isSharedCheck_2722_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_typeExpr_2712_);
lean_inc(v_evalTerm_2711_);
lean_dec(v_inst_2710_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2722_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2720_; 
lean_inc_ref(v_typeExpr_2712_);
v___x_2716_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___boxed), 11, 3);
lean_closure_set(v___x_2716_, 0, lean_box(0));
lean_closure_set(v___x_2716_, 1, v_typeExpr_2712_);
lean_closure_set(v___x_2716_, 2, v_evalTerm_2711_);
v___x_2717_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2);
v___x_2718_ = l_Lean_Expr_app___override(v___x_2717_, v_typeExpr_2712_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 1, v___x_2718_);
lean_ctor_set(v___x_2714_, 0, v___x_2716_);
v___x_2720_ = v___x_2714_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2716_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v___x_2718_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instArray(lean_object* v_00_u03b1_2723_, lean_object* v_inst_2724_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_Elab_ConfigEval_EvalTerm_instArray___redArg(v_inst_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instProd___redArg(lean_object* v_inst_2726_, lean_object* v_inst_2727_){
_start:
{
lean_object* v_evalTerm_2728_; lean_object* v_typeExpr_2729_; lean_object* v_evalTerm_2730_; lean_object* v_typeExpr_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2741_; 
v_evalTerm_2728_ = lean_ctor_get(v_inst_2726_, 0);
lean_inc_ref(v_evalTerm_2728_);
v_typeExpr_2729_ = lean_ctor_get(v_inst_2726_, 1);
lean_inc_ref(v_typeExpr_2729_);
lean_dec_ref(v_inst_2726_);
v_evalTerm_2730_ = lean_ctor_get(v_inst_2727_, 0);
v_typeExpr_2731_ = lean_ctor_get(v_inst_2727_, 1);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_inst_2727_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2733_ = v_inst_2727_;
v_isShared_2734_ = v_isSharedCheck_2741_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_typeExpr_2731_);
lean_inc(v_evalTerm_2730_);
lean_dec(v_inst_2727_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2741_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2739_; 
lean_inc_ref(v_typeExpr_2731_);
lean_inc_ref(v_typeExpr_2729_);
v___x_2735_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___boxed), 14, 6);
lean_closure_set(v___x_2735_, 0, lean_box(0));
lean_closure_set(v___x_2735_, 1, lean_box(0));
lean_closure_set(v___x_2735_, 2, v_typeExpr_2729_);
lean_closure_set(v___x_2735_, 3, v_typeExpr_2731_);
lean_closure_set(v___x_2735_, 4, v_evalTerm_2728_);
lean_closure_set(v___x_2735_, 5, v_evalTerm_2730_);
v___x_2736_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3);
v___x_2737_ = l_Lean_mkAppB(v___x_2736_, v_typeExpr_2729_, v_typeExpr_2731_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v___x_2737_);
lean_ctor_set(v___x_2733_, 0, v___x_2735_);
v___x_2739_ = v___x_2733_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v___x_2737_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instProd(lean_object* v_00_u03b1_2742_, lean_object* v_00_u03b1_x27_2743_, lean_object* v_inst_2744_, lean_object* v_inst_2745_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Lean_Elab_ConfigEval_EvalTerm_instProd___redArg(v_inst_2744_, v_inst_2745_);
return v___x_2746_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2(void){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2751_ = lean_box(0);
v___x_2752_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1));
v___x_2753_ = l_Lean_Expr_const___override(v___x_2752_, v___x_2751_);
return v___x_2753_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3(void){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2754_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2);
v___x_2755_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__0));
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
lean_ctor_set(v___x_2756_, 1, v___x_2754_);
return v___x_2756_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue(void){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3);
return v___x_2757_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2758_ = lean_box(0);
v___x_2759_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_2760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
lean_ctor_set(v___x_2760_, 1, v___x_2758_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg(){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0);
v___x_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___boxed(lean_object* v___y_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0(lean_object* v_00_u03b1_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___boxed(lean_object* v_00_u03b1_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0(v_00_u03b1_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore(lean_object* v_e_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; 
v___x_2786_ = l_Lean_Expr_cleanupAnnotations(v_e_2780_);
v___x_2787_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8));
v___x_2788_ = l_Lean_Expr_isConstOf(v___x_2786_, v___x_2787_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; uint8_t v___x_2790_; 
v___x_2789_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5));
v___x_2790_ = l_Lean_Expr_isConstOf(v___x_2786_, v___x_2789_);
lean_dec_ref(v___x_2786_);
if (v___x_2790_ == 0)
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_2791_;
}
else
{
lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2792_ = lean_box(v___x_2790_);
v___x_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
return v___x_2793_;
}
}
else
{
uint8_t v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
lean_dec_ref(v___x_2786_);
v___x_2794_ = 0;
v___x_2795_ = lean_box(v___x_2794_);
v___x_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
return v___x_2796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore___boxed(lean_object* v_e_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore(v_e_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_);
lean_dec(v_a_2801_);
lean_dec_ref(v_a_2800_);
lean_dec(v_a_2799_);
lean_dec_ref(v_a_2798_);
return v_res_2803_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__1));
v___x_2807_ = l_Lean_stringToMessageData(v___x_2806_);
return v___x_2807_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3(void){
_start:
{
uint8_t v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2808_ = 0;
v___x_2809_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__1));
v___x_2810_ = l_Lean_MessageData_ofConstName(v___x_2809_, v___x_2808_);
return v___x_2810_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4(void){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2811_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3);
v___x_2812_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_2813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
lean_ctor_set(v___x_2813_, 1, v___x_2811_);
return v___x_2813_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6(void){
_start:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__5));
v___x_2816_ = l_Lean_stringToMessageData(v___x_2815_);
return v___x_2816_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7(void){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2817_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_2818_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4);
v___x_2819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
lean_ctor_set(v___x_2819_, 1, v___x_2817_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(lean_object* v_e_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2826_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__0));
v___x_2827_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7);
v___x_2828_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_2826_, v_e_2820_, v___x_2827_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___boxed(lean_object* v_e_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v_e_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(lean_object* v_e_2836_){
_start:
{
lean_object* v___y_2839_; lean_object* v___x_2849_; 
lean_inc_ref(v_e_2836_);
v___x_2849_ = l_Lean_Expr_nat_x3f(v_e_2836_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Lean_Expr_rawNatLit_x3f(v_e_2836_);
v___y_2839_ = v___x_2850_;
goto v___jp_2838_;
}
else
{
lean_dec_ref(v_e_2836_);
v___y_2839_ = v___x_2849_;
goto v___jp_2838_;
}
v___jp_2838_:
{
if (lean_obj_tag(v___y_2839_) == 0)
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_2840_;
}
else
{
lean_object* v_val_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
v_val_2841_ = lean_ctor_get(v___y_2839_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___y_2839_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___y_2839_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_val_2841_);
lean_dec(v___y_2839_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
lean_ctor_set_tag(v___x_2843_, 0);
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_val_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg___boxed(lean_object* v_e_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(v_e_2851_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore(lean_object* v_e_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(v_e_2854_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___boxed(lean_object* v_e_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore(v_e_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_);
lean_dec(v_a_2865_);
lean_dec_ref(v_a_2864_);
lean_dec(v_a_2863_);
lean_dec_ref(v_a_2862_);
return v_res_2867_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1(void){
_start:
{
uint8_t v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2869_ = 0;
v___x_2870_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__1));
v___x_2871_ = l_Lean_MessageData_ofConstName(v___x_2870_, v___x_2869_);
return v___x_2871_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2(void){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2872_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1);
v___x_2873_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_2874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2873_);
lean_ctor_set(v___x_2874_, 1, v___x_2872_);
return v___x_2874_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3(void){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2875_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_2876_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2);
v___x_2877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
lean_ctor_set(v___x_2877_, 1, v___x_2875_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(lean_object* v_e_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2884_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__0));
v___x_2885_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3, &l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3);
v___x_2886_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_2884_, v_e_2878_, v___x_2885_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___boxed(lean_object* v_e_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v_e_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
lean_dec(v_a_2891_);
lean_dec_ref(v_a_2890_);
lean_dec(v_a_2889_);
lean_dec_ref(v_a_2888_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(lean_object* v_msg_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v_ref_2900_; lean_object* v___x_2901_; lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2910_; 
v_ref_2900_ = lean_ctor_get(v___y_2897_, 5);
v___x_2901_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6(v_msg_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2904_ = v___x_2901_;
v_isShared_2905_ = v_isSharedCheck_2910_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2901_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2910_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2906_; lean_object* v___x_2908_; 
lean_inc(v_ref_2900_);
v___x_2906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2906_, 0, v_ref_2900_);
lean_ctor_set(v___x_2906_, 1, v_a_2902_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set_tag(v___x_2904_, 1);
lean_ctor_set(v___x_2904_, 0, v___x_2906_);
v___x_2908_ = v___x_2904_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg___boxed(lean_object* v_msg_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(v_msg_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
return v_res_2917_;
}
}
static lean_object* _init_l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = ((lean_object*)(l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__0));
v___x_2920_ = l_Lean_stringToMessageData(v___x_2919_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg(lean_object* v_x_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
if (lean_obj_tag(v_x_2921_) == 0)
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = lean_obj_once(&l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1, &l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1_once, _init_l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1);
v___x_2928_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(v___x_2927_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
return v___x_2928_;
}
else
{
lean_object* v_val_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
v_val_2929_ = lean_ctor_get(v_x_2921_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v_x_2921_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v_x_2921_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_val_2929_);
lean_dec(v_x_2921_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
lean_ctor_set_tag(v___x_2931_, 0);
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_val_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___boxed(lean_object* v_x_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg(v_x_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore(lean_object* v_e_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_){
_start:
{
lean_object* v___y_2958_; lean_object* v___y_2959_; uint8_t v___y_2960_; lean_object* v___x_3016_; 
v___x_3016_ = l_Lean_Meta_saveState___redArg(v_a_2953_, v_a_2955_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
lean_inc_ref(v_e_2951_);
v___x_3018_ = l_Lean_Expr_int_x3f(v_e_2951_);
v___x_3019_ = l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg(v___x_3018_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_dec(v_a_3017_);
lean_dec_ref(v_e_2951_);
return v___x_3019_;
}
else
{
lean_object* v_a_3020_; uint8_t v___y_3022_; uint8_t v___x_3062_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
v___x_3062_ = l_Lean_Exception_isInterrupt(v_a_3020_);
if (v___x_3062_ == 0)
{
uint8_t v___x_3063_; 
v___x_3063_ = l_Lean_Exception_isRuntime(v_a_3020_);
v___y_3022_ = v___x_3063_;
goto v___jp_3021_;
}
else
{
lean_dec(v_a_3020_);
v___y_3022_ = v___x_3062_;
goto v___jp_3021_;
}
v___jp_3021_:
{
if (v___y_3022_ == 0)
{
lean_object* v___x_3023_; 
lean_dec_ref_known(v___x_3019_, 1);
v___x_3023_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3017_, v_a_2953_, v_a_2955_);
lean_dec(v_a_3017_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v___x_3024_; 
lean_dec_ref_known(v___x_3023_, 1);
v___x_3024_ = l_Lean_Meta_saveState___redArg(v_a_2953_, v_a_2955_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3026_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
lean_inc_ref(v_e_2951_);
v___x_3026_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(v_e_2951_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3035_; 
lean_dec(v_a_3025_);
lean_dec_ref(v_e_2951_);
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3029_ = v___x_3026_;
v_isShared_3030_ = v_isSharedCheck_3035_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3026_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3035_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3031_; lean_object* v___x_3033_; 
v___x_3031_ = lean_nat_to_int(v_a_3027_);
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 0, v___x_3031_);
v___x_3033_ = v___x_3029_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3031_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3045_; 
v_a_3036_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3038_ = v___x_3026_;
v_isShared_3039_ = v_isSharedCheck_3045_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3026_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3045_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
lean_inc(v_a_3036_);
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
uint8_t v___x_3042_; 
v___x_3042_ = l_Lean_Exception_isInterrupt(v_a_3036_);
if (v___x_3042_ == 0)
{
uint8_t v___x_3043_; 
v___x_3043_ = l_Lean_Exception_isRuntime(v_a_3036_);
v___y_2958_ = v___x_3041_;
v___y_2959_ = v_a_3025_;
v___y_2960_ = v___x_3043_;
goto v___jp_2957_;
}
else
{
lean_dec(v_a_3036_);
v___y_2958_ = v___x_3041_;
v___y_2959_ = v_a_3025_;
v___y_2960_ = v___x_3042_;
goto v___jp_2957_;
}
}
}
}
}
else
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
lean_dec_ref(v_e_2951_);
v_a_3046_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_3024_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3024_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_dec_ref(v_e_2951_);
v_a_3054_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_3023_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3023_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
else
{
lean_dec(v_a_3017_);
lean_dec_ref(v_e_2951_);
return v___x_3019_;
}
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec_ref(v_e_2951_);
v_a_3064_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3016_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3016_);
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
v___jp_2957_:
{
if (v___y_2960_ == 0)
{
lean_object* v___x_2961_; 
lean_dec_ref(v___y_2958_);
v___x_2961_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2959_, v_a_2953_, v_a_2955_);
lean_dec_ref(v___y_2959_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v___x_2962_; uint8_t v___x_2963_; 
lean_dec_ref_known(v___x_2961_, 1);
v___x_2962_ = l_Lean_Expr_cleanupAnnotations(v_e_2951_);
v___x_2963_ = l_Lean_Expr_isApp(v___x_2962_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2964_; 
lean_dec_ref(v___x_2962_);
v___x_2964_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_2964_;
}
else
{
lean_object* v_arg_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; uint8_t v___x_2968_; 
v_arg_2965_ = lean_ctor_get(v___x_2962_, 1);
lean_inc_ref(v_arg_2965_);
v___x_2966_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2962_);
v___x_2967_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1));
v___x_2968_ = l_Lean_Expr_isConstOf(v___x_2966_, v___x_2967_);
if (v___x_2968_ == 0)
{
lean_object* v___x_2969_; uint8_t v___x_2970_; 
v___x_2969_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2));
v___x_2970_ = l_Lean_Expr_isConstOf(v___x_2966_, v___x_2969_);
lean_dec_ref(v___x_2966_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; 
lean_dec_ref(v_arg_2965_);
v___x_2971_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_2971_;
}
else
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v_arg_2965_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2981_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2975_ = v___x_2972_;
v_isShared_2976_ = v_isSharedCheck_2981_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2972_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2981_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2977_; lean_object* v___x_2979_; 
v___x_2977_ = lean_nat_to_int(v_a_2973_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 0, v___x_2977_);
v___x_2979_ = v___x_2975_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
v_a_2982_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2972_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2972_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
}
else
{
lean_object* v___x_2990_; 
lean_dec_ref(v___x_2966_);
v___x_2990_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v_arg_2965_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2999_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2993_ = v___x_2990_;
v_isShared_2994_ = v_isSharedCheck_2999_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2999_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2995_; lean_object* v___x_2997_; 
v___x_2995_ = lean_int_neg_succ_of_nat(v_a_2991_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v___x_2995_);
v___x_2997_ = v___x_2993_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
v_a_3000_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2990_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2990_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
}
}
else
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
lean_dec_ref(v_e_2951_);
v_a_3008_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v___x_2961_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_2961_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
else
{
lean_dec_ref(v___y_2959_);
lean_dec_ref(v_e_2951_);
return v___y_2958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___boxed(lean_object* v_e_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore(v_e_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
lean_dec(v_a_3074_);
lean_dec_ref(v_a_3073_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0(lean_object* v_00_u03b1_3079_, lean_object* v_x_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v___x_3086_; 
v___x_3086_ = l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg(v_x_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___boxed(lean_object* v_00_u03b1_3087_, lean_object* v_x_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0(v_00_u03b1_3087_, v_x_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0(lean_object* v_00_u03b1_3095_, lean_object* v_msg_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v___x_3102_; 
v___x_3102_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(v_msg_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3103_, lean_object* v_msg_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0(v_00_u03b1_3103_, v_msg_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
return v_res_3110_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1(void){
_start:
{
uint8_t v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = 0;
v___x_3113_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__1));
v___x_3114_ = l_Lean_MessageData_ofConstName(v___x_3113_, v___x_3112_);
return v___x_3114_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2(void){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1);
v___x_3116_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
lean_ctor_set(v___x_3117_, 1, v___x_3115_);
return v___x_3117_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3(void){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3119_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2);
v___x_3120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
lean_ctor_set(v___x_3120_, 1, v___x_3118_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr(lean_object* v_e_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3127_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__0));
v___x_3128_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3, &l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3);
v___x_3129_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_3127_, v_e_3121_, v___x_3128_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___boxed(lean_object* v_e_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr(v_e_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
lean_dec(v_a_3134_);
lean_dec_ref(v_a_3133_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3131_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg(lean_object* v_x_3137_){
_start:
{
if (lean_obj_tag(v_x_3137_) == 9)
{
lean_object* v_a_3139_; 
v_a_3139_ = lean_ctor_get(v_x_3137_, 0);
lean_inc_ref(v_a_3139_);
lean_dec_ref_known(v_x_3137_, 1);
if (lean_obj_tag(v_a_3139_) == 1)
{
lean_object* v_val_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
v_val_3140_ = lean_ctor_get(v_a_3139_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v_a_3139_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v_a_3139_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_val_3140_);
lean_dec(v_a_3139_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
lean_ctor_set_tag(v___x_3142_, 0);
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_val_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
else
{
lean_object* v___x_3148_; 
lean_dec_ref(v_a_3139_);
v___x_3148_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3148_;
}
}
else
{
lean_object* v___x_3149_; 
lean_dec_ref(v_x_3137_);
v___x_3149_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg___boxed(lean_object* v_x_3150_, lean_object* v_a_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg(v_x_3150_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore(lean_object* v_x_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg(v_x_3153_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___boxed(lean_object* v_x_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_){
_start:
{
lean_object* v_res_3166_; 
v_res_3166_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore(v_x_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_);
lean_dec(v_a_3164_);
lean_dec_ref(v_a_3163_);
lean_dec(v_a_3162_);
lean_dec_ref(v_a_3161_);
return v_res_3166_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1(void){
_start:
{
uint8_t v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3168_ = 0;
v___x_3169_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__1));
v___x_3170_ = l_Lean_MessageData_ofConstName(v___x_3169_, v___x_3168_);
return v___x_3170_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3171_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1);
v___x_3172_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
lean_ctor_set(v___x_3173_, 1, v___x_3171_);
return v___x_3173_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3(void){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3174_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3175_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2);
v___x_3176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
lean_ctor_set(v___x_3176_, 1, v___x_3174_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr(lean_object* v_e_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_){
_start:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3183_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__0));
v___x_3184_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3, &l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3);
v___x_3185_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_3183_, v_e_3177_, v___x_3184_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___boxed(lean_object* v_e_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr(v_e_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg(lean_object* v_e_3193_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Lean_Expr_name_x3f(v_e_3193_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v___x_3196_; 
v___x_3196_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3196_;
}
else
{
lean_object* v_val_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
v_val_3197_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3195_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_val_3197_);
lean_dec(v___x_3195_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
lean_ctor_set_tag(v___x_3199_, 0);
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_val_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg___boxed(lean_object* v_e_3205_, lean_object* v_a_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg(v_e_3205_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore(lean_object* v_e_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_){
_start:
{
lean_object* v___x_3214_; 
v___x_3214_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg(v_e_3208_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___boxed(lean_object* v_e_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore(v_e_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
lean_dec(v_a_3217_);
lean_dec_ref(v_a_3216_);
return v_res_3221_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1(void){
_start:
{
uint8_t v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3223_ = 0;
v___x_3224_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1));
v___x_3225_ = l_Lean_MessageData_ofConstName(v___x_3224_, v___x_3223_);
return v___x_3225_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1);
v___x_3227_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
lean_ctor_set(v___x_3228_, 1, v___x_3226_);
return v___x_3228_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3230_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2);
v___x_3231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
lean_ctor_set(v___x_3231_, 1, v___x_3229_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr(lean_object* v_e_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3238_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__0));
v___x_3239_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3, &l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3);
v___x_3240_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_3238_, v_e_3232_, v___x_3239_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___boxed(lean_object* v_e_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr(v_e_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_);
lean_dec(v_a_3245_);
lean_dec_ref(v_a_3244_);
lean_dec(v_a_3243_);
lean_dec_ref(v_a_3242_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg(lean_object* v_ev_3251_, lean_object* v_e_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_){
_start:
{
lean_object* v___x_3258_; uint8_t v___x_3259_; 
v___x_3258_ = l_Lean_Expr_cleanupAnnotations(v_e_3252_);
v___x_3259_ = l_Lean_Expr_isApp(v___x_3258_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; 
lean_dec_ref(v___x_3258_);
lean_dec_ref(v_ev_3251_);
v___x_3260_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3260_;
}
else
{
lean_object* v_arg_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; uint8_t v___x_3264_; 
v_arg_3261_ = lean_ctor_get(v___x_3258_, 1);
lean_inc_ref(v_arg_3261_);
v___x_3262_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3258_);
v___x_3263_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8));
v___x_3264_ = l_Lean_Expr_isConstOf(v___x_3262_, v___x_3263_);
if (v___x_3264_ == 0)
{
uint8_t v___x_3265_; 
v___x_3265_ = l_Lean_Expr_isApp(v___x_3262_);
if (v___x_3265_ == 0)
{
lean_object* v___x_3266_; 
lean_dec_ref(v___x_3262_);
lean_dec_ref(v_arg_3261_);
lean_dec_ref(v_ev_3251_);
v___x_3266_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3266_;
}
else
{
lean_object* v___x_3267_; lean_object* v___x_3268_; uint8_t v___x_3269_; 
v___x_3267_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3262_);
v___x_3268_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0));
v___x_3269_ = l_Lean_Expr_isConstOf(v___x_3267_, v___x_3268_);
lean_dec_ref(v___x_3267_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; 
lean_dec_ref(v_arg_3261_);
lean_dec_ref(v_ev_3251_);
v___x_3270_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3270_;
}
else
{
lean_object* v___x_3271_; 
lean_inc(v_a_3256_);
lean_inc_ref(v_a_3255_);
lean_inc(v_a_3254_);
lean_inc_ref(v_a_3253_);
v___x_3271_ = lean_apply_6(v_ev_3251_, v_arg_3261_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_, lean_box(0));
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3280_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3274_ = v___x_3271_;
v_isShared_3275_ = v_isSharedCheck_3280_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3271_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3280_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; lean_object* v___x_3278_; 
v___x_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3276_, 0, v_a_3272_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3276_);
v___x_3278_ = v___x_3274_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3276_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
v_a_3281_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3271_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3271_);
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
}
}
else
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
lean_dec_ref(v___x_3262_);
lean_dec_ref(v_arg_3261_);
lean_dec_ref(v_ev_3251_);
v___x_3289_ = lean_box(0);
v___x_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
return v___x_3290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___boxed(lean_object* v_ev_3291_, lean_object* v_e_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg(v_ev_3291_, v_e_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
lean_dec(v_a_3296_);
lean_dec_ref(v_a_3295_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore(lean_object* v_00_u03b1_3299_, lean_object* v_ev_3300_, lean_object* v_e_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg(v_ev_3300_, v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___boxed(lean_object* v_00_u03b1_3308_, lean_object* v_ev_3309_, lean_object* v_e_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore(v_00_u03b1_3308_, v_ev_3309_, v_e_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
lean_dec(v_a_3314_);
lean_dec_ref(v_a_3313_);
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3311_);
return v_res_3316_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0(void){
_start:
{
uint8_t v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3317_ = 0;
v___x_3318_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__1));
v___x_3319_ = l_Lean_MessageData_ofConstName(v___x_3318_, v___x_3317_);
return v___x_3319_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1(void){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3320_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0, &l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0);
v___x_3321_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
lean_ctor_set(v___x_3322_, 1, v___x_3320_);
return v___x_3322_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3324_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1);
v___x_3325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
lean_ctor_set(v___x_3325_, 1, v___x_3323_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg(lean_object* v_ev_3326_, lean_object* v_e_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_){
_start:
{
lean_object* v___x_3333_; 
v___x_3333_ = l_Lean_Meta_saveState___redArg(v_a_3329_, v_a_3331_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_a_3334_);
lean_dec_ref_known(v___x_3333_, 1);
lean_inc_ref(v_ev_3326_);
v___x_3335_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___boxed), 8, 2);
lean_closure_set(v___x_3335_, 0, lean_box(0));
lean_closure_set(v___x_3335_, 1, v_ev_3326_);
v___x_3336_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2);
lean_inc_ref(v_e_3327_);
v___x_3337_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_3335_, v_e_3327_, v___x_3336_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3327_);
lean_dec_ref(v_ev_3326_);
return v___x_3337_;
}
else
{
lean_object* v_a_3338_; uint8_t v___y_3340_; uint8_t v___x_3375_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
v___x_3375_ = l_Lean_Exception_isInterrupt(v_a_3338_);
if (v___x_3375_ == 0)
{
uint8_t v___x_3376_; 
v___x_3376_ = l_Lean_Exception_isRuntime(v_a_3338_);
v___y_3340_ = v___x_3376_;
goto v___jp_3339_;
}
else
{
lean_dec(v_a_3338_);
v___y_3340_ = v___x_3375_;
goto v___jp_3339_;
}
v___jp_3339_:
{
if (v___y_3340_ == 0)
{
lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3373_; 
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3373_ == 0)
{
lean_object* v_unused_3374_; 
v_unused_3374_ = lean_ctor_get(v___x_3337_, 0);
lean_dec(v_unused_3374_);
v___x_3342_ = v___x_3337_;
v_isShared_3343_ = v_isSharedCheck_3373_;
goto v_resetjp_3341_;
}
else
{
lean_dec(v___x_3337_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3373_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3344_; 
v___x_3344_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3334_, v_a_3329_, v_a_3331_);
lean_dec(v_a_3334_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v___x_3345_; 
lean_dec_ref_known(v___x_3344_, 1);
lean_inc(v_a_3331_);
lean_inc_ref(v_a_3330_);
lean_inc(v_a_3329_);
lean_inc_ref(v_a_3328_);
v___x_3345_ = lean_apply_6(v_ev_3326_, v_e_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, lean_box(0));
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3356_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3348_ = v___x_3345_;
v_isShared_3349_ = v_isSharedCheck_3356_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3345_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3356_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 0, v_a_3346_);
v___x_3351_ = v___x_3342_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
lean_object* v___x_3353_; 
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v___x_3351_);
v___x_3353_ = v___x_3348_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3351_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
lean_del_object(v___x_3342_);
v_a_3357_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3345_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3345_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_del_object(v___x_3342_);
lean_dec_ref(v_e_3327_);
lean_dec_ref(v_ev_3326_);
v_a_3365_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3344_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3344_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
}
else
{
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3327_);
lean_dec_ref(v_ev_3326_);
return v___x_3337_;
}
}
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec_ref(v_e_3327_);
lean_dec_ref(v_ev_3326_);
v_a_3377_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3333_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3333_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___boxed(lean_object* v_ev_3385_, lean_object* v_e_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg(v_ev_3385_, v_e_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
lean_dec(v_a_3388_);
lean_dec_ref(v_a_3387_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr(lean_object* v_00_u03b1_3393_, lean_object* v_ev_3394_, lean_object* v_e_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_){
_start:
{
lean_object* v___x_3401_; 
v___x_3401_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg(v_ev_3394_, v_e_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___boxed(lean_object* v_00_u03b1_3402_, lean_object* v_ev_3403_, lean_object* v_e_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr(v_00_u03b1_3402_, v_ev_3403_, v_e_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
lean_dec(v_a_3408_);
lean_dec_ref(v_a_3407_);
lean_dec(v_a_3406_);
lean_dec_ref(v_a_3405_);
return v_res_3410_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1(void){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__0));
v___x_3413_ = l_Lean_stringToMessageData(v___x_3412_);
return v___x_3413_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2(void){
_start:
{
uint8_t v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3414_ = 0;
v___x_3415_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__0));
v___x_3416_ = l_Lean_MessageData_ofConstName(v___x_3415_, v___x_3414_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(lean_object* v_ev_3417_, lean_object* v_e_3418_, uint8_t v_didWHNF_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_){
_start:
{
lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___x_3452_; uint8_t v___x_3453_; 
lean_inc_ref(v_e_3418_);
v___x_3452_ = l_Lean_Expr_cleanupAnnotations(v_e_3418_);
v___x_3453_ = l_Lean_Expr_isApp(v___x_3452_);
if (v___x_3453_ == 0)
{
lean_dec_ref(v___x_3452_);
v___y_3426_ = v_a_3420_;
v___y_3427_ = v_a_3421_;
v___y_3428_ = v_a_3422_;
v___y_3429_ = v_a_3423_;
goto v___jp_3425_;
}
else
{
lean_object* v_arg_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; uint8_t v___x_3457_; 
v_arg_3454_ = lean_ctor_get(v___x_3452_, 1);
lean_inc_ref(v_arg_3454_);
v___x_3455_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3452_);
v___x_3456_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5));
v___x_3457_ = l_Lean_Expr_isConstOf(v___x_3455_, v___x_3456_);
if (v___x_3457_ == 0)
{
uint8_t v___x_3458_; 
v___x_3458_ = l_Lean_Expr_isApp(v___x_3455_);
if (v___x_3458_ == 0)
{
lean_dec_ref(v___x_3455_);
lean_dec_ref(v_arg_3454_);
v___y_3426_ = v_a_3420_;
v___y_3427_ = v_a_3421_;
v___y_3428_ = v_a_3422_;
v___y_3429_ = v_a_3423_;
goto v___jp_3425_;
}
else
{
lean_object* v_arg_3459_; lean_object* v___x_3460_; uint8_t v___x_3461_; 
v_arg_3459_ = lean_ctor_get(v___x_3455_, 1);
lean_inc_ref(v_arg_3459_);
v___x_3460_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3455_);
v___x_3461_ = l_Lean_Expr_isApp(v___x_3460_);
if (v___x_3461_ == 0)
{
lean_dec_ref(v___x_3460_);
lean_dec_ref(v_arg_3459_);
lean_dec_ref(v_arg_3454_);
v___y_3426_ = v_a_3420_;
v___y_3427_ = v_a_3421_;
v___y_3428_ = v_a_3422_;
v___y_3429_ = v_a_3423_;
goto v___jp_3425_;
}
else
{
lean_object* v___x_3462_; lean_object* v___x_3463_; uint8_t v___x_3464_; 
v___x_3462_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3460_);
v___x_3463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2));
v___x_3464_ = l_Lean_Expr_isConstOf(v___x_3462_, v___x_3463_);
lean_dec_ref(v___x_3462_);
if (v___x_3464_ == 0)
{
lean_dec_ref(v_arg_3459_);
lean_dec_ref(v_arg_3454_);
v___y_3426_ = v_a_3420_;
v___y_3427_ = v_a_3421_;
v___y_3428_ = v_a_3422_;
v___y_3429_ = v_a_3423_;
goto v___jp_3425_;
}
else
{
lean_object* v___x_3465_; 
lean_dec_ref(v_e_3418_);
lean_inc_ref(v_ev_3417_);
lean_inc(v_a_3423_);
lean_inc_ref(v_a_3422_);
lean_inc(v_a_3421_);
lean_inc_ref(v_a_3420_);
v___x_3465_ = lean_apply_6(v_ev_3417_, v_arg_3459_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, lean_box(0));
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3467_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref_known(v___x_3465_, 1);
v___x_3467_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(v_ev_3417_, v_arg_3454_, v___x_3457_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3476_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3470_ = v___x_3467_;
v_isShared_3471_ = v_isSharedCheck_3476_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3467_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3476_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3472_; lean_object* v___x_3474_; 
v___x_3472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3472_, 0, v_a_3466_);
lean_ctor_set(v___x_3472_, 1, v_a_3468_);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v___x_3472_);
v___x_3474_ = v___x_3470_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3472_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
else
{
lean_dec(v_a_3466_);
return v___x_3467_;
}
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
lean_dec_ref(v_arg_3454_);
lean_dec_ref(v_ev_3417_);
v_a_3477_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3465_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3465_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
lean_dec_ref(v___x_3455_);
lean_dec_ref(v_arg_3454_);
lean_dec_ref(v_e_3418_);
lean_dec_ref(v_ev_3417_);
v___x_3485_ = lean_box(0);
v___x_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
return v___x_3486_;
}
}
v___jp_3425_:
{
if (v_didWHNF_3419_ == 0)
{
lean_object* v___x_3430_; 
lean_inc(v___y_3429_);
lean_inc_ref(v___y_3428_);
lean_inc(v___y_3427_);
lean_inc_ref(v___y_3426_);
v___x_3430_ = lean_whnf(v_e_3418_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; uint8_t v___x_3432_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref_known(v___x_3430_, 1);
v___x_3432_ = 1;
v_e_3418_ = v_a_3431_;
v_didWHNF_3419_ = v___x_3432_;
v_a_3420_ = v___y_3426_;
v_a_3421_ = v___y_3427_;
v_a_3422_ = v___y_3428_;
v_a_3423_ = v___y_3429_;
goto _start;
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec_ref(v_ev_3417_);
v_a_3434_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3430_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3430_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
else
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
lean_dec_ref(v_ev_3417_);
v___x_3442_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1);
v___x_3443_ = l_Lean_indentExpr(v_e_3418_);
v___x_3444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3442_);
lean_ctor_set(v___x_3444_, 1, v___x_3443_);
v___x_3445_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3444_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
v___x_3447_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2);
v___x_3448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3446_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
v___x_3449_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3448_);
lean_ctor_set(v___x_3450_, 1, v___x_3449_);
v___x_3451_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(v___x_3450_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
return v___x_3451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___boxed(lean_object* v_ev_3487_, lean_object* v_e_3488_, lean_object* v_didWHNF_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_){
_start:
{
uint8_t v_didWHNF_boxed_3495_; lean_object* v_res_3496_; 
v_didWHNF_boxed_3495_ = lean_unbox(v_didWHNF_3489_);
v_res_3496_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(v_ev_3487_, v_e_3488_, v_didWHNF_boxed_3495_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
lean_dec(v_a_3493_);
lean_dec_ref(v_a_3492_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3490_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr(lean_object* v_00_u03b1_3497_, lean_object* v_ev_3498_, lean_object* v_e_3499_, uint8_t v_didWHNF_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_){
_start:
{
lean_object* v___x_3506_; 
v___x_3506_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(v_ev_3498_, v_e_3499_, v_didWHNF_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___boxed(lean_object* v_00_u03b1_3507_, lean_object* v_ev_3508_, lean_object* v_e_3509_, lean_object* v_didWHNF_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_){
_start:
{
uint8_t v_didWHNF_boxed_3516_; lean_object* v_res_3517_; 
v_didWHNF_boxed_3516_ = lean_unbox(v_didWHNF_3510_);
v_res_3517_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr(v_00_u03b1_3507_, v_ev_3508_, v_e_3509_, v_didWHNF_boxed_3516_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
lean_dec(v_a_3514_);
lean_dec_ref(v_a_3513_);
lean_dec(v_a_3512_);
lean_dec_ref(v_a_3511_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0(lean_object* v_ev_3524_, lean_object* v_e_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v_e_x27_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___x_3556_; uint8_t v___x_3557_; 
v___x_3556_ = l_Lean_Expr_cleanupAnnotations(v_e_3525_);
v___x_3557_ = l_Lean_Expr_isApp(v___x_3556_);
if (v___x_3557_ == 0)
{
lean_object* v___x_3558_; 
lean_dec_ref(v___x_3556_);
lean_dec_ref(v_ev_3524_);
v___x_3558_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3558_;
}
else
{
lean_object* v_arg_3559_; lean_object* v___x_3560_; uint8_t v___x_3561_; 
v_arg_3559_ = lean_ctor_get(v___x_3556_, 1);
lean_inc_ref(v_arg_3559_);
v___x_3560_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3556_);
v___x_3561_ = l_Lean_Expr_isApp(v___x_3560_);
if (v___x_3561_ == 0)
{
lean_object* v___x_3562_; 
lean_dec_ref(v___x_3560_);
lean_dec_ref(v_arg_3559_);
lean_dec_ref(v_ev_3524_);
v___x_3562_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3562_;
}
else
{
lean_object* v___x_3563_; lean_object* v___x_3564_; uint8_t v___x_3565_; 
v___x_3563_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3560_);
v___x_3564_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0));
v___x_3565_ = l_Lean_Expr_isConstOf(v___x_3563_, v___x_3564_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3566_; uint8_t v___x_3567_; 
v___x_3566_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1));
v___x_3567_ = l_Lean_Expr_isConstOf(v___x_3563_, v___x_3566_);
lean_dec_ref(v___x_3563_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3568_; 
lean_dec_ref(v_arg_3559_);
lean_dec_ref(v_ev_3524_);
v___x_3568_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3568_;
}
else
{
v_e_x27_3532_ = v_arg_3559_;
v___y_3533_ = v___y_3526_;
v___y_3534_ = v___y_3527_;
v___y_3535_ = v___y_3528_;
v___y_3536_ = v___y_3529_;
goto v___jp_3531_;
}
}
else
{
lean_dec_ref(v___x_3563_);
v_e_x27_3532_ = v_arg_3559_;
v___y_3533_ = v___y_3526_;
v___y_3534_ = v___y_3527_;
v___y_3535_ = v___y_3528_;
v___y_3536_ = v___y_3529_;
goto v___jp_3531_;
}
}
}
v___jp_3531_:
{
uint8_t v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = 0;
v___x_3538_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(v_ev_3524_, v_e_x27_3532_, v___x_3537_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3547_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3541_ = v___x_3538_;
v_isShared_3542_ = v_isSharedCheck_3547_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3538_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3547_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3543_; lean_object* v___x_3545_; 
v___x_3543_ = lean_array_mk(v_a_3539_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 0, v___x_3543_);
v___x_3545_ = v___x_3541_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
v_a_3548_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3538_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3538_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___boxed(lean_object* v_ev_3569_, lean_object* v_e_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0(v_ev_3569_, v_e_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
return v_res_3576_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0(void){
_start:
{
uint8_t v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3577_ = 0;
v___x_3578_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__1));
v___x_3579_ = l_Lean_MessageData_ofConstName(v___x_3578_, v___x_3577_);
return v___x_3579_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1(void){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3580_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0, &l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0);
v___x_3581_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
lean_ctor_set(v___x_3582_, 1, v___x_3580_);
return v___x_3582_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2(void){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3583_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3584_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1);
v___x_3585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3584_);
lean_ctor_set(v___x_3585_, 1, v___x_3583_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg(lean_object* v_ev_3586_, lean_object* v_e_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_){
_start:
{
lean_object* v___f_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___f_3593_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3593_, 0, v_ev_3586_);
v___x_3594_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2);
v___x_3595_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___f_3593_, v_e_3587_, v___x_3594_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___boxed(lean_object* v_ev_3596_, lean_object* v_e_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg(v_ev_3596_, v_e_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_);
lean_dec(v_a_3601_);
lean_dec_ref(v_a_3600_);
lean_dec(v_a_3599_);
lean_dec_ref(v_a_3598_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr(lean_object* v_00_u03b1_3604_, lean_object* v_ev_3605_, lean_object* v_e_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg(v_ev_3605_, v_e_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___boxed(lean_object* v_00_u03b1_3613_, lean_object* v_ev_3614_, lean_object* v_e_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_){
_start:
{
lean_object* v_res_3621_; 
v_res_3621_ = l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr(v_00_u03b1_3613_, v_ev_3614_, v_e_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_);
lean_dec(v_a_3619_);
lean_dec_ref(v_a_3618_);
lean_dec(v_a_3617_);
lean_dec_ref(v_a_3616_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore(lean_object* v_e_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_){
_start:
{
lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; uint8_t v___y_3633_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; uint8_t v___y_3649_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; uint8_t v___y_3694_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; uint8_t v___y_3741_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; uint8_t v___y_3788_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___x_3864_; uint8_t v___x_3865_; 
lean_inc_ref(v_e_3622_);
v___x_3864_ = l_Lean_Expr_cleanupAnnotations(v_e_3622_);
v___x_3865_ = l_Lean_Expr_isApp(v___x_3864_);
if (v___x_3865_ == 0)
{
lean_dec_ref(v___x_3864_);
v___y_3829_ = v_a_3623_;
v___y_3830_ = v_a_3624_;
v___y_3831_ = v_a_3625_;
v___y_3832_ = v_a_3626_;
goto v___jp_3828_;
}
else
{
lean_object* v_arg_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; uint8_t v___x_3869_; 
v_arg_3866_ = lean_ctor_get(v___x_3864_, 1);
lean_inc_ref(v_arg_3866_);
v___x_3867_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3864_);
v___x_3868_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8));
v___x_3869_ = l_Lean_Expr_isConstOf(v___x_3867_, v___x_3868_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3870_; uint8_t v___x_3871_; 
v___x_3870_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10));
v___x_3871_ = l_Lean_Expr_isConstOf(v___x_3867_, v___x_3870_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3872_; uint8_t v___x_3873_; 
v___x_3872_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13));
v___x_3873_ = l_Lean_Expr_isConstOf(v___x_3867_, v___x_3872_);
if (v___x_3873_ == 0)
{
lean_object* v___x_3874_; uint8_t v___x_3875_; 
v___x_3874_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15));
v___x_3875_ = l_Lean_Expr_isConstOf(v___x_3867_, v___x_3874_);
if (v___x_3875_ == 0)
{
lean_object* v___x_3876_; uint8_t v___x_3877_; 
v___x_3876_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3));
v___x_3877_ = l_Lean_Expr_isConstOf(v___x_3867_, v___x_3876_);
lean_dec_ref(v___x_3867_);
if (v___x_3877_ == 0)
{
lean_dec_ref(v_arg_3866_);
v___y_3829_ = v_a_3623_;
v___y_3830_ = v_a_3624_;
v___y_3831_ = v_a_3625_;
v___y_3832_ = v_a_3626_;
goto v___jp_3828_;
}
else
{
lean_object* v___x_3878_; 
lean_dec_ref(v_e_3622_);
v___x_3878_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v_arg_3866_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3888_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3881_ = v___x_3878_;
v_isShared_3882_ = v_isSharedCheck_3888_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3878_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3888_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3883_; uint8_t v___x_3884_; lean_object* v___x_3886_; 
v___x_3883_ = lean_alloc_ctor(1, 0, 1);
v___x_3884_ = lean_unbox(v_a_3879_);
lean_dec(v_a_3879_);
lean_ctor_set_uint8(v___x_3883_, 0, v___x_3884_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 0, v___x_3883_);
v___x_3886_ = v___x_3881_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3883_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
else
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
v_a_3889_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3878_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3878_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
}
else
{
lean_object* v___x_3897_; 
lean_dec_ref(v___x_3867_);
lean_dec_ref(v_e_3622_);
v___x_3897_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v_arg_3866_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3906_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3900_ = v___x_3897_;
v_isShared_3901_ = v_isSharedCheck_3906_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3897_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3906_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3902_; lean_object* v___x_3904_; 
v___x_3902_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3902_, 0, v_a_3898_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3902_);
v___x_3904_ = v___x_3900_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3902_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
else
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3914_; 
v_a_3907_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3909_ = v___x_3897_;
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3897_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
}
else
{
lean_object* v___x_3915_; 
lean_dec_ref(v___x_3867_);
lean_dec_ref(v_e_3622_);
v___x_3915_ = l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr(v_arg_3866_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3924_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3918_ = v___x_3915_;
v_isShared_3919_ = v_isSharedCheck_3924_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3915_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3924_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3920_; lean_object* v___x_3922_; 
v___x_3920_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3920_, 0, v_a_3916_);
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 0, v___x_3920_);
v___x_3922_ = v___x_3918_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3920_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
v_a_3925_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3915_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3915_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
}
else
{
lean_object* v___x_3933_; 
lean_dec_ref(v___x_3867_);
lean_dec_ref(v_e_3622_);
v___x_3933_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr(v_arg_3866_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3942_; 
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3936_ = v___x_3933_;
v_isShared_3937_ = v_isSharedCheck_3942_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3933_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3942_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3938_; lean_object* v___x_3940_; 
v___x_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3938_, 0, v_a_3934_);
if (v_isShared_3937_ == 0)
{
lean_ctor_set(v___x_3936_, 0, v___x_3938_);
v___x_3940_ = v___x_3936_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3938_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
v_a_3943_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3933_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3933_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
}
else
{
lean_object* v___x_3951_; 
lean_dec_ref(v___x_3867_);
lean_dec_ref(v_e_3622_);
v___x_3951_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr(v_arg_3866_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3960_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3954_ = v___x_3951_;
v_isShared_3955_ = v_isSharedCheck_3960_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_a_3952_);
lean_dec(v___x_3951_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3960_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3956_; lean_object* v___x_3958_; 
v___x_3956_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3956_, 0, v_a_3952_);
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 0, v___x_3956_);
v___x_3958_ = v___x_3954_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3956_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
}
else
{
lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3968_; 
v_a_3961_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3963_ = v___x_3951_;
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v___x_3951_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3966_; 
if (v_isShared_3964_ == 0)
{
v___x_3966_ = v___x_3963_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3961_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
}
}
v___jp_3628_:
{
if (v___y_3633_ == 0)
{
lean_object* v___x_3634_; 
lean_dec_ref(v___y_3632_);
v___x_3634_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3631_, v___y_3630_, v___y_3629_);
lean_dec_ref(v___y_3631_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v___x_3635_; 
lean_dec_ref_known(v___x_3634_, 1);
v___x_3635_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3635_;
}
else
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3643_; 
v_a_3636_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3638_ = v___x_3634_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3634_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
if (v_isShared_3639_ == 0)
{
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3636_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
else
{
lean_dec_ref(v___y_3631_);
return v___y_3632_;
}
}
v___jp_3644_:
{
if (v___y_3649_ == 0)
{
lean_object* v___x_3650_; 
lean_dec_ref(v___y_3646_);
v___x_3650_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3647_, v___y_3648_, v___y_3645_);
lean_dec_ref(v___y_3647_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v___x_3651_; 
lean_dec_ref_known(v___x_3650_, 1);
v___x_3651_ = l_Lean_Meta_saveState___redArg(v___y_3648_, v___y_3645_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; lean_object* v___x_3653_; 
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_a_3652_);
lean_dec_ref_known(v___x_3651_, 1);
v___x_3653_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg(v_e_3622_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3662_; 
lean_dec(v_a_3652_);
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3656_ = v___x_3653_;
v_isShared_3657_ = v_isSharedCheck_3662_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3653_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3662_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3658_; lean_object* v___x_3660_; 
v___x_3658_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3658_, 0, v_a_3654_);
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 0, v___x_3658_);
v___x_3660_ = v___x_3656_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3658_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3672_; 
v_a_3663_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3665_ = v___x_3653_;
v_isShared_3666_ = v_isSharedCheck_3672_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3653_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3672_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
lean_inc(v_a_3663_);
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
uint8_t v___x_3669_; 
v___x_3669_ = l_Lean_Exception_isInterrupt(v_a_3663_);
if (v___x_3669_ == 0)
{
uint8_t v___x_3670_; 
v___x_3670_ = l_Lean_Exception_isRuntime(v_a_3663_);
v___y_3629_ = v___y_3645_;
v___y_3630_ = v___y_3648_;
v___y_3631_ = v_a_3652_;
v___y_3632_ = v___x_3668_;
v___y_3633_ = v___x_3670_;
goto v___jp_3628_;
}
else
{
lean_dec(v_a_3663_);
v___y_3629_ = v___y_3645_;
v___y_3630_ = v___y_3648_;
v___y_3631_ = v_a_3652_;
v___y_3632_ = v___x_3668_;
v___y_3633_ = v___x_3669_;
goto v___jp_3628_;
}
}
}
}
}
else
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
lean_dec_ref(v_e_3622_);
v_a_3673_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___x_3651_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3651_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec_ref(v_e_3622_);
v_a_3681_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3650_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3650_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
else
{
lean_dec_ref(v___y_3647_);
lean_dec_ref(v_e_3622_);
return v___y_3646_;
}
}
v___jp_3689_:
{
if (v___y_3694_ == 0)
{
lean_object* v___x_3695_; 
lean_dec_ref(v___y_3693_);
v___x_3695_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3692_, v___y_3691_, v___y_3690_);
lean_dec_ref(v___y_3692_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v___x_3696_; 
lean_dec_ref_known(v___x_3695_, 1);
v___x_3696_ = l_Lean_Meta_saveState___redArg(v___y_3691_, v___y_3690_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v_a_3697_; lean_object* v___x_3698_; 
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
lean_inc(v_a_3697_);
lean_dec_ref_known(v___x_3696_, 1);
lean_inc_ref(v_e_3622_);
v___x_3698_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg(v_e_3622_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3707_; 
lean_dec(v_a_3697_);
lean_dec_ref(v_e_3622_);
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3701_ = v___x_3698_;
v_isShared_3702_ = v_isSharedCheck_3707_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3698_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3707_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3703_; lean_object* v___x_3705_; 
v___x_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3703_, 0, v_a_3699_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 0, v___x_3703_);
v___x_3705_ = v___x_3701_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3703_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3717_; 
v_a_3708_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3710_ = v___x_3698_;
v_isShared_3711_ = v_isSharedCheck_3717_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3698_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3717_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
lean_inc(v_a_3708_);
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
uint8_t v___x_3714_; 
v___x_3714_ = l_Lean_Exception_isInterrupt(v_a_3708_);
if (v___x_3714_ == 0)
{
uint8_t v___x_3715_; 
v___x_3715_ = l_Lean_Exception_isRuntime(v_a_3708_);
v___y_3645_ = v___y_3690_;
v___y_3646_ = v___x_3713_;
v___y_3647_ = v_a_3697_;
v___y_3648_ = v___y_3691_;
v___y_3649_ = v___x_3715_;
goto v___jp_3644_;
}
else
{
lean_dec(v_a_3708_);
v___y_3645_ = v___y_3690_;
v___y_3646_ = v___x_3713_;
v___y_3647_ = v_a_3697_;
v___y_3648_ = v___y_3691_;
v___y_3649_ = v___x_3714_;
goto v___jp_3644_;
}
}
}
}
}
else
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3725_; 
lean_dec_ref(v_e_3622_);
v_a_3718_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3720_ = v___x_3696_;
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3696_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
if (v_isShared_3721_ == 0)
{
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3718_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
else
{
lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
lean_dec_ref(v_e_3622_);
v_a_3726_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3728_ = v___x_3695_;
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_a_3726_);
lean_dec(v___x_3695_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_a_3726_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
else
{
lean_dec_ref(v___y_3692_);
lean_dec_ref(v_e_3622_);
return v___y_3693_;
}
}
v___jp_3734_:
{
if (v___y_3741_ == 0)
{
lean_object* v___x_3742_; 
lean_dec_ref(v___y_3735_);
v___x_3742_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3738_, v___y_3737_, v___y_3736_);
lean_dec_ref(v___y_3738_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v___x_3743_; 
lean_dec_ref_known(v___x_3742_, 1);
v___x_3743_ = l_Lean_Meta_saveState___redArg(v___y_3737_, v___y_3736_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v___x_3745_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
lean_inc(v_a_3744_);
lean_dec_ref_known(v___x_3743_, 1);
lean_inc_ref(v_e_3622_);
v___x_3745_ = l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore(v_e_3622_, v___y_3739_, v___y_3737_, v___y_3740_, v___y_3736_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3754_; 
lean_dec(v_a_3744_);
lean_dec_ref(v_e_3622_);
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3748_ = v___x_3745_;
v_isShared_3749_ = v_isSharedCheck_3754_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3745_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3754_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3750_; lean_object* v___x_3752_; 
v___x_3750_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3750_, 0, v_a_3746_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v___x_3750_);
v___x_3752_ = v___x_3748_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3750_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3764_; 
v_a_3755_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3757_ = v___x_3745_;
v_isShared_3758_ = v_isSharedCheck_3764_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3745_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3764_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
lean_inc(v_a_3755_);
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
uint8_t v___x_3761_; 
v___x_3761_ = l_Lean_Exception_isInterrupt(v_a_3755_);
if (v___x_3761_ == 0)
{
uint8_t v___x_3762_; 
v___x_3762_ = l_Lean_Exception_isRuntime(v_a_3755_);
v___y_3690_ = v___y_3736_;
v___y_3691_ = v___y_3737_;
v___y_3692_ = v_a_3744_;
v___y_3693_ = v___x_3760_;
v___y_3694_ = v___x_3762_;
goto v___jp_3689_;
}
else
{
lean_dec(v_a_3755_);
v___y_3690_ = v___y_3736_;
v___y_3691_ = v___y_3737_;
v___y_3692_ = v_a_3744_;
v___y_3693_ = v___x_3760_;
v___y_3694_ = v___x_3761_;
goto v___jp_3689_;
}
}
}
}
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
lean_dec_ref(v_e_3622_);
v_a_3765_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3743_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3743_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
lean_dec_ref(v_e_3622_);
v_a_3773_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3742_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3742_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3778_; 
if (v_isShared_3776_ == 0)
{
v___x_3778_ = v___x_3775_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3773_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
else
{
lean_dec_ref(v___y_3738_);
lean_dec_ref(v_e_3622_);
return v___y_3735_;
}
}
v___jp_3781_:
{
if (v___y_3788_ == 0)
{
lean_object* v___x_3789_; 
lean_dec_ref(v___y_3782_);
v___x_3789_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3783_, v___y_3785_, v___y_3784_);
lean_dec_ref(v___y_3783_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v___x_3790_; 
lean_dec_ref_known(v___x_3789_, 1);
v___x_3790_ = l_Lean_Meta_saveState___redArg(v___y_3785_, v___y_3784_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v_a_3791_; lean_object* v___x_3792_; 
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
lean_inc(v_a_3791_);
lean_dec_ref_known(v___x_3790_, 1);
lean_inc_ref(v_e_3622_);
v___x_3792_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(v_e_3622_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3801_; 
lean_dec(v_a_3791_);
lean_dec_ref(v_e_3622_);
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3795_ = v___x_3792_;
v_isShared_3796_ = v_isSharedCheck_3801_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_a_3793_);
lean_dec(v___x_3792_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3801_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3797_; lean_object* v___x_3799_; 
v___x_3797_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3797_, 0, v_a_3793_);
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 0, v___x_3797_);
v___x_3799_ = v___x_3795_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3797_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3811_; 
v_a_3802_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3804_ = v___x_3792_;
v_isShared_3805_ = v_isSharedCheck_3811_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3792_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3811_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
lean_inc(v_a_3802_);
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
uint8_t v___x_3808_; 
v___x_3808_ = l_Lean_Exception_isInterrupt(v_a_3802_);
if (v___x_3808_ == 0)
{
uint8_t v___x_3809_; 
v___x_3809_ = l_Lean_Exception_isRuntime(v_a_3802_);
v___y_3735_ = v___x_3807_;
v___y_3736_ = v___y_3784_;
v___y_3737_ = v___y_3785_;
v___y_3738_ = v_a_3791_;
v___y_3739_ = v___y_3786_;
v___y_3740_ = v___y_3787_;
v___y_3741_ = v___x_3809_;
goto v___jp_3734_;
}
else
{
lean_dec(v_a_3802_);
v___y_3735_ = v___x_3807_;
v___y_3736_ = v___y_3784_;
v___y_3737_ = v___y_3785_;
v___y_3738_ = v_a_3791_;
v___y_3739_ = v___y_3786_;
v___y_3740_ = v___y_3787_;
v___y_3741_ = v___x_3808_;
goto v___jp_3734_;
}
}
}
}
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_dec_ref(v_e_3622_);
v_a_3812_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3790_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3790_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
lean_dec_ref(v_e_3622_);
v_a_3820_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3789_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3789_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
else
{
lean_dec_ref(v___y_3783_);
lean_dec_ref(v_e_3622_);
return v___y_3782_;
}
}
v___jp_3828_:
{
lean_object* v___x_3833_; 
v___x_3833_ = l_Lean_Meta_saveState___redArg(v___y_3830_, v___y_3832_);
if (lean_obj_tag(v___x_3833_) == 0)
{
lean_object* v_a_3834_; lean_object* v___x_3835_; 
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
lean_inc(v_a_3834_);
lean_dec_ref_known(v___x_3833_, 1);
lean_inc_ref(v_e_3622_);
v___x_3835_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore(v_e_3622_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3845_; 
lean_dec(v_a_3834_);
lean_dec_ref(v_e_3622_);
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3838_ = v___x_3835_;
v_isShared_3839_ = v_isSharedCheck_3845_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3835_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3845_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3840_; uint8_t v___x_3841_; lean_object* v___x_3843_; 
v___x_3840_ = lean_alloc_ctor(1, 0, 1);
v___x_3841_ = lean_unbox(v_a_3836_);
lean_dec(v_a_3836_);
lean_ctor_set_uint8(v___x_3840_, 0, v___x_3841_);
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 0, v___x_3840_);
v___x_3843_ = v___x_3838_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v___x_3840_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3855_; 
v_a_3846_ = lean_ctor_get(v___x_3835_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3848_ = v___x_3835_;
v_isShared_3849_ = v_isSharedCheck_3855_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3835_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3855_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
lean_inc(v_a_3846_);
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3846_);
v___x_3851_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
uint8_t v___x_3852_; 
v___x_3852_ = l_Lean_Exception_isInterrupt(v_a_3846_);
if (v___x_3852_ == 0)
{
uint8_t v___x_3853_; 
v___x_3853_ = l_Lean_Exception_isRuntime(v_a_3846_);
v___y_3782_ = v___x_3851_;
v___y_3783_ = v_a_3834_;
v___y_3784_ = v___y_3832_;
v___y_3785_ = v___y_3830_;
v___y_3786_ = v___y_3829_;
v___y_3787_ = v___y_3831_;
v___y_3788_ = v___x_3853_;
goto v___jp_3781_;
}
else
{
lean_dec(v_a_3846_);
v___y_3782_ = v___x_3851_;
v___y_3783_ = v_a_3834_;
v___y_3784_ = v___y_3832_;
v___y_3785_ = v___y_3830_;
v___y_3786_ = v___y_3829_;
v___y_3787_ = v___y_3831_;
v___y_3788_ = v___x_3852_;
goto v___jp_3781_;
}
}
}
}
}
else
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3863_; 
lean_dec_ref(v_e_3622_);
v_a_3856_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3858_ = v___x_3833_;
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3833_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3861_; 
if (v_isShared_3859_ == 0)
{
v___x_3861_ = v___x_3858_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3856_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore___boxed(lean_object* v_e_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore(v_e_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
lean_dec(v_a_3973_);
lean_dec_ref(v_a_3972_);
lean_dec(v_a_3971_);
lean_dec_ref(v_a_3970_);
return v_res_3975_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1(void){
_start:
{
uint8_t v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3977_ = 0;
v___x_3978_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1));
v___x_3979_ = l_Lean_MessageData_ofConstName(v___x_3978_, v___x_3977_);
return v___x_3979_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2(void){
_start:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3980_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1);
v___x_3981_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3981_);
lean_ctor_set(v___x_3982_, 1, v___x_3980_);
return v___x_3982_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3(void){
_start:
{
lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3983_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3984_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2);
v___x_3985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3984_);
lean_ctor_set(v___x_3985_, 1, v___x_3983_);
return v___x_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr(lean_object* v_e_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_){
_start:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3992_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__0));
v___x_3993_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3, &l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3);
v___x_3994_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_3992_, v_e_3986_, v___x_3993_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_);
return v___x_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___boxed(lean_object* v_e_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_){
_start:
{
lean_object* v_res_4001_; 
v_res_4001_ = l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr(v_e_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
lean_dec(v_a_3999_);
lean_dec_ref(v_a_3998_);
lean_dec(v_a_3997_);
lean_dec_ref(v_a_3996_);
return v_res_4001_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1(void){
_start:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4003_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3);
v___x_4004_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__0));
v___x_4005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
lean_ctor_set(v___x_4005_, 1, v___x_4003_);
return v___x_4005_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instBool(void){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1);
return v___x_4006_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1(void){
_start:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4008_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3);
v___x_4009_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__0));
v___x_4010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
lean_ctor_set(v___x_4010_, 1, v___x_4008_);
return v___x_4010_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instNat(void){
_start:
{
lean_object* v___x_4011_; 
v___x_4011_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1);
return v___x_4011_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1(void){
_start:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4013_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3);
v___x_4014_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__0));
v___x_4015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4014_);
lean_ctor_set(v___x_4015_, 1, v___x_4013_);
return v___x_4015_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instInt(void){
_start:
{
lean_object* v___x_4016_; 
v___x_4016_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1);
return v___x_4016_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1(void){
_start:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; 
v___x_4018_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3);
v___x_4019_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__0));
v___x_4020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4019_);
lean_ctor_set(v___x_4020_, 1, v___x_4018_);
return v___x_4020_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instString(void){
_start:
{
lean_object* v___x_4021_; 
v___x_4021_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1);
return v___x_4021_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1(void){
_start:
{
lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4023_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3);
v___x_4024_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__0));
v___x_4025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4024_);
lean_ctor_set(v___x_4025_, 1, v___x_4023_);
return v___x_4025_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instName(void){
_start:
{
lean_object* v___x_4026_; 
v___x_4026_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1);
return v___x_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instOption___redArg(lean_object* v_inst_4027_){
_start:
{
lean_object* v_evalExpr_4028_; lean_object* v_expectedType_x3f_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4050_; 
v_evalExpr_4028_ = lean_ctor_get(v_inst_4027_, 0);
v_expectedType_x3f_4029_ = lean_ctor_get(v_inst_4027_, 1);
v_isSharedCheck_4050_ = !lean_is_exclusive(v_inst_4027_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4031_ = v_inst_4027_;
v_isShared_4032_ = v_isSharedCheck_4050_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_expectedType_x3f_4029_);
lean_inc(v_evalExpr_4028_);
lean_dec(v_inst_4027_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4050_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4033_; 
v___x_4033_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___boxed), 8, 2);
lean_closure_set(v___x_4033_, 0, lean_box(0));
lean_closure_set(v___x_4033_, 1, v_evalExpr_4028_);
if (lean_obj_tag(v_expectedType_x3f_4029_) == 0)
{
lean_object* v___x_4035_; 
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 0, v___x_4033_);
v___x_4035_ = v___x_4031_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_4033_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v_expectedType_x3f_4029_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
else
{
lean_object* v_val_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4049_; 
v_val_4037_ = lean_ctor_get(v_expectedType_x3f_4029_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v_expectedType_x3f_4029_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4039_ = v_expectedType_x3f_4029_;
v_isShared_4040_ = v_isSharedCheck_4049_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_val_4037_);
lean_dec(v_expectedType_x3f_4029_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4049_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4044_; 
v___x_4041_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2);
v___x_4042_ = l_Lean_Expr_app___override(v___x_4041_, v_val_4037_);
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 0, v___x_4042_);
v___x_4044_ = v___x_4039_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v___x_4042_);
v___x_4044_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
lean_object* v___x_4046_; 
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 1, v___x_4044_);
lean_ctor_set(v___x_4031_, 0, v___x_4033_);
v___x_4046_ = v___x_4031_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v___x_4033_);
lean_ctor_set(v_reuseFailAlloc_4047_, 1, v___x_4044_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instOption(lean_object* v_00_u03b1_4051_, lean_object* v_inst_4052_){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Lean_Elab_ConfigEval_EvalExpr_instOption___redArg(v_inst_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0(lean_object* v_evalExpr_4054_, lean_object* v_e_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
uint8_t v___x_4061_; lean_object* v___x_4062_; 
v___x_4061_ = 0;
v___x_4062_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(v_evalExpr_4054_, v_e_4055_, v___x_4061_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0___boxed(lean_object* v_evalExpr_4063_, lean_object* v_e_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0(v_evalExpr_4063_, v_e_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg(lean_object* v_inst_4071_){
_start:
{
lean_object* v_evalExpr_4072_; lean_object* v_expectedType_x3f_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4094_; 
v_evalExpr_4072_ = lean_ctor_get(v_inst_4071_, 0);
v_expectedType_x3f_4073_ = lean_ctor_get(v_inst_4071_, 1);
v_isSharedCheck_4094_ = !lean_is_exclusive(v_inst_4071_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4075_ = v_inst_4071_;
v_isShared_4076_ = v_isSharedCheck_4094_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_expectedType_x3f_4073_);
lean_inc(v_evalExpr_4072_);
lean_dec(v_inst_4071_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4094_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___f_4077_; 
v___f_4077_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4077_, 0, v_evalExpr_4072_);
if (lean_obj_tag(v_expectedType_x3f_4073_) == 0)
{
lean_object* v___x_4079_; 
if (v_isShared_4076_ == 0)
{
lean_ctor_set(v___x_4075_, 0, v___f_4077_);
v___x_4079_ = v___x_4075_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___f_4077_);
lean_ctor_set(v_reuseFailAlloc_4080_, 1, v_expectedType_x3f_4073_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
else
{
lean_object* v_val_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4093_; 
v_val_4081_ = lean_ctor_get(v_expectedType_x3f_4073_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v_expectedType_x3f_4073_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4083_ = v_expectedType_x3f_4073_;
v_isShared_4084_ = v_isSharedCheck_4093_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_val_4081_);
lean_dec(v_expectedType_x3f_4073_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4093_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4088_; 
v___x_4085_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1);
v___x_4086_ = l_Lean_Expr_app___override(v___x_4085_, v_val_4081_);
if (v_isShared_4084_ == 0)
{
lean_ctor_set(v___x_4083_, 0, v___x_4086_);
v___x_4088_ = v___x_4083_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_4086_);
v___x_4088_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
lean_object* v___x_4090_; 
if (v_isShared_4076_ == 0)
{
lean_ctor_set(v___x_4075_, 1, v___x_4088_);
lean_ctor_set(v___x_4075_, 0, v___f_4077_);
v___x_4090_ = v___x_4075_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___f_4077_);
lean_ctor_set(v_reuseFailAlloc_4091_, 1, v___x_4088_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList(lean_object* v_00_u03b1_4095_, lean_object* v_inst_4096_){
_start:
{
lean_object* v___x_4097_; 
v___x_4097_ = l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg(v_inst_4096_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instArray___redArg(lean_object* v_inst_4098_){
_start:
{
lean_object* v_evalExpr_4099_; lean_object* v_expectedType_x3f_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4121_; 
v_evalExpr_4099_ = lean_ctor_get(v_inst_4098_, 0);
v_expectedType_x3f_4100_ = lean_ctor_get(v_inst_4098_, 1);
v_isSharedCheck_4121_ = !lean_is_exclusive(v_inst_4098_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4102_ = v_inst_4098_;
v_isShared_4103_ = v_isSharedCheck_4121_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_expectedType_x3f_4100_);
lean_inc(v_evalExpr_4099_);
lean_dec(v_inst_4098_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4121_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4104_; 
v___x_4104_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___boxed), 8, 2);
lean_closure_set(v___x_4104_, 0, lean_box(0));
lean_closure_set(v___x_4104_, 1, v_evalExpr_4099_);
if (lean_obj_tag(v_expectedType_x3f_4100_) == 0)
{
lean_object* v___x_4106_; 
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 0, v___x_4104_);
v___x_4106_ = v___x_4102_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v___x_4104_);
lean_ctor_set(v_reuseFailAlloc_4107_, 1, v_expectedType_x3f_4100_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
else
{
lean_object* v_val_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4120_; 
v_val_4108_ = lean_ctor_get(v_expectedType_x3f_4100_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v_expectedType_x3f_4100_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4110_ = v_expectedType_x3f_4100_;
v_isShared_4111_ = v_isSharedCheck_4120_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_val_4108_);
lean_dec(v_expectedType_x3f_4100_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4120_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4115_; 
v___x_4112_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2);
v___x_4113_ = l_Lean_Expr_app___override(v___x_4112_, v_val_4108_);
if (v_isShared_4111_ == 0)
{
lean_ctor_set(v___x_4110_, 0, v___x_4113_);
v___x_4115_ = v___x_4110_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v___x_4113_);
v___x_4115_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
lean_object* v___x_4117_; 
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 1, v___x_4115_);
lean_ctor_set(v___x_4102_, 0, v___x_4104_);
v___x_4117_ = v___x_4102_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___x_4104_);
lean_ctor_set(v_reuseFailAlloc_4118_, 1, v___x_4115_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instArray(lean_object* v_00_u03b1_4122_, lean_object* v_inst_4123_){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = l_Lean_Elab_ConfigEval_EvalExpr_instArray___redArg(v_inst_4123_);
return v___x_4124_;
}
}
lean_object* runtime_initialize_Lean_Elab_ConfigEval_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ConfigEval_Instances(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_ConfigEval_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_ConfigEval_EvalTerm_instBool = _init_l_Lean_Elab_ConfigEval_EvalTerm_instBool();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalTerm_instBool);
l_Lean_Elab_ConfigEval_EvalTerm_instNat = _init_l_Lean_Elab_ConfigEval_EvalTerm_instNat();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalTerm_instNat);
l_Lean_Elab_ConfigEval_EvalTerm_instInt = _init_l_Lean_Elab_ConfigEval_EvalTerm_instInt();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalTerm_instInt);
l_Lean_Elab_ConfigEval_EvalTerm_instString = _init_l_Lean_Elab_ConfigEval_EvalTerm_instString();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalTerm_instString);
l_Lean_Elab_ConfigEval_EvalTerm_instName = _init_l_Lean_Elab_ConfigEval_EvalTerm_instName();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalTerm_instName);
l_Lean_Elab_ConfigEval_EvalTerm_instDataValue = _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue);
l_Lean_Elab_ConfigEval_EvalExpr_instBool = _init_l_Lean_Elab_ConfigEval_EvalExpr_instBool();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalExpr_instBool);
l_Lean_Elab_ConfigEval_EvalExpr_instNat = _init_l_Lean_Elab_ConfigEval_EvalExpr_instNat();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalExpr_instNat);
l_Lean_Elab_ConfigEval_EvalExpr_instInt = _init_l_Lean_Elab_ConfigEval_EvalExpr_instInt();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalExpr_instInt);
l_Lean_Elab_ConfigEval_EvalExpr_instString = _init_l_Lean_Elab_ConfigEval_EvalExpr_instString();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalExpr_instString);
l_Lean_Elab_ConfigEval_EvalExpr_instName = _init_l_Lean_Elab_ConfigEval_EvalExpr_instName();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalExpr_instName);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_ConfigEval_Instances(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_ConfigEval_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ConfigEval_Instances(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_ConfigEval_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_ConfigEval_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_ConfigEval_Instances(builtin);
}
#ifdef __cplusplus
}
#endif
