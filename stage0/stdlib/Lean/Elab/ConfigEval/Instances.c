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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
size_t lean_usize_shift_left(size_t, size_t);
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
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
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
lean_object* lean_erase_macro_scopes(lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__1;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v_id_118_ = lean_erase_macro_scopes(v___x_117_);
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
lean_inc(v___y_122_);
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
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_426_; size_t v___x_427_; size_t v___x_428_; 
v___x_426_ = ((size_t)5ULL);
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_shift_left(v___x_427_, v___x_426_);
return v___x_428_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_429_; size_t v___x_430_; size_t v___x_431_; 
v___x_429_ = ((size_t)1ULL);
v___x_430_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__0);
v___x_431_ = lean_usize_sub(v___x_430_, v___x_429_);
return v___x_431_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_432_, size_t v_x_433_, lean_object* v_x_434_){
_start:
{
if (lean_obj_tag(v_x_432_) == 0)
{
lean_object* v_es_435_; lean_object* v___x_436_; size_t v___x_437_; size_t v___x_438_; size_t v___x_439_; lean_object* v_j_440_; lean_object* v___x_441_; 
v_es_435_ = lean_ctor_get(v_x_432_, 0);
v___x_436_ = lean_box(2);
v___x_437_ = ((size_t)5ULL);
v___x_438_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_439_ = lean_usize_land(v_x_433_, v___x_438_);
v_j_440_ = lean_usize_to_nat(v___x_439_);
v___x_441_ = lean_array_get_borrowed(v___x_436_, v_es_435_, v_j_440_);
lean_dec(v_j_440_);
switch(lean_obj_tag(v___x_441_))
{
case 0:
{
lean_object* v_key_442_; uint8_t v___x_443_; 
v_key_442_ = lean_ctor_get(v___x_441_, 0);
v___x_443_ = l_Lean_instBEqExtraModUse_beq(v_x_434_, v_key_442_);
return v___x_443_;
}
case 1:
{
lean_object* v_node_444_; size_t v___x_445_; 
v_node_444_ = lean_ctor_get(v___x_441_, 0);
v___x_445_ = lean_usize_shift_right(v_x_433_, v___x_437_);
v_x_432_ = v_node_444_;
v_x_433_ = v___x_445_;
goto _start;
}
default: 
{
uint8_t v___x_447_; 
v___x_447_ = 0;
return v___x_447_;
}
}
}
else
{
lean_object* v_ks_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_ks_448_ = lean_ctor_get(v_x_432_, 0);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_ks_448_, v___x_449_, v_x_434_);
return v___x_450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_x_451_, lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
size_t v_x_10220__boxed_454_; uint8_t v_res_455_; lean_object* v_r_456_; 
v_x_10220__boxed_454_ = lean_unbox_usize(v_x_452_);
lean_dec(v_x_452_);
v_res_455_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg(v_x_451_, v_x_10220__boxed_454_, v_x_453_);
lean_dec_ref(v_x_453_);
lean_dec_ref(v_x_451_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg(lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
uint64_t v___x_459_; size_t v___x_460_; uint8_t v___x_461_; 
v___x_459_ = l_Lean_instHashableExtraModUse_hash(v_x_458_);
v___x_460_ = lean_uint64_to_usize(v___x_459_);
v___x_461_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg(v_x_457_, v___x_460_, v_x_458_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
uint8_t v_res_464_; lean_object* v_r_465_; 
v_res_464_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg(v_x_462_, v_x_463_);
lean_dec_ref(v_x_463_);
lean_dec_ref(v_x_462_);
v_r_465_ = lean_box(v_res_464_);
return v_r_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6(lean_object* v_msgData_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___x_472_; lean_object* v_env_473_; lean_object* v___x_474_; lean_object* v_mctx_475_; lean_object* v_lctx_476_; lean_object* v_options_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_472_ = lean_st_ref_get(v___y_470_);
v_env_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc_ref(v_env_473_);
lean_dec(v___x_472_);
v___x_474_ = lean_st_ref_get(v___y_468_);
v_mctx_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc_ref(v_mctx_475_);
lean_dec(v___x_474_);
v_lctx_476_ = lean_ctor_get(v___y_467_, 2);
v_options_477_ = lean_ctor_get(v___y_469_, 2);
lean_inc_ref(v_options_477_);
lean_inc_ref(v_lctx_476_);
v___x_478_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_478_, 0, v_env_473_);
lean_ctor_set(v___x_478_, 1, v_mctx_475_);
lean_ctor_set(v___x_478_, 2, v_lctx_476_);
lean_ctor_set(v___x_478_, 3, v_options_477_);
v___x_479_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v_msgData_466_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_msgData_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6(v_msgData_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
return v_res_487_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_488_; double v___x_489_; 
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = lean_float_of_nat(v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_493_, lean_object* v_msg_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_ref_500_; lean_object* v___x_501_; lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_546_; 
v_ref_500_ = lean_ctor_get(v___y_497_, 5);
v___x_501_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6(v_msg_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_546_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_546_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_546_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v_traceState_507_; lean_object* v_env_508_; lean_object* v_nextMacroScope_509_; lean_object* v_ngen_510_; lean_object* v_auxDeclNGen_511_; lean_object* v_cache_512_; lean_object* v_messages_513_; lean_object* v_infoState_514_; lean_object* v_snapshotTasks_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_545_; 
v___x_506_ = lean_st_ref_take(v___y_498_);
v_traceState_507_ = lean_ctor_get(v___x_506_, 4);
v_env_508_ = lean_ctor_get(v___x_506_, 0);
v_nextMacroScope_509_ = lean_ctor_get(v___x_506_, 1);
v_ngen_510_ = lean_ctor_get(v___x_506_, 2);
v_auxDeclNGen_511_ = lean_ctor_get(v___x_506_, 3);
v_cache_512_ = lean_ctor_get(v___x_506_, 5);
v_messages_513_ = lean_ctor_get(v___x_506_, 6);
v_infoState_514_ = lean_ctor_get(v___x_506_, 7);
v_snapshotTasks_515_ = lean_ctor_get(v___x_506_, 8);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_545_ == 0)
{
v___x_517_ = v___x_506_;
v_isShared_518_ = v_isSharedCheck_545_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_snapshotTasks_515_);
lean_inc(v_infoState_514_);
lean_inc(v_messages_513_);
lean_inc(v_cache_512_);
lean_inc(v_traceState_507_);
lean_inc(v_auxDeclNGen_511_);
lean_inc(v_ngen_510_);
lean_inc(v_nextMacroScope_509_);
lean_inc(v_env_508_);
lean_dec(v___x_506_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_545_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
uint64_t v_tid_519_; lean_object* v_traces_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_544_; 
v_tid_519_ = lean_ctor_get_uint64(v_traceState_507_, sizeof(void*)*1);
v_traces_520_ = lean_ctor_get(v_traceState_507_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v_traceState_507_);
if (v_isSharedCheck_544_ == 0)
{
v___x_522_ = v_traceState_507_;
v_isShared_523_ = v_isSharedCheck_544_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_traces_520_);
lean_dec(v_traceState_507_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_544_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; double v___x_525_; uint8_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_524_ = lean_box(0);
v___x_525_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_526_ = 0;
v___x_527_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_528_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_528_, 0, v_cls_493_);
lean_ctor_set(v___x_528_, 1, v___x_524_);
lean_ctor_set(v___x_528_, 2, v___x_527_);
lean_ctor_set_float(v___x_528_, sizeof(void*)*3, v___x_525_);
lean_ctor_set_float(v___x_528_, sizeof(void*)*3 + 8, v___x_525_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*3 + 16, v___x_526_);
v___x_529_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_530_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v_a_502_);
lean_ctor_set(v___x_530_, 2, v___x_529_);
lean_inc(v_ref_500_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v_ref_500_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = l_Lean_PersistentArray_push___redArg(v_traces_520_, v___x_531_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_532_);
v___x_534_ = v___x_522_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_532_);
lean_ctor_set_uint64(v_reuseFailAlloc_543_, sizeof(void*)*1, v_tid_519_);
v___x_534_ = v_reuseFailAlloc_543_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_536_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 4, v___x_534_);
v___x_536_ = v___x_517_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_env_508_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_nextMacroScope_509_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_ngen_510_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v_auxDeclNGen_511_);
lean_ctor_set(v_reuseFailAlloc_542_, 4, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_542_, 5, v_cache_512_);
lean_ctor_set(v_reuseFailAlloc_542_, 6, v_messages_513_);
lean_ctor_set(v_reuseFailAlloc_542_, 7, v_infoState_514_);
lean_ctor_set(v_reuseFailAlloc_542_, 8, v_snapshotTasks_515_);
v___x_536_ = v_reuseFailAlloc_542_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_537_ = lean_st_ref_set(v___y_498_, v___x_536_);
v___x_538_ = lean_box(0);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_538_);
v___x_540_ = v___x_504_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_547_, lean_object* v_msg_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg(v_cls_547_, v_msg_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
return v_res_554_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__1));
v___x_558_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__0));
v___x_559_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_558_, v___x_557_);
return v___x_559_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_560_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
return v___x_564_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4);
v___x_566_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
lean_ctor_set(v___x_566_, 2, v___x_565_);
lean_ctor_set(v___x_566_, 3, v___x_565_);
lean_ctor_set(v___x_566_, 4, v___x_565_);
lean_ctor_set(v___x_566_, 5, v___x_565_);
return v___x_566_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__9));
v___x_572_ = l_Lean_stringToMessageData(v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__11));
v___x_575_ = l_Lean_stringToMessageData(v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_577_ = l_Lean_stringToMessageData(v___x_576_);
return v___x_577_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v_cls_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_cls_581_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__8));
v___x_582_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__15));
v___x_583_ = l_Lean_Name_append(v___x_582_, v_cls_581_);
return v___x_583_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__17));
v___x_586_ = l_Lean_stringToMessageData(v___x_585_);
return v___x_586_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__19));
v___x_589_ = l_Lean_stringToMessageData(v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0(lean_object* v_mod_594_, uint8_t v_isMeta_595_, lean_object* v_hint_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v___x_604_; lean_object* v_env_605_; uint8_t v_isExporting_606_; lean_object* v___x_607_; lean_object* v_env_608_; lean_object* v___x_609_; lean_object* v_entry_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_604_ = lean_st_ref_get(v___y_602_);
v_env_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc_ref(v_env_605_);
lean_dec(v___x_604_);
v_isExporting_606_ = lean_ctor_get_uint8(v_env_605_, sizeof(void*)*8);
lean_dec_ref(v_env_605_);
v___x_607_ = lean_st_ref_get(v___y_602_);
v_env_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc_ref(v_env_608_);
lean_dec(v___x_607_);
v___x_609_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2);
lean_inc(v_mod_594_);
v_entry_610_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_610_, 0, v_mod_594_);
lean_ctor_set_uint8(v_entry_610_, sizeof(void*)*1, v_isExporting_606_);
lean_ctor_set_uint8(v_entry_610_, sizeof(void*)*1 + 1, v_isMeta_595_);
v___x_611_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_612_ = lean_box(1);
v___x_613_ = lean_box(0);
v___x_656_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_609_, v___x_611_, v_env_608_, v___x_612_, v___x_613_);
v___x_657_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg(v___x_656_, v_entry_610_);
lean_dec(v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v_options_658_; uint8_t v_hasTrace_659_; 
v_options_658_ = lean_ctor_get(v___y_601_, 2);
v_hasTrace_659_ = lean_ctor_get_uint8(v_options_658_, sizeof(void*)*1);
if (v_hasTrace_659_ == 0)
{
lean_dec(v_hint_596_);
lean_dec(v_mod_594_);
v___y_615_ = v___y_600_;
v___y_616_ = v___y_602_;
goto v___jp_614_;
}
else
{
lean_object* v_inheritedTraceOptions_660_; lean_object* v_cls_661_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_inheritedTraceOptions_660_ = lean_ctor_get(v___y_601_, 13);
v_cls_661_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__8));
v___x_681_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16);
v___x_682_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_660_, v_options_658_, v___x_681_);
if (v___x_682_ == 0)
{
lean_dec(v_hint_596_);
lean_dec(v_mod_594_);
v___y_615_ = v___y_600_;
v___y_616_ = v___y_602_;
goto v___jp_614_;
}
else
{
lean_object* v___x_683_; lean_object* v___y_685_; 
v___x_683_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18);
if (v_isExporting_606_ == 0)
{
lean_object* v___x_692_; 
v___x_692_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__23));
v___y_685_ = v___x_692_;
goto v___jp_684_;
}
else
{
lean_object* v___x_693_; 
v___x_693_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__24));
v___y_685_ = v___x_693_;
goto v___jp_684_;
}
v___jp_684_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
lean_inc_ref(v___y_685_);
v___x_686_ = l_Lean_stringToMessageData(v___y_685_);
v___x_687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_683_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20);
v___x_689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
if (v_isMeta_595_ == 0)
{
lean_object* v___x_690_; 
v___x_690_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__21));
v___y_668_ = v___x_689_;
v___y_669_ = v___x_690_;
goto v___jp_667_;
}
else
{
lean_object* v___x_691_; 
v___x_691_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__22));
v___y_668_ = v___x_689_;
v___y_669_ = v___x_691_;
goto v___jp_667_;
}
}
}
v___jp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v___y_663_);
lean_ctor_set(v___x_665_, 1, v___y_664_);
v___x_666_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg(v_cls_661_, v___x_665_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_dec_ref_known(v___x_666_, 1);
v___y_615_ = v___y_600_;
v___y_616_ = v___y_602_;
goto v___jp_614_;
}
else
{
lean_dec_ref_known(v_entry_610_, 1);
return v___x_666_;
}
}
v___jp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
lean_inc_ref(v___y_669_);
v___x_670_ = l_Lean_stringToMessageData(v___y_669_);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___y_668_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = l_Lean_MessageData_ofName(v_mod_594_);
v___x_675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_673_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = l_Lean_Name_isAnonymous(v_hint_596_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12);
v___x_678_ = l_Lean_MessageData_ofName(v_hint_596_);
v___x_679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___y_663_ = v___x_675_;
v___y_664_ = v___x_679_;
goto v___jp_662_;
}
else
{
lean_object* v___x_680_; 
lean_dec(v_hint_596_);
v___x_680_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13);
v___y_663_ = v___x_675_;
v___y_664_ = v___x_680_;
goto v___jp_662_;
}
}
}
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; 
lean_dec_ref_known(v_entry_610_, 1);
lean_dec(v_hint_596_);
lean_dec(v_mod_594_);
v___x_694_ = lean_box(0);
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
return v___x_695_;
}
v___jp_614_:
{
lean_object* v___x_617_; lean_object* v_toEnvExtension_618_; lean_object* v_env_619_; lean_object* v_nextMacroScope_620_; lean_object* v_ngen_621_; lean_object* v_auxDeclNGen_622_; lean_object* v_traceState_623_; lean_object* v_messages_624_; lean_object* v_infoState_625_; lean_object* v_snapshotTasks_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_654_; 
v___x_617_ = lean_st_ref_take(v___y_616_);
v_toEnvExtension_618_ = lean_ctor_get(v___x_611_, 0);
v_env_619_ = lean_ctor_get(v___x_617_, 0);
v_nextMacroScope_620_ = lean_ctor_get(v___x_617_, 1);
v_ngen_621_ = lean_ctor_get(v___x_617_, 2);
v_auxDeclNGen_622_ = lean_ctor_get(v___x_617_, 3);
v_traceState_623_ = lean_ctor_get(v___x_617_, 4);
v_messages_624_ = lean_ctor_get(v___x_617_, 6);
v_infoState_625_ = lean_ctor_get(v___x_617_, 7);
v_snapshotTasks_626_ = lean_ctor_get(v___x_617_, 8);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v___x_617_, 5);
lean_dec(v_unused_655_);
v___x_628_ = v___x_617_;
v_isShared_629_ = v_isSharedCheck_654_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_snapshotTasks_626_);
lean_inc(v_infoState_625_);
lean_inc(v_messages_624_);
lean_inc(v_traceState_623_);
lean_inc(v_auxDeclNGen_622_);
lean_inc(v_ngen_621_);
lean_inc(v_nextMacroScope_620_);
lean_inc(v_env_619_);
lean_dec(v___x_617_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_654_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v_asyncMode_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v_asyncMode_630_ = lean_ctor_get(v_toEnvExtension_618_, 2);
v___x_631_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_611_, v_env_619_, v_entry_610_, v_asyncMode_630_, v___x_613_);
v___x_632_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 5, v___x_632_);
lean_ctor_set(v___x_628_, 0, v___x_631_);
v___x_634_ = v___x_628_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_nextMacroScope_620_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v_ngen_621_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v_auxDeclNGen_622_);
lean_ctor_set(v_reuseFailAlloc_653_, 4, v_traceState_623_);
lean_ctor_set(v_reuseFailAlloc_653_, 5, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_653_, 6, v_messages_624_);
lean_ctor_set(v_reuseFailAlloc_653_, 7, v_infoState_625_);
lean_ctor_set(v_reuseFailAlloc_653_, 8, v_snapshotTasks_626_);
v___x_634_ = v_reuseFailAlloc_653_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v_mctx_637_; lean_object* v_zetaDeltaFVarIds_638_; lean_object* v_postponed_639_; lean_object* v_diag_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_651_; 
v___x_635_ = lean_st_ref_set(v___y_616_, v___x_634_);
v___x_636_ = lean_st_ref_take(v___y_615_);
v_mctx_637_ = lean_ctor_get(v___x_636_, 0);
v_zetaDeltaFVarIds_638_ = lean_ctor_get(v___x_636_, 2);
v_postponed_639_ = lean_ctor_get(v___x_636_, 3);
v_diag_640_ = lean_ctor_get(v___x_636_, 4);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v___x_636_, 1);
lean_dec(v_unused_652_);
v___x_642_ = v___x_636_;
v_isShared_643_ = v_isSharedCheck_651_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_diag_640_);
lean_inc(v_postponed_639_);
lean_inc(v_zetaDeltaFVarIds_638_);
lean_inc(v_mctx_637_);
lean_dec(v___x_636_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_651_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_644_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v___x_644_);
v___x_646_ = v___x_642_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_mctx_637_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_zetaDeltaFVarIds_638_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v_postponed_639_);
lean_ctor_set(v_reuseFailAlloc_650_, 4, v_diag_640_);
v___x_646_ = v_reuseFailAlloc_650_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_st_ref_set(v___y_615_, v___x_646_);
v___x_648_ = lean_box(0);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___boxed(lean_object* v_mod_696_, lean_object* v_isMeta_697_, lean_object* v_hint_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
uint8_t v_isMeta_boxed_706_; lean_object* v_res_707_; 
v_isMeta_boxed_706_ = lean_unbox(v_isMeta_697_);
v_res_707_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0(v_mod_696_, v_isMeta_boxed_706_, v_hint_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1(lean_object* v___x_708_, lean_object* v_declName_709_, lean_object* v_as_710_, size_t v_sz_711_, size_t v_i_712_, lean_object* v_b_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
uint8_t v___x_721_; 
v___x_721_ = lean_usize_dec_lt(v_i_712_, v_sz_711_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
lean_dec(v_declName_709_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v_b_713_);
return v___x_722_;
}
else
{
lean_object* v___x_723_; lean_object* v_modules_724_; lean_object* v___x_725_; lean_object* v_a_726_; lean_object* v___x_727_; lean_object* v_toImport_728_; lean_object* v_module_729_; uint8_t v___x_730_; lean_object* v___x_731_; 
v___x_723_ = l_Lean_Environment_header(v___x_708_);
v_modules_724_ = lean_ctor_get(v___x_723_, 3);
lean_inc_ref(v_modules_724_);
lean_dec_ref(v___x_723_);
v___x_725_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_726_ = lean_array_uget_borrowed(v_as_710_, v_i_712_);
v___x_727_ = lean_array_get(v___x_725_, v_modules_724_, v_a_726_);
lean_dec_ref(v_modules_724_);
v_toImport_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc_ref(v_toImport_728_);
lean_dec(v___x_727_);
v_module_729_ = lean_ctor_get(v_toImport_728_, 0);
lean_inc(v_module_729_);
lean_dec_ref(v_toImport_728_);
v___x_730_ = 0;
lean_inc(v_declName_709_);
v___x_731_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0(v_module_729_, v___x_730_, v_declName_709_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v___x_732_; size_t v___x_733_; size_t v___x_734_; 
lean_dec_ref_known(v___x_731_, 1);
v___x_732_ = lean_box(0);
v___x_733_ = ((size_t)1ULL);
v___x_734_ = lean_usize_add(v_i_712_, v___x_733_);
v_i_712_ = v___x_734_;
v_b_713_ = v___x_732_;
goto _start;
}
else
{
lean_dec(v_declName_709_);
return v___x_731_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1___boxed(lean_object* v___x_736_, lean_object* v_declName_737_, lean_object* v_as_738_, lean_object* v_sz_739_, lean_object* v_i_740_, lean_object* v_b_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
size_t v_sz_boxed_749_; size_t v_i_boxed_750_; lean_object* v_res_751_; 
v_sz_boxed_749_ = lean_unbox_usize(v_sz_739_);
lean_dec(v_sz_739_);
v_i_boxed_750_ = lean_unbox_usize(v_i_740_);
lean_dec(v_i_740_);
v_res_751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1(v___x_736_, v_declName_737_, v_as_738_, v_sz_boxed_749_, v_i_boxed_750_, v_b_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec_ref(v_as_738_);
lean_dec_ref(v___x_736_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(lean_object* v_a_752_, lean_object* v_x_753_){
_start:
{
if (lean_obj_tag(v_x_753_) == 0)
{
lean_object* v___x_754_; 
v___x_754_ = lean_box(0);
return v___x_754_;
}
else
{
lean_object* v_key_755_; lean_object* v_value_756_; lean_object* v_tail_757_; uint8_t v___x_758_; 
v_key_755_ = lean_ctor_get(v_x_753_, 0);
v_value_756_ = lean_ctor_get(v_x_753_, 1);
v_tail_757_ = lean_ctor_get(v_x_753_, 2);
v___x_758_ = lean_name_eq(v_key_755_, v_a_752_);
if (v___x_758_ == 0)
{
v_x_753_ = v_tail_757_;
goto _start;
}
else
{
lean_object* v___x_760_; 
lean_inc(v_value_756_);
v___x_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_760_, 0, v_value_756_);
return v___x_760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_761_, lean_object* v_x_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(v_a_761_, v_x_762_);
lean_dec(v_x_762_);
lean_dec(v_a_761_);
return v_res_763_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_764_; uint64_t v___x_765_; 
v___x_764_ = lean_unsigned_to_nat(1723u);
v___x_765_ = lean_uint64_of_nat(v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg(lean_object* v_m_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_buckets_768_; lean_object* v___x_769_; uint64_t v___y_771_; 
v_buckets_768_ = lean_ctor_get(v_m_766_, 1);
v___x_769_ = lean_array_get_size(v_buckets_768_);
if (lean_obj_tag(v_a_767_) == 0)
{
uint64_t v___x_785_; 
v___x_785_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___closed__0);
v___y_771_ = v___x_785_;
goto v___jp_770_;
}
else
{
uint64_t v_hash_786_; 
v_hash_786_ = lean_ctor_get_uint64(v_a_767_, sizeof(void*)*2);
v___y_771_ = v_hash_786_;
goto v___jp_770_;
}
v___jp_770_:
{
uint64_t v___x_772_; uint64_t v___x_773_; uint64_t v_fold_774_; uint64_t v___x_775_; uint64_t v___x_776_; uint64_t v___x_777_; size_t v___x_778_; size_t v___x_779_; size_t v___x_780_; size_t v___x_781_; size_t v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_772_ = 32ULL;
v___x_773_ = lean_uint64_shift_right(v___y_771_, v___x_772_);
v_fold_774_ = lean_uint64_xor(v___y_771_, v___x_773_);
v___x_775_ = 16ULL;
v___x_776_ = lean_uint64_shift_right(v_fold_774_, v___x_775_);
v___x_777_ = lean_uint64_xor(v_fold_774_, v___x_776_);
v___x_778_ = lean_uint64_to_usize(v___x_777_);
v___x_779_ = lean_usize_of_nat(v___x_769_);
v___x_780_ = ((size_t)1ULL);
v___x_781_ = lean_usize_sub(v___x_779_, v___x_780_);
v___x_782_ = lean_usize_land(v___x_778_, v___x_781_);
v___x_783_ = lean_array_uget_borrowed(v_buckets_768_, v___x_782_);
v___x_784_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(v_a_767_, v___x_783_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___boxed(lean_object* v_m_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg(v_m_787_, v_a_788_);
lean_dec(v_a_788_);
lean_dec_ref(v_m_787_);
return v_res_789_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_792_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__1));
v___x_793_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__0));
v___x_794_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_793_, v___x_792_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0(lean_object* v_declName_797_, uint8_t v_isMeta_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; lean_object* v_env_810_; lean_object* v___y_812_; lean_object* v___x_825_; 
v___x_806_ = lean_st_ref_get(v___y_804_);
v_env_810_ = lean_ctor_get(v___x_806_, 0);
lean_inc_ref(v_env_810_);
lean_dec(v___x_806_);
v___x_825_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_810_, v_declName_797_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_dec_ref(v_env_810_);
lean_dec(v_declName_797_);
goto v___jp_807_;
}
else
{
lean_object* v_val_826_; lean_object* v___x_827_; lean_object* v_modules_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v_val_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v___x_825_, 1);
v___x_827_ = l_Lean_Environment_header(v_env_810_);
v_modules_828_ = lean_ctor_get(v___x_827_, 3);
lean_inc_ref(v_modules_828_);
lean_dec_ref(v___x_827_);
v___x_829_ = lean_array_get_size(v_modules_828_);
v___x_830_ = lean_nat_dec_lt(v_val_826_, v___x_829_);
if (v___x_830_ == 0)
{
lean_dec_ref(v_modules_828_);
lean_dec(v_val_826_);
lean_dec_ref(v_env_810_);
lean_dec(v_declName_797_);
goto v___jp_807_;
}
else
{
lean_object* v___x_831_; lean_object* v_env_832_; lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___y_836_; 
v___x_831_ = lean_st_ref_get(v___y_804_);
v_env_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc_ref(v_env_832_);
lean_dec(v___x_831_);
v___x_833_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2);
v___x_834_ = lean_array_fget(v_modules_828_, v_val_826_);
lean_dec(v_val_826_);
lean_dec_ref(v_modules_828_);
if (v_isMeta_798_ == 0)
{
lean_dec_ref(v_env_832_);
v___y_836_ = v_isMeta_798_;
goto v___jp_835_;
}
else
{
uint8_t v___x_847_; 
lean_inc(v_declName_797_);
v___x_847_ = l_Lean_isMarkedMeta(v_env_832_, v_declName_797_);
if (v___x_847_ == 0)
{
v___y_836_ = v_isMeta_798_;
goto v___jp_835_;
}
else
{
uint8_t v___x_848_; 
v___x_848_ = 0;
v___y_836_ = v___x_848_;
goto v___jp_835_;
}
}
v___jp_835_:
{
lean_object* v_toImport_837_; lean_object* v_module_838_; lean_object* v___x_839_; 
v_toImport_837_ = lean_ctor_get(v___x_834_, 0);
lean_inc_ref(v_toImport_837_);
lean_dec(v___x_834_);
v_module_838_ = lean_ctor_get(v_toImport_837_, 0);
lean_inc(v_module_838_);
lean_dec_ref(v_toImport_837_);
lean_inc(v_declName_797_);
v___x_839_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0(v_module_838_, v___y_836_, v_declName_797_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
lean_dec_ref_known(v___x_839_, 1);
v___x_840_ = l_Lean_indirectModUseExt;
v___x_841_ = lean_box(1);
v___x_842_ = lean_box(0);
lean_inc_ref(v_env_810_);
v___x_843_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_833_, v___x_840_, v_env_810_, v___x_841_, v___x_842_);
v___x_844_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg(v___x_843_, v_declName_797_);
lean_dec(v___x_843_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v___x_845_; 
v___x_845_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__3));
v___y_812_ = v___x_845_;
goto v___jp_811_;
}
else
{
lean_object* v_val_846_; 
v_val_846_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_val_846_);
lean_dec_ref_known(v___x_844_, 1);
v___y_812_ = v_val_846_;
goto v___jp_811_;
}
}
else
{
lean_dec_ref(v_env_810_);
lean_dec(v_declName_797_);
return v___x_839_;
}
}
}
}
v___jp_807_:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_box(0);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
return v___x_809_;
}
v___jp_811_:
{
lean_object* v___x_813_; size_t v_sz_814_; size_t v___x_815_; lean_object* v___x_816_; 
v___x_813_ = lean_box(0);
v_sz_814_ = lean_array_size(v___y_812_);
v___x_815_ = ((size_t)0ULL);
v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1(v_env_810_, v_declName_797_, v___y_812_, v_sz_814_, v___x_815_, v___x_813_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec_ref(v___y_812_);
lean_dec_ref(v_env_810_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v___x_816_, 0);
lean_dec(v_unused_824_);
v___x_818_ = v___x_816_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_dec(v___x_816_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_813_);
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_813_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
else
{
return v___x_816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___boxed(lean_object* v_declName_849_, lean_object* v_isMeta_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
uint8_t v_isMeta_boxed_858_; lean_object* v_res_859_; 
v_isMeta_boxed_858_ = lean_unbox(v_isMeta_850_);
v_res_859_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0(v_declName_849_, v_isMeta_boxed_858_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0(lean_object* v___x_860_, lean_object* v___x_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_860_, v___x_861_, v___y_866_, v___y_867_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; uint8_t v___x_871_; lean_object* v___x_872_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc_n(v_a_870_, 2);
lean_dec_ref_known(v___x_869_, 1);
v___x_871_ = 0;
v___x_872_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0(v_a_870_, v___x_871_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_879_ == 0)
{
lean_object* v_unused_880_; 
v_unused_880_ = lean_ctor_get(v___x_872_, 0);
lean_dec(v_unused_880_);
v___x_874_ = v___x_872_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_dec(v___x_872_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v_a_870_);
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_870_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec(v_a_870_);
v_a_881_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_872_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_872_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0___boxed(lean_object* v___x_889_, lean_object* v___x_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0(v___x_889_, v___x_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0(lean_object* v___y_899_, uint8_t v_isExporting_900_, lean_object* v___x_901_, lean_object* v___y_902_, lean_object* v___x_903_, lean_object* v_a_x3f_904_){
_start:
{
lean_object* v___x_906_; lean_object* v_env_907_; lean_object* v_nextMacroScope_908_; lean_object* v_ngen_909_; lean_object* v_auxDeclNGen_910_; lean_object* v_traceState_911_; lean_object* v_messages_912_; lean_object* v_infoState_913_; lean_object* v_snapshotTasks_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_939_; 
v___x_906_ = lean_st_ref_take(v___y_899_);
v_env_907_ = lean_ctor_get(v___x_906_, 0);
v_nextMacroScope_908_ = lean_ctor_get(v___x_906_, 1);
v_ngen_909_ = lean_ctor_get(v___x_906_, 2);
v_auxDeclNGen_910_ = lean_ctor_get(v___x_906_, 3);
v_traceState_911_ = lean_ctor_get(v___x_906_, 4);
v_messages_912_ = lean_ctor_get(v___x_906_, 6);
v_infoState_913_ = lean_ctor_get(v___x_906_, 7);
v_snapshotTasks_914_ = lean_ctor_get(v___x_906_, 8);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; 
v_unused_940_ = lean_ctor_get(v___x_906_, 5);
lean_dec(v_unused_940_);
v___x_916_ = v___x_906_;
v_isShared_917_ = v_isSharedCheck_939_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_snapshotTasks_914_);
lean_inc(v_infoState_913_);
lean_inc(v_messages_912_);
lean_inc(v_traceState_911_);
lean_inc(v_auxDeclNGen_910_);
lean_inc(v_ngen_909_);
lean_inc(v_nextMacroScope_908_);
lean_inc(v_env_907_);
lean_dec(v___x_906_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_939_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_918_ = l_Lean_Environment_setExporting(v_env_907_, v_isExporting_900_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 5, v___x_901_);
lean_ctor_set(v___x_916_, 0, v___x_918_);
v___x_920_ = v___x_916_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_nextMacroScope_908_);
lean_ctor_set(v_reuseFailAlloc_938_, 2, v_ngen_909_);
lean_ctor_set(v_reuseFailAlloc_938_, 3, v_auxDeclNGen_910_);
lean_ctor_set(v_reuseFailAlloc_938_, 4, v_traceState_911_);
lean_ctor_set(v_reuseFailAlloc_938_, 5, v___x_901_);
lean_ctor_set(v_reuseFailAlloc_938_, 6, v_messages_912_);
lean_ctor_set(v_reuseFailAlloc_938_, 7, v_infoState_913_);
lean_ctor_set(v_reuseFailAlloc_938_, 8, v_snapshotTasks_914_);
v___x_920_ = v_reuseFailAlloc_938_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v_mctx_923_; lean_object* v_zetaDeltaFVarIds_924_; lean_object* v_postponed_925_; lean_object* v_diag_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_936_; 
v___x_921_ = lean_st_ref_set(v___y_899_, v___x_920_);
v___x_922_ = lean_st_ref_take(v___y_902_);
v_mctx_923_ = lean_ctor_get(v___x_922_, 0);
v_zetaDeltaFVarIds_924_ = lean_ctor_get(v___x_922_, 2);
v_postponed_925_ = lean_ctor_get(v___x_922_, 3);
v_diag_926_ = lean_ctor_get(v___x_922_, 4);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; 
v_unused_937_ = lean_ctor_get(v___x_922_, 1);
lean_dec(v_unused_937_);
v___x_928_ = v___x_922_;
v_isShared_929_ = v_isSharedCheck_936_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_diag_926_);
lean_inc(v_postponed_925_);
lean_inc(v_zetaDeltaFVarIds_924_);
lean_inc(v_mctx_923_);
lean_dec(v___x_922_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_936_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 1, v___x_903_);
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_mctx_923_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_zetaDeltaFVarIds_924_);
lean_ctor_set(v_reuseFailAlloc_935_, 3, v_postponed_925_);
lean_ctor_set(v_reuseFailAlloc_935_, 4, v_diag_926_);
v___x_931_ = v_reuseFailAlloc_935_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = lean_st_ref_set(v___y_902_, v___x_931_);
v___x_933_ = lean_box(0);
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
return v___x_934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v___y_941_, lean_object* v_isExporting_942_, lean_object* v___x_943_, lean_object* v___y_944_, lean_object* v___x_945_, lean_object* v_a_x3f_946_, lean_object* v___y_947_){
_start:
{
uint8_t v_isExporting_boxed_948_; lean_object* v_res_949_; 
v_isExporting_boxed_948_ = lean_unbox(v_isExporting_942_);
v_res_949_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0(v___y_941_, v_isExporting_boxed_948_, v___x_943_, v___y_944_, v___x_945_, v_a_x3f_946_);
lean_dec(v_a_x3f_946_);
lean_dec(v___y_944_);
lean_dec(v___y_941_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg(lean_object* v_x_950_, uint8_t v_isExporting_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; lean_object* v_env_960_; uint8_t v_isExporting_961_; lean_object* v___x_962_; lean_object* v_env_963_; lean_object* v_nextMacroScope_964_; lean_object* v_ngen_965_; lean_object* v_auxDeclNGen_966_; lean_object* v_traceState_967_; lean_object* v_messages_968_; lean_object* v_infoState_969_; lean_object* v_snapshotTasks_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_1024_; 
v___x_959_ = lean_st_ref_get(v___y_957_);
v_env_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc_ref(v_env_960_);
lean_dec(v___x_959_);
v_isExporting_961_ = lean_ctor_get_uint8(v_env_960_, sizeof(void*)*8);
lean_dec_ref(v_env_960_);
v___x_962_ = lean_st_ref_take(v___y_957_);
v_env_963_ = lean_ctor_get(v___x_962_, 0);
v_nextMacroScope_964_ = lean_ctor_get(v___x_962_, 1);
v_ngen_965_ = lean_ctor_get(v___x_962_, 2);
v_auxDeclNGen_966_ = lean_ctor_get(v___x_962_, 3);
v_traceState_967_ = lean_ctor_get(v___x_962_, 4);
v_messages_968_ = lean_ctor_get(v___x_962_, 6);
v_infoState_969_ = lean_ctor_get(v___x_962_, 7);
v_snapshotTasks_970_ = lean_ctor_get(v___x_962_, 8);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; 
v_unused_1025_ = lean_ctor_get(v___x_962_, 5);
lean_dec(v_unused_1025_);
v___x_972_ = v___x_962_;
v_isShared_973_ = v_isSharedCheck_1024_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_snapshotTasks_970_);
lean_inc(v_infoState_969_);
lean_inc(v_messages_968_);
lean_inc(v_traceState_967_);
lean_inc(v_auxDeclNGen_966_);
lean_inc(v_ngen_965_);
lean_inc(v_nextMacroScope_964_);
lean_inc(v_env_963_);
lean_dec(v___x_962_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_1024_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_974_ = l_Lean_Environment_setExporting(v_env_963_, v_isExporting_951_);
v___x_975_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 5, v___x_975_);
lean_ctor_set(v___x_972_, 0, v___x_974_);
v___x_977_ = v___x_972_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_nextMacroScope_964_);
lean_ctor_set(v_reuseFailAlloc_1023_, 2, v_ngen_965_);
lean_ctor_set(v_reuseFailAlloc_1023_, 3, v_auxDeclNGen_966_);
lean_ctor_set(v_reuseFailAlloc_1023_, 4, v_traceState_967_);
lean_ctor_set(v_reuseFailAlloc_1023_, 5, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_1023_, 6, v_messages_968_);
lean_ctor_set(v_reuseFailAlloc_1023_, 7, v_infoState_969_);
lean_ctor_set(v_reuseFailAlloc_1023_, 8, v_snapshotTasks_970_);
v___x_977_ = v_reuseFailAlloc_1023_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v_mctx_980_; lean_object* v_zetaDeltaFVarIds_981_; lean_object* v_postponed_982_; lean_object* v_diag_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1021_; 
v___x_978_ = lean_st_ref_set(v___y_957_, v___x_977_);
v___x_979_ = lean_st_ref_take(v___y_955_);
v_mctx_980_ = lean_ctor_get(v___x_979_, 0);
v_zetaDeltaFVarIds_981_ = lean_ctor_get(v___x_979_, 2);
v_postponed_982_ = lean_ctor_get(v___x_979_, 3);
v_diag_983_ = lean_ctor_get(v___x_979_, 4);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v___x_979_, 1);
lean_dec(v_unused_1022_);
v___x_985_ = v___x_979_;
v_isShared_986_ = v_isSharedCheck_1021_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_diag_983_);
lean_inc(v_postponed_982_);
lean_inc(v_zetaDeltaFVarIds_981_);
lean_inc(v_mctx_980_);
lean_dec(v___x_979_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1021_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_987_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 1, v___x_987_);
v___x_989_ = v___x_985_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_mctx_980_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_zetaDeltaFVarIds_981_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v_postponed_982_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v_diag_983_);
v___x_989_ = v_reuseFailAlloc_1020_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_990_; lean_object* v_r_991_; 
v___x_990_ = lean_st_ref_set(v___y_955_, v___x_989_);
lean_inc(v___y_957_);
lean_inc_ref(v___y_956_);
lean_inc(v___y_955_);
lean_inc_ref(v___y_954_);
lean_inc(v___y_953_);
lean_inc_ref(v___y_952_);
v_r_991_ = lean_apply_7(v_x_950_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, lean_box(0));
if (lean_obj_tag(v_r_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1008_; 
v_a_992_ = lean_ctor_get(v_r_991_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_r_991_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_994_ = v_r_991_;
v_isShared_995_ = v_isSharedCheck_1008_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v_r_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1008_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
lean_inc(v_a_992_);
if (v_isShared_995_ == 0)
{
lean_ctor_set_tag(v___x_994_, 1);
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_1007_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
v___x_998_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0(v___y_957_, v_isExporting_961_, v___x_975_, v___y_955_, v___x_987_, v___x_997_);
lean_dec_ref(v___x_997_);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1005_ == 0)
{
lean_object* v_unused_1006_; 
v_unused_1006_ = lean_ctor_get(v___x_998_, 0);
lean_dec(v_unused_1006_);
v___x_1000_ = v___x_998_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_dec(v___x_998_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v_a_992_);
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_992_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
v_a_1009_ = lean_ctor_get(v_r_991_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v_r_991_, 1);
v___x_1010_ = lean_box(0);
v___x_1011_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0(v___y_957_, v_isExporting_961_, v___x_975_, v___y_955_, v___x_987_, v___x_1010_);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; 
v_unused_1019_ = lean_ctor_get(v___x_1011_, 0);
lean_dec(v_unused_1019_);
v___x_1013_ = v___x_1011_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_dec(v___x_1011_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set_tag(v___x_1013_, 1);
lean_ctor_set(v___x_1013_, 0, v_a_1009_);
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1009_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___boxed(lean_object* v_x_1026_, lean_object* v_isExporting_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
uint8_t v_isExporting_boxed_1035_; lean_object* v_res_1036_; 
v_isExporting_boxed_1035_ = lean_unbox(v_isExporting_1027_);
v_res_1036_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg(v_x_1026_, v_isExporting_boxed_1035_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg(lean_object* v_x_1037_, uint8_t v_when_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
if (v_when_1038_ == 0)
{
lean_object* v___x_1046_; 
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
lean_inc(v___y_1042_);
lean_inc_ref(v___y_1041_);
lean_inc(v___y_1040_);
lean_inc_ref(v___y_1039_);
v___x_1046_ = lean_apply_7(v_x_1037_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, lean_box(0));
return v___x_1046_;
}
else
{
uint8_t v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = 0;
v___x_1048_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg(v_x_1037_, v___x_1047_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg___boxed(lean_object* v_x_1049_, lean_object* v_when_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
uint8_t v_when_boxed_1058_; lean_object* v_res_1059_; 
v_when_boxed_1058_ = lean_unbox(v_when_1050_);
v_res_1059_ = l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg(v_x_1049_, v_when_boxed_1058_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1(lean_object* v___x_1061_, lean_object* v___x_1062_, lean_object* v_____r_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1071_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12));
v___x_1072_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13));
v___x_1073_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___closed__0));
v___x_1074_ = l_Lean_Name_mkStr4(v___x_1061_, v___x_1071_, v___x_1072_, v___x_1073_);
lean_inc(v___x_1062_);
v___x_1075_ = l_Lean_Syntax_isOfKind(v___x_1062_, v___x_1074_);
lean_dec(v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; 
lean_dec(v___x_1062_);
v___x_1076_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
return v___x_1076_;
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___f_1080_; lean_object* v___x_1081_; 
v___x_1077_ = lean_unsigned_to_nat(2u);
v___x_1078_ = l_Lean_Syntax_getArg(v___x_1062_, v___x_1077_);
lean_dec(v___x_1062_);
v___x_1079_ = lean_box(0);
v___f_1080_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1080_, 0, v___x_1078_);
lean_closure_set(v___f_1080_, 1, v___x_1079_);
v___x_1081_ = l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg(v___f_1080_, v___x_1075_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1081_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___boxed(lean_object* v___x_1082_, lean_object* v___x_1083_, lean_object* v_____r_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1(v___x_1082_, v___x_1083_, v_____r_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
return v_res_1092_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = lean_box(0);
v___x_1098_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1));
v___x_1099_ = l_Lean_mkConst(v___x_1098_, v___x_1097_);
return v___x_1099_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2);
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx(lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v_fileName_1116_; lean_object* v_fileMap_1117_; lean_object* v_options_1118_; lean_object* v_currRecDepth_1119_; lean_object* v_maxRecDepth_1120_; lean_object* v_ref_1121_; lean_object* v_currNamespace_1122_; lean_object* v_openDecls_1123_; lean_object* v_initHeartbeats_1124_; lean_object* v_maxHeartbeats_1125_; lean_object* v_quotContext_1126_; lean_object* v_currMacroScope_1127_; uint8_t v_diag_1128_; lean_object* v_cancelTk_x3f_1129_; uint8_t v_suppressElabErrors_1130_; lean_object* v_inheritedTraceOptions_1131_; lean_object* v___x_1132_; lean_object* v_a_1134_; lean_object* v___y_1163_; lean_object* v___x_1173_; lean_object* v_ref_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v_fileName_1116_ = lean_ctor_get(v_a_1113_, 0);
v_fileMap_1117_ = lean_ctor_get(v_a_1113_, 1);
v_options_1118_ = lean_ctor_get(v_a_1113_, 2);
v_currRecDepth_1119_ = lean_ctor_get(v_a_1113_, 3);
v_maxRecDepth_1120_ = lean_ctor_get(v_a_1113_, 4);
v_ref_1121_ = lean_ctor_get(v_a_1113_, 5);
v_currNamespace_1122_ = lean_ctor_get(v_a_1113_, 6);
v_openDecls_1123_ = lean_ctor_get(v_a_1113_, 7);
v_initHeartbeats_1124_ = lean_ctor_get(v_a_1113_, 8);
v_maxHeartbeats_1125_ = lean_ctor_get(v_a_1113_, 9);
v_quotContext_1126_ = lean_ctor_get(v_a_1113_, 10);
v_currMacroScope_1127_ = lean_ctor_get(v_a_1113_, 11);
v_diag_1128_ = lean_ctor_get_uint8(v_a_1113_, sizeof(void*)*14);
v_cancelTk_x3f_1129_ = lean_ctor_get(v_a_1113_, 12);
v_suppressElabErrors_1130_ = lean_ctor_get_uint8(v_a_1113_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1131_ = lean_ctor_get(v_a_1113_, 13);
v___x_1132_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11));
lean_inc(v_a_1108_);
v___x_1173_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_a_1108_);
v_ref_1174_ = l_Lean_replaceRef(v_a_1108_, v_ref_1121_);
lean_inc_ref(v_inheritedTraceOptions_1131_);
lean_inc(v_cancelTk_x3f_1129_);
lean_inc(v_currMacroScope_1127_);
lean_inc(v_quotContext_1126_);
lean_inc(v_maxHeartbeats_1125_);
lean_inc(v_initHeartbeats_1124_);
lean_inc(v_openDecls_1123_);
lean_inc(v_currNamespace_1122_);
lean_inc(v_maxRecDepth_1120_);
lean_inc(v_currRecDepth_1119_);
lean_inc_ref(v_options_1118_);
lean_inc_ref(v_fileMap_1117_);
lean_inc_ref(v_fileName_1116_);
v___x_1175_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1175_, 0, v_fileName_1116_);
lean_ctor_set(v___x_1175_, 1, v_fileMap_1117_);
lean_ctor_set(v___x_1175_, 2, v_options_1118_);
lean_ctor_set(v___x_1175_, 3, v_currRecDepth_1119_);
lean_ctor_set(v___x_1175_, 4, v_maxRecDepth_1120_);
lean_ctor_set(v___x_1175_, 5, v_ref_1174_);
lean_ctor_set(v___x_1175_, 6, v_currNamespace_1122_);
lean_ctor_set(v___x_1175_, 7, v_openDecls_1123_);
lean_ctor_set(v___x_1175_, 8, v_initHeartbeats_1124_);
lean_ctor_set(v___x_1175_, 9, v_maxHeartbeats_1125_);
lean_ctor_set(v___x_1175_, 10, v_quotContext_1126_);
lean_ctor_set(v___x_1175_, 11, v_currMacroScope_1127_);
lean_ctor_set(v___x_1175_, 12, v_cancelTk_x3f_1129_);
lean_ctor_set(v___x_1175_, 13, v_inheritedTraceOptions_1131_);
lean_ctor_set_uint8(v___x_1175_, sizeof(void*)*14, v_diag_1128_);
lean_ctor_set_uint8(v___x_1175_, sizeof(void*)*14 + 1, v_suppressElabErrors_1130_);
v___x_1176_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5));
lean_inc(v___x_1173_);
v___x_1177_ = l_Lean_Syntax_isOfKind(v___x_1173_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = lean_box(0);
v___x_1179_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1(v___x_1132_, v___x_1173_, v___x_1178_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v___x_1175_, v_a_1114_);
lean_dec_ref_known(v___x_1175_, 14);
v___y_1163_ = v___x_1179_;
goto v___jp_1162_;
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1180_ = lean_unsigned_to_nat(0u);
v___x_1181_ = l_Lean_Syntax_getArg(v___x_1173_, v___x_1180_);
v___x_1182_ = l_Lean_Syntax_isNameLit_x3f(v___x_1181_);
lean_dec(v___x_1181_);
if (lean_obj_tag(v___x_1182_) == 1)
{
lean_object* v_val_1183_; 
lean_dec_ref_known(v___x_1175_, 14);
lean_dec(v___x_1173_);
v_val_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_val_1183_);
lean_dec_ref_known(v___x_1182_, 1);
v_a_1134_ = v_val_1183_;
goto v___jp_1133_;
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec(v___x_1182_);
v___x_1184_ = lean_box(0);
v___x_1185_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1(v___x_1132_, v___x_1173_, v___x_1184_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v___x_1175_, v_a_1114_);
lean_dec_ref_known(v___x_1175_, 14);
v___y_1163_ = v___x_1185_;
goto v___jp_1162_;
}
}
v___jp_1133_:
{
lean_object* v___x_1135_; lean_object* v_infoState_1136_; uint8_t v_enabled_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1135_ = lean_st_ref_get(v_a_1114_);
v_infoState_1136_ = lean_ctor_get(v___x_1135_, 7);
lean_inc_ref(v_infoState_1136_);
lean_dec(v___x_1135_);
v_enabled_1137_ = lean_ctor_get_uint8(v_infoState_1136_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1136_);
lean_inc(v_a_1134_);
v___x_1138_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_1134_);
lean_inc_ref(v___x_1138_);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_a_1134_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
if (v_enabled_1137_ == 0)
{
lean_object* v___x_1140_; 
lean_dec_ref(v___x_1138_);
lean_dec(v_a_1108_);
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; 
v___x_1141_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3);
v___x_1142_ = lean_box(0);
v___x_1143_ = lean_box(0);
v___x_1144_ = 0;
v___x_1145_ = l_Lean_Elab_Term_addTermInfo_x27(v_a_1108_, v___x_1138_, v___x_1141_, v___x_1142_, v___x_1143_, v___x_1144_, v___x_1144_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1152_ == 0)
{
lean_object* v_unused_1153_; 
v_unused_1153_ = lean_ctor_get(v___x_1145_, 0);
lean_dec(v_unused_1153_);
v___x_1147_ = v___x_1145_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_dec(v___x_1145_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1139_);
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1139_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec_ref_known(v___x_1139_, 2);
v_a_1154_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1145_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1145_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
v___jp_1162_:
{
if (lean_obj_tag(v___y_1163_) == 0)
{
lean_object* v_a_1164_; 
v_a_1164_ = lean_ctor_get(v___y_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref_known(v___y_1163_, 1);
v_a_1134_ = v_a_1164_;
goto v___jp_1133_;
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec(v_a_1108_);
v_a_1165_ = lean_ctor_get(v___y_1163_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___y_1163_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___y_1163_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___y_1163_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___boxed(lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx(v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4(lean_object* v_00_u03b1_1195_, lean_object* v_x_1196_, uint8_t v_isExporting_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg(v_x_1196_, v_isExporting_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1206_, lean_object* v_x_1207_, lean_object* v_isExporting_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
uint8_t v_isExporting_boxed_1216_; lean_object* v_res_1217_; 
v_isExporting_boxed_1216_ = lean_unbox(v_isExporting_1208_);
v_res_1217_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4(v_00_u03b1_1206_, v_x_1207_, v_isExporting_boxed_1216_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1(lean_object* v_00_u03b1_1218_, lean_object* v_x_1219_, uint8_t v_when_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg(v_x_1219_, v_when_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___boxed(lean_object* v_00_u03b1_1229_, lean_object* v_x_1230_, lean_object* v_when_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
uint8_t v_when_boxed_1239_; lean_object* v_res_1240_; 
v_when_boxed_1239_ = lean_unbox(v_when_1231_);
v_res_1240_ = l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1(v_00_u03b1_1229_, v_x_1230_, v_when_boxed_1239_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2(lean_object* v_00_u03b2_1241_, lean_object* v_m_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg(v_m_1242_, v_a_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1245_, lean_object* v_m_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2(v_00_u03b2_1245_, v_m_1246_, v_a_1247_);
lean_dec(v_a_1247_);
lean_dec_ref(v_m_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1249_, lean_object* v_x_1250_, lean_object* v_x_1251_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg(v_x_1250_, v_x_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1253_, lean_object* v_x_1254_, lean_object* v_x_1255_){
_start:
{
uint8_t v_res_1256_; lean_object* v_r_1257_; 
v_res_1256_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1(v_00_u03b2_1253_, v_x_1254_, v_x_1255_);
lean_dec_ref(v_x_1255_);
lean_dec_ref(v_x_1254_);
v_r_1257_ = lean_box(v_res_1256_);
return v_r_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2(lean_object* v_cls_1258_, lean_object* v_msg_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg(v_cls_1258_, v_msg_1259_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1268_, lean_object* v_msg_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2(v_cls_1268_, v_msg_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1278_, lean_object* v_a_1279_, lean_object* v_x_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(v_a_1279_, v_x_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1282_, lean_object* v_a_1283_, lean_object* v_x_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5(v_00_u03b2_1282_, v_a_1283_, v_x_1284_);
lean_dec(v_x_1284_);
lean_dec(v_a_1283_);
return v_res_1285_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1286_, lean_object* v_x_1287_, size_t v_x_1288_, lean_object* v_x_1289_){
_start:
{
uint8_t v___x_1290_; 
v___x_1290_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg(v_x_1287_, v_x_1288_, v_x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_, lean_object* v_x_1294_){
_start:
{
size_t v_x_11525__boxed_1295_; uint8_t v_res_1296_; lean_object* v_r_1297_; 
v_x_11525__boxed_1295_ = lean_unbox_usize(v_x_1293_);
lean_dec(v_x_1293_);
v_res_1296_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_1291_, v_x_1292_, v_x_11525__boxed_1295_, v_x_1294_);
lean_dec_ref(v_x_1294_);
lean_dec_ref(v_x_1292_);
v_r_1297_ = lean_box(v_res_1296_);
return v_r_1297_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_1298_, lean_object* v_keys_1299_, lean_object* v_vals_1300_, lean_object* v_heq_1301_, lean_object* v_i_1302_, lean_object* v_k_1303_){
_start:
{
uint8_t v___x_1304_; 
v___x_1304_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_keys_1299_, v_i_1302_, v_k_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1305_, lean_object* v_keys_1306_, lean_object* v_vals_1307_, lean_object* v_heq_1308_, lean_object* v_i_1309_, lean_object* v_k_1310_){
_start:
{
uint8_t v_res_1311_; lean_object* v_r_1312_; 
v_res_1311_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7(v_00_u03b2_1305_, v_keys_1306_, v_vals_1307_, v_heq_1308_, v_i_1309_, v_k_1310_);
lean_dec_ref(v_k_1310_);
lean_dec_ref(v_vals_1307_);
lean_dec_ref(v_keys_1306_);
v_r_1312_ = lean_box(v_res_1311_);
return v_r_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(lean_object* v_ev_1314_, lean_object* v___x_1315_, lean_object* v___x_1316_, lean_object* v_typeExpr_1317_, lean_object* v_stx_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_1326_; 
lean_inc(v___y_1324_);
lean_inc_ref(v___y_1323_);
lean_inc(v___y_1322_);
lean_inc_ref(v___y_1321_);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
v___x_1326_ = lean_apply_8(v_ev_1314_, v_stx_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, lean_box(0));
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1348_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1348_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1348_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v_fst_1331_; lean_object* v_snd_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1347_; 
v_fst_1331_ = lean_ctor_get(v_a_1327_, 0);
v_snd_1332_ = lean_ctor_get(v_a_1327_, 1);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_a_1327_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1334_ = v_a_1327_;
v_isShared_1335_ = v_isSharedCheck_1347_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_snd_1332_);
lean_inc(v_fst_1331_);
lean_dec(v_a_1327_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1347_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1336_, 0, v_fst_1331_);
v___x_1337_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0));
v___x_1338_ = l_Lean_Name_mkStr2(v___x_1315_, v___x_1337_);
v___x_1339_ = l_Lean_Expr_const___override(v___x_1338_, v___x_1316_);
v___x_1340_ = l_Lean_mkAppB(v___x_1339_, v_typeExpr_1317_, v_snd_1332_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 1, v___x_1340_);
lean_ctor_set(v___x_1334_, 0, v___x_1336_);
v___x_1342_ = v___x_1334_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1344_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1342_);
v___x_1344_ = v___x_1329_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec_ref(v_typeExpr_1317_);
lean_dec(v___x_1316_);
lean_dec_ref(v___x_1315_);
v_a_1349_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1326_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1326_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___boxed(lean_object* v_ev_1357_, lean_object* v___x_1358_, lean_object* v___x_1359_, lean_object* v_typeExpr_1360_, lean_object* v_stx_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1357_, v___x_1358_, v___x_1359_, v_typeExpr_1360_, v_stx_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1369_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1373_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1374_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__1));
v___x_1375_ = l_Lean_Expr_const___override(v___x_1374_, v___x_1373_);
return v___x_1375_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1391_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8));
v___x_1392_ = l_Lean_Expr_const___override(v___x_1391_, v___x_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(lean_object* v_typeExpr_1393_, lean_object* v_ev_1394_, lean_object* v_stx_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v_a_1410_; lean_object* v_snd_1411_; lean_object* v___y_1437_; lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v___x_1403_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0));
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1406_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2);
lean_inc_ref(v_typeExpr_1393_);
v___x_1407_ = l_Lean_Expr_app___override(v___x_1406_, v_typeExpr_1393_);
v___x_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
lean_inc(v_stx_1395_);
v___x_1440_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_1395_);
v___x_1441_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__4));
v___x_1442_ = l_Lean_Syntax_matchesIdent(v___x_1440_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v_fileName_1443_; lean_object* v_fileMap_1444_; lean_object* v_options_1445_; lean_object* v_currRecDepth_1446_; lean_object* v_maxRecDepth_1447_; lean_object* v_ref_1448_; lean_object* v_currNamespace_1449_; lean_object* v_openDecls_1450_; lean_object* v_initHeartbeats_1451_; lean_object* v_maxHeartbeats_1452_; lean_object* v_quotContext_1453_; lean_object* v_currMacroScope_1454_; uint8_t v_diag_1455_; lean_object* v_cancelTk_x3f_1456_; uint8_t v_suppressElabErrors_1457_; lean_object* v_inheritedTraceOptions_1458_; lean_object* v_ref_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v_fileName_1443_ = lean_ctor_get(v_a_1400_, 0);
v_fileMap_1444_ = lean_ctor_get(v_a_1400_, 1);
v_options_1445_ = lean_ctor_get(v_a_1400_, 2);
v_currRecDepth_1446_ = lean_ctor_get(v_a_1400_, 3);
v_maxRecDepth_1447_ = lean_ctor_get(v_a_1400_, 4);
v_ref_1448_ = lean_ctor_get(v_a_1400_, 5);
v_currNamespace_1449_ = lean_ctor_get(v_a_1400_, 6);
v_openDecls_1450_ = lean_ctor_get(v_a_1400_, 7);
v_initHeartbeats_1451_ = lean_ctor_get(v_a_1400_, 8);
v_maxHeartbeats_1452_ = lean_ctor_get(v_a_1400_, 9);
v_quotContext_1453_ = lean_ctor_get(v_a_1400_, 10);
v_currMacroScope_1454_ = lean_ctor_get(v_a_1400_, 11);
v_diag_1455_ = lean_ctor_get_uint8(v_a_1400_, sizeof(void*)*14);
v_cancelTk_x3f_1456_ = lean_ctor_get(v_a_1400_, 12);
v_suppressElabErrors_1457_ = lean_ctor_get_uint8(v_a_1400_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1458_ = lean_ctor_get(v_a_1400_, 13);
v_ref_1459_ = l_Lean_replaceRef(v_stx_1395_, v_ref_1448_);
lean_inc_ref(v_inheritedTraceOptions_1458_);
lean_inc(v_cancelTk_x3f_1456_);
lean_inc(v_currMacroScope_1454_);
lean_inc(v_quotContext_1453_);
lean_inc(v_maxHeartbeats_1452_);
lean_inc(v_initHeartbeats_1451_);
lean_inc(v_openDecls_1450_);
lean_inc(v_currNamespace_1449_);
lean_inc(v_maxRecDepth_1447_);
lean_inc(v_currRecDepth_1446_);
lean_inc_ref(v_options_1445_);
lean_inc_ref(v_fileMap_1444_);
lean_inc_ref(v_fileName_1443_);
v___x_1460_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1460_, 0, v_fileName_1443_);
lean_ctor_set(v___x_1460_, 1, v_fileMap_1444_);
lean_ctor_set(v___x_1460_, 2, v_options_1445_);
lean_ctor_set(v___x_1460_, 3, v_currRecDepth_1446_);
lean_ctor_set(v___x_1460_, 4, v_maxRecDepth_1447_);
lean_ctor_set(v___x_1460_, 5, v_ref_1459_);
lean_ctor_set(v___x_1460_, 6, v_currNamespace_1449_);
lean_ctor_set(v___x_1460_, 7, v_openDecls_1450_);
lean_ctor_set(v___x_1460_, 8, v_initHeartbeats_1451_);
lean_ctor_set(v___x_1460_, 9, v_maxHeartbeats_1452_);
lean_ctor_set(v___x_1460_, 10, v_quotContext_1453_);
lean_ctor_set(v___x_1460_, 11, v_currMacroScope_1454_);
lean_ctor_set(v___x_1460_, 12, v_cancelTk_x3f_1456_);
lean_ctor_set(v___x_1460_, 13, v_inheritedTraceOptions_1458_);
lean_ctor_set_uint8(v___x_1460_, sizeof(void*)*14, v_diag_1455_);
lean_ctor_set_uint8(v___x_1460_, sizeof(void*)*14 + 1, v_suppressElabErrors_1457_);
v___x_1461_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15));
lean_inc(v___x_1440_);
v___x_1462_ = l_Lean_Syntax_isOfKind(v___x_1440_, v___x_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1463_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6));
lean_inc(v___x_1440_);
v___x_1464_ = l_Lean_Syntax_isOfKind(v___x_1440_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1394_, v___x_1403_, v___x_1405_, v_typeExpr_1393_, v___x_1440_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v___x_1460_, v_a_1401_);
lean_dec_ref_known(v___x_1460_, 14);
v___y_1437_ = v___x_1465_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1466_ = l_Lean_Syntax_getArg(v___x_1440_, v___x_1404_);
v___x_1467_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__7));
v___x_1468_ = l_Lean_Syntax_matchesIdent(v___x_1466_, v___x_1467_);
if (v___x_1468_ == 0)
{
uint8_t v___x_1469_; 
lean_inc(v___x_1466_);
v___x_1469_ = l_Lean_Syntax_isOfKind(v___x_1466_, v___x_1461_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; 
lean_dec(v___x_1466_);
v___x_1470_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1394_, v___x_1403_, v___x_1405_, v_typeExpr_1393_, v___x_1440_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v___x_1460_, v_a_1401_);
lean_dec_ref_known(v___x_1460_, 14);
v___y_1437_ = v___x_1470_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v___x_1471_ = lean_unsigned_to_nat(1u);
v___x_1472_ = l_Lean_Syntax_getArg(v___x_1466_, v___x_1471_);
lean_dec(v___x_1466_);
v___x_1473_ = l_Lean_Syntax_matchesIdent(v___x_1472_, v___x_1467_);
lean_dec(v___x_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1394_, v___x_1403_, v___x_1405_, v_typeExpr_1393_, v___x_1440_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v___x_1460_, v_a_1401_);
lean_dec_ref_known(v___x_1460_, 14);
v___y_1437_ = v___x_1474_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1475_; uint8_t v___x_1476_; 
v___x_1475_ = l_Lean_Syntax_getArg(v___x_1440_, v___x_1471_);
lean_inc(v___x_1475_);
v___x_1476_ = l_Lean_Syntax_matchesNull(v___x_1475_, v___x_1471_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
lean_dec(v___x_1475_);
v___x_1477_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1394_, v___x_1403_, v___x_1405_, v_typeExpr_1393_, v___x_1440_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v___x_1460_, v_a_1401_);
lean_dec_ref_known(v___x_1460_, 14);
v___y_1437_ = v___x_1477_;
goto v___jp_1436_;
}
else
{
lean_object* v_stx_1478_; lean_object* v___x_1479_; 
lean_dec(v___x_1440_);
v_stx_1478_ = l_Lean_Syntax_getArg(v___x_1475_, v___x_1404_);
lean_dec(v___x_1475_);
v___x_1479_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1394_, v___x_1403_, v___x_1405_, v_typeExpr_1393_, v_stx_1478_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v___x_1460_, v_a_1401_);
lean_dec_ref_known(v___x_1460_, 14);
v___y_1437_ = v___x_1479_;
goto v___jp_1436_;
}
}
}
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1480_ = lean_unsigned_to_nat(1u);
v___x_1481_ = l_Lean_Syntax_getArg(v___x_1440_, v___x_1480_);
lean_inc(v___x_1481_);
v___x_1482_ = l_Lean_Syntax_matchesNull(v___x_1481_, v___x_1480_);
if (v___x_1482_ == 0)
{
uint8_t v___x_1483_; 
lean_inc(v___x_1466_);
v___x_1483_ = l_Lean_Syntax_isOfKind(v___x_1466_, v___x_1461_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; 
lean_dec(v___x_1481_);
lean_dec(v___x_1466_);
v___x_1484_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1394_, v___x_1403_, v___x_1405_, v_typeExpr_1393_, v___x_1440_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v___x_1460_, v_a_1401_);
lean_dec_ref_known(v___x_1460_, 14);
v___y_1437_ = v___x_1484_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1485_ = l_Lean_Syntax_getArg(v___x_1466_, v___x_1480_);
lean_dec(v___x_1466_);
v___x_1486_ = l_Lean_Syntax_matchesIdent(v___x_1485_, v___x_1467_);
lean_dec(v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; 
lean_dec(v___x_1481_);
v___x_1487_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1394_, v___x_1403_, v___x_1405_, v_typeExpr_1393_, v___x_1440_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v___x_1460_, v_a_1401_);
lean_dec_ref_known(v___x_1460_, 14);
v___y_1437_ = v___x_1487_;
goto v___jp_1436_;
}
else
{
if (v___x_1482_ == 0)
{
lean_object* v___x_1488_; 
lean_dec(v___x_1481_);
v___x_1488_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1394_, v___x_1403_, v___x_1405_, v_typeExpr_1393_, v___x_1440_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v___x_1460_, v_a_1401_);
lean_dec_ref_known(v___x_1460_, 14);
v___y_1437_ = v___x_1488_;
goto v___jp_1436_;
}
else
{
lean_object* v_stx_1489_; lean_object* v___x_1490_; 
lean_dec(v___x_1440_);
v_stx_1489_ = l_Lean_Syntax_getArg(v___x_1481_, v___x_1404_);
lean_dec(v___x_1481_);
v___x_1490_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1394_, v___x_1403_, v___x_1405_, v_typeExpr_1393_, v_stx_1489_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v___x_1460_, v_a_1401_);
lean_dec_ref_known(v___x_1460_, 14);
v___y_1437_ = v___x_1490_;
goto v___jp_1436_;
}
}
}
}
else
{
lean_object* v_stx_1491_; lean_object* v___x_1492_; 
lean_dec(v___x_1466_);
lean_dec(v___x_1440_);
v_stx_1491_ = l_Lean_Syntax_getArg(v___x_1481_, v___x_1404_);
lean_dec(v___x_1481_);
v___x_1492_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1394_, v___x_1403_, v___x_1405_, v_typeExpr_1393_, v_stx_1491_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v___x_1460_, v_a_1401_);
lean_dec_ref_known(v___x_1460_, 14);
v___y_1437_ = v___x_1492_;
goto v___jp_1436_;
}
}
}
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___x_1493_ = lean_unsigned_to_nat(1u);
v___x_1494_ = l_Lean_Syntax_getArg(v___x_1440_, v___x_1493_);
v___x_1495_ = l_Lean_Syntax_matchesIdent(v___x_1494_, v___x_1441_);
lean_dec(v___x_1494_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1394_, v___x_1403_, v___x_1405_, v_typeExpr_1393_, v___x_1440_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v___x_1460_, v_a_1401_);
lean_dec_ref_known(v___x_1460_, 14);
v___y_1437_ = v___x_1496_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_dec_ref_known(v___x_1460_, 14);
lean_dec(v___x_1440_);
lean_dec_ref(v_ev_1394_);
v___x_1497_ = lean_box(0);
v___x_1498_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9);
v___x_1499_ = l_Lean_Expr_app___override(v___x_1498_, v_typeExpr_1393_);
lean_inc_ref(v___x_1499_);
v___x_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1497_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
v_a_1410_ = v___x_1500_;
v_snd_1411_ = v___x_1499_;
goto v___jp_1409_;
}
}
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec(v___x_1440_);
lean_dec_ref(v_ev_1394_);
v___x_1501_ = lean_box(0);
v___x_1502_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9);
v___x_1503_ = l_Lean_Expr_app___override(v___x_1502_, v_typeExpr_1393_);
lean_inc_ref(v___x_1503_);
v___x_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1501_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
v_a_1410_ = v___x_1504_;
v_snd_1411_ = v___x_1503_;
goto v___jp_1409_;
}
v___jp_1409_:
{
lean_object* v___x_1412_; lean_object* v_infoState_1413_; uint8_t v_enabled_1414_; 
v___x_1412_ = lean_st_ref_get(v_a_1401_);
v_infoState_1413_ = lean_ctor_get(v___x_1412_, 7);
lean_inc_ref(v_infoState_1413_);
lean_dec(v___x_1412_);
v_enabled_1414_ = lean_ctor_get_uint8(v_infoState_1413_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1413_);
if (v_enabled_1414_ == 0)
{
lean_object* v___x_1415_; 
lean_dec_ref(v_snd_1411_);
lean_dec_ref_known(v___x_1408_, 1);
lean_dec(v_stx_1395_);
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v_a_1410_);
return v___x_1415_;
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; lean_object* v___x_1419_; 
v___x_1416_ = lean_box(0);
v___x_1417_ = lean_box(0);
v___x_1418_ = 0;
v___x_1419_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_1395_, v_snd_1411_, v___x_1408_, v___x_1416_, v___x_1417_, v___x_1418_, v___x_1418_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; 
v_unused_1427_ = lean_ctor_get(v___x_1419_, 0);
lean_dec(v_unused_1427_);
v___x_1421_ = v___x_1419_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_dec(v___x_1419_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v_a_1410_);
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1410_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec_ref(v_a_1410_);
v_a_1428_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1419_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1419_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
v___jp_1436_:
{
if (lean_obj_tag(v___y_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v_snd_1439_; 
v_a_1438_ = lean_ctor_get(v___y_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___y_1437_, 1);
v_snd_1439_ = lean_ctor_get(v_a_1438_, 1);
lean_inc(v_snd_1439_);
v_a_1410_ = v_a_1438_;
v_snd_1411_ = v_snd_1439_;
goto v___jp_1409_;
}
else
{
lean_dec_ref_known(v___x_1408_, 1);
lean_dec(v_stx_1395_);
return v___y_1437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___boxed(lean_object* v_typeExpr_1505_, lean_object* v_ev_1506_, lean_object* v_stx_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(v_typeExpr_1505_, v_ev_1506_, v_stx_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
lean_dec(v_a_1513_);
lean_dec_ref(v_a_1512_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx(lean_object* v_00_u03b1_1516_, lean_object* v_typeExpr_1517_, lean_object* v_ev_1518_, lean_object* v_stx_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(v_typeExpr_1517_, v_ev_1518_, v_stx_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___boxed(lean_object* v_00_u03b1_1528_, lean_object* v_typeExpr_1529_, lean_object* v_ev_1530_, lean_object* v_stx_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx(v_00_u03b1_1528_, v_typeExpr_1529_, v_ev_1530_, v_stx_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(uint8_t v___x_1540_, lean_object* v_as_1541_, size_t v_i_1542_, size_t v_stop_1543_, lean_object* v_b_1544_){
_start:
{
lean_object* v___y_1546_; uint8_t v___x_1550_; 
v___x_1550_ = lean_usize_dec_eq(v_i_1542_, v_stop_1543_);
if (v___x_1550_ == 0)
{
lean_object* v_fst_1551_; uint8_t v___x_1552_; 
v_fst_1551_ = lean_ctor_get(v_b_1544_, 0);
v___x_1552_ = lean_unbox(v_fst_1551_);
if (v___x_1552_ == 0)
{
lean_object* v_snd_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1561_; 
v_snd_1553_ = lean_ctor_get(v_b_1544_, 1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_b_1544_);
if (v_isSharedCheck_1561_ == 0)
{
lean_object* v_unused_1562_; 
v_unused_1562_ = lean_ctor_get(v_b_1544_, 0);
lean_dec(v_unused_1562_);
v___x_1555_ = v_b_1544_;
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_snd_1553_);
lean_dec(v_b_1544_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = lean_box(v___x_1540_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1557_);
v___x_1559_ = v___x_1555_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_snd_1553_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
v___y_1546_ = v___x_1559_;
goto v___jp_1545_;
}
}
}
else
{
lean_object* v_snd_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1573_; 
v_snd_1563_ = lean_ctor_get(v_b_1544_, 1);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_b_1544_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; 
v_unused_1574_ = lean_ctor_get(v_b_1544_, 0);
lean_dec(v_unused_1574_);
v___x_1565_ = v_b_1544_;
v_isShared_1566_ = v_isSharedCheck_1573_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_snd_1563_);
lean_dec(v_b_1544_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1573_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1567_ = lean_array_uget_borrowed(v_as_1541_, v_i_1542_);
lean_inc(v___x_1567_);
v___x_1568_ = lean_array_push(v_snd_1563_, v___x_1567_);
v___x_1569_ = lean_box(v___x_1550_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 1, v___x_1568_);
lean_ctor_set(v___x_1565_, 0, v___x_1569_);
v___x_1571_ = v___x_1565_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v___x_1568_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
v___y_1546_ = v___x_1571_;
goto v___jp_1545_;
}
}
}
}
else
{
return v_b_1544_;
}
v___jp_1545_:
{
size_t v___x_1547_; size_t v___x_1548_; 
v___x_1547_ = ((size_t)1ULL);
v___x_1548_ = lean_usize_add(v_i_1542_, v___x_1547_);
v_i_1542_ = v___x_1548_;
v_b_1544_ = v___y_1546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3___boxed(lean_object* v___x_1575_, lean_object* v_as_1576_, lean_object* v_i_1577_, lean_object* v_stop_1578_, lean_object* v_b_1579_){
_start:
{
uint8_t v___x_1661__boxed_1580_; size_t v_i_boxed_1581_; size_t v_stop_boxed_1582_; lean_object* v_res_1583_; 
v___x_1661__boxed_1580_ = lean_unbox(v___x_1575_);
v_i_boxed_1581_ = lean_unbox_usize(v_i_1577_);
lean_dec(v_i_1577_);
v_stop_boxed_1582_ = lean_unbox_usize(v_stop_1578_);
lean_dec(v_stop_1578_);
v_res_1583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_1661__boxed_1580_, v_as_1576_, v_i_boxed_1581_, v_stop_boxed_1582_, v_b_1579_);
lean_dec_ref(v_as_1576_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(lean_object* v_ev_1584_, size_t v_sz_1585_, size_t v_i_1586_, lean_object* v_bs_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
uint8_t v___x_1595_; 
v___x_1595_ = lean_usize_dec_lt(v_i_1586_, v_sz_1585_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; 
lean_dec_ref(v_ev_1584_);
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v_bs_1587_);
return v___x_1596_;
}
else
{
lean_object* v_v_1597_; lean_object* v___x_1598_; 
v_v_1597_ = lean_array_uget_borrowed(v_bs_1587_, v_i_1586_);
lean_inc_ref(v_ev_1584_);
lean_inc(v___y_1593_);
lean_inc_ref(v___y_1592_);
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
lean_inc(v___y_1589_);
lean_inc_ref(v___y_1588_);
lean_inc(v_v_1597_);
v___x_1598_ = lean_apply_8(v_ev_1584_, v_v_1597_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, lean_box(0));
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1600_; lean_object* v_bs_x27_1601_; size_t v___x_1602_; size_t v___x_1603_; lean_object* v___x_1604_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
v___x_1600_ = lean_unsigned_to_nat(0u);
v_bs_x27_1601_ = lean_array_uset(v_bs_1587_, v_i_1586_, v___x_1600_);
v___x_1602_ = ((size_t)1ULL);
v___x_1603_ = lean_usize_add(v_i_1586_, v___x_1602_);
v___x_1604_ = lean_array_uset(v_bs_x27_1601_, v_i_1586_, v_a_1599_);
v_i_1586_ = v___x_1603_;
v_bs_1587_ = v___x_1604_;
goto _start;
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec_ref(v_bs_1587_);
lean_dec_ref(v_ev_1584_);
v_a_1606_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1598_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1598_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg___boxed(lean_object* v_ev_1614_, lean_object* v_sz_1615_, lean_object* v_i_1616_, lean_object* v_bs_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
size_t v_sz_boxed_1625_; size_t v_i_boxed_1626_; lean_object* v_res_1627_; 
v_sz_boxed_1625_ = lean_unbox_usize(v_sz_1615_);
lean_dec(v_sz_1615_);
v_i_boxed_1626_ = lean_unbox_usize(v_i_1616_);
lean_dec(v_i_1616_);
v_res_1627_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(v_ev_1614_, v_sz_boxed_1625_, v_i_boxed_1626_, v_bs_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
return v_res_1627_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1633_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1634_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2));
v___x_1635_ = l_Lean_Expr_const___override(v___x_1634_, v___x_1633_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2(lean_object* v_typeExpr_1636_, lean_object* v_as_1637_, size_t v_i_1638_, size_t v_stop_1639_, lean_object* v_b_1640_){
_start:
{
uint8_t v___x_1641_; 
v___x_1641_ = lean_usize_dec_eq(v_i_1638_, v_stop_1639_);
if (v___x_1641_ == 0)
{
size_t v___x_1642_; size_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1642_ = ((size_t)1ULL);
v___x_1643_ = lean_usize_sub(v_i_1638_, v___x_1642_);
v___x_1644_ = lean_array_uget_borrowed(v_as_1637_, v___x_1643_);
v___x_1645_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3);
lean_inc(v___x_1644_);
lean_inc_ref(v_typeExpr_1636_);
v___x_1646_ = l_Lean_mkApp3(v___x_1645_, v_typeExpr_1636_, v___x_1644_, v_b_1640_);
v_i_1638_ = v___x_1643_;
v_b_1640_ = v___x_1646_;
goto _start;
}
else
{
lean_dec_ref(v_typeExpr_1636_);
return v_b_1640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___boxed(lean_object* v_typeExpr_1648_, lean_object* v_as_1649_, lean_object* v_i_1650_, lean_object* v_stop_1651_, lean_object* v_b_1652_){
_start:
{
size_t v_i_boxed_1653_; size_t v_stop_boxed_1654_; lean_object* v_res_1655_; 
v_i_boxed_1653_ = lean_unbox_usize(v_i_1650_);
lean_dec(v_i_1650_);
v_stop_boxed_1654_ = lean_unbox_usize(v_stop_1651_);
lean_dec(v_stop_1651_);
v_res_1655_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2(v_typeExpr_1648_, v_as_1649_, v_i_boxed_1653_, v_stop_boxed_1654_, v_b_1652_);
lean_dec_ref(v_as_1649_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0(size_t v_sz_1656_, size_t v_i_1657_, lean_object* v_bs_1658_){
_start:
{
uint8_t v___x_1659_; 
v___x_1659_ = lean_usize_dec_lt(v_i_1657_, v_sz_1656_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1660_, 0, v_bs_1658_);
return v___x_1660_;
}
else
{
lean_object* v_v_1661_; lean_object* v___x_1662_; lean_object* v_bs_x27_1663_; size_t v___x_1664_; size_t v___x_1665_; lean_object* v___x_1666_; 
v_v_1661_ = lean_array_uget(v_bs_1658_, v_i_1657_);
v___x_1662_ = lean_unsigned_to_nat(0u);
v_bs_x27_1663_ = lean_array_uset(v_bs_1658_, v_i_1657_, v___x_1662_);
v___x_1664_ = ((size_t)1ULL);
v___x_1665_ = lean_usize_add(v_i_1657_, v___x_1664_);
v___x_1666_ = lean_array_uset(v_bs_x27_1663_, v_i_1657_, v_v_1661_);
v_i_1657_ = v___x_1665_;
v_bs_1658_ = v___x_1666_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0___boxed(lean_object* v_sz_1668_, lean_object* v_i_1669_, lean_object* v_bs_1670_){
_start:
{
size_t v_sz_boxed_1671_; size_t v_i_boxed_1672_; lean_object* v_res_1673_; 
v_sz_boxed_1671_ = lean_unbox_usize(v_sz_1668_);
lean_dec(v_sz_1668_);
v_i_boxed_1672_ = lean_unbox_usize(v_i_1669_);
lean_dec(v_i_1669_);
v_res_1673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0(v_sz_boxed_1671_, v_i_boxed_1672_, v_bs_1670_);
return v_res_1673_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1677_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__0));
v___x_1678_ = l_Lean_Expr_const___override(v___x_1677_, v___x_1676_);
return v___x_1678_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1687_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5));
v___x_1688_ = l_Lean_Expr_const___override(v___x_1687_, v___x_1686_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(lean_object* v_typeExpr_1691_, lean_object* v_ev_1692_, lean_object* v_stx_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_fileName_1701_; lean_object* v_fileMap_1702_; lean_object* v_options_1703_; lean_object* v_currRecDepth_1704_; lean_object* v_maxRecDepth_1705_; lean_object* v_ref_1706_; lean_object* v_currNamespace_1707_; lean_object* v_openDecls_1708_; lean_object* v_initHeartbeats_1709_; lean_object* v_maxHeartbeats_1710_; lean_object* v_quotContext_1711_; lean_object* v_currMacroScope_1712_; uint8_t v_diag_1713_; lean_object* v_cancelTk_x3f_1714_; uint8_t v_suppressElabErrors_1715_; lean_object* v_inheritedTraceOptions_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v_a_1722_; lean_object* v_snd_1723_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v_fileName_1701_ = lean_ctor_get(v_a_1698_, 0);
v_fileMap_1702_ = lean_ctor_get(v_a_1698_, 1);
v_options_1703_ = lean_ctor_get(v_a_1698_, 2);
v_currRecDepth_1704_ = lean_ctor_get(v_a_1698_, 3);
v_maxRecDepth_1705_ = lean_ctor_get(v_a_1698_, 4);
v_ref_1706_ = lean_ctor_get(v_a_1698_, 5);
v_currNamespace_1707_ = lean_ctor_get(v_a_1698_, 6);
v_openDecls_1708_ = lean_ctor_get(v_a_1698_, 7);
v_initHeartbeats_1709_ = lean_ctor_get(v_a_1698_, 8);
v_maxHeartbeats_1710_ = lean_ctor_get(v_a_1698_, 9);
v_quotContext_1711_ = lean_ctor_get(v_a_1698_, 10);
v_currMacroScope_1712_ = lean_ctor_get(v_a_1698_, 11);
v_diag_1713_ = lean_ctor_get_uint8(v_a_1698_, sizeof(void*)*14);
v_cancelTk_x3f_1714_ = lean_ctor_get(v_a_1698_, 12);
v_suppressElabErrors_1715_ = lean_ctor_get_uint8(v_a_1698_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1716_ = lean_ctor_get(v_a_1698_, 13);
v___x_1717_ = lean_unsigned_to_nat(0u);
v___x_1718_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1);
lean_inc_ref(v_typeExpr_1691_);
v___x_1719_ = l_Lean_Expr_app___override(v___x_1718_, v_typeExpr_1691_);
v___x_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
lean_inc(v_stx_1693_);
v___x_1755_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_1693_);
v___x_1756_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__3));
lean_inc(v___x_1755_);
v___x_1757_ = l_Lean_Syntax_isOfKind(v___x_1755_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; 
lean_dec(v___x_1755_);
lean_dec_ref_known(v___x_1720_, 1);
lean_dec(v_stx_1693_);
lean_dec_ref(v_ev_1692_);
lean_dec_ref(v_typeExpr_1691_);
v___x_1758_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_1754_ = v___x_1758_;
goto v___jp_1753_;
}
else
{
lean_object* v_ref_1759_; lean_object* v___x_1760_; lean_object* v___y_1762_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v_ref_1759_ = l_Lean_replaceRef(v_stx_1693_, v_ref_1706_);
lean_inc_ref(v_inheritedTraceOptions_1716_);
lean_inc(v_cancelTk_x3f_1714_);
lean_inc(v_currMacroScope_1712_);
lean_inc(v_quotContext_1711_);
lean_inc(v_maxHeartbeats_1710_);
lean_inc(v_initHeartbeats_1709_);
lean_inc(v_openDecls_1708_);
lean_inc(v_currNamespace_1707_);
lean_inc(v_maxRecDepth_1705_);
lean_inc(v_currRecDepth_1704_);
lean_inc_ref(v_options_1703_);
lean_inc_ref(v_fileMap_1702_);
lean_inc_ref(v_fileName_1701_);
v___x_1760_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1760_, 0, v_fileName_1701_);
lean_ctor_set(v___x_1760_, 1, v_fileMap_1702_);
lean_ctor_set(v___x_1760_, 2, v_options_1703_);
lean_ctor_set(v___x_1760_, 3, v_currRecDepth_1704_);
lean_ctor_set(v___x_1760_, 4, v_maxRecDepth_1705_);
lean_ctor_set(v___x_1760_, 5, v_ref_1759_);
lean_ctor_set(v___x_1760_, 6, v_currNamespace_1707_);
lean_ctor_set(v___x_1760_, 7, v_openDecls_1708_);
lean_ctor_set(v___x_1760_, 8, v_initHeartbeats_1709_);
lean_ctor_set(v___x_1760_, 9, v_maxHeartbeats_1710_);
lean_ctor_set(v___x_1760_, 10, v_quotContext_1711_);
lean_ctor_set(v___x_1760_, 11, v_currMacroScope_1712_);
lean_ctor_set(v___x_1760_, 12, v_cancelTk_x3f_1714_);
lean_ctor_set(v___x_1760_, 13, v_inheritedTraceOptions_1716_);
lean_ctor_set_uint8(v___x_1760_, sizeof(void*)*14, v_diag_1713_);
lean_ctor_set_uint8(v___x_1760_, sizeof(void*)*14 + 1, v_suppressElabErrors_1715_);
v___x_1788_ = lean_unsigned_to_nat(1u);
v___x_1789_ = l_Lean_Syntax_getArg(v___x_1755_, v___x_1788_);
lean_dec(v___x_1755_);
v___x_1790_ = l_Lean_Syntax_getArgs(v___x_1789_);
lean_dec(v___x_1789_);
v___x_1791_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__7));
v___x_1792_ = lean_array_get_size(v___x_1790_);
v___x_1793_ = lean_nat_dec_lt(v___x_1717_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_dec_ref(v___x_1790_);
v___y_1762_ = v___x_1791_;
goto v___jp_1761_;
}
else
{
lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1794_ = lean_box(v___x_1757_);
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
lean_ctor_set(v___x_1795_, 1, v___x_1791_);
v___x_1796_ = lean_nat_dec_le(v___x_1792_, v___x_1792_);
if (v___x_1796_ == 0)
{
if (v___x_1793_ == 0)
{
lean_dec_ref_known(v___x_1795_, 2);
lean_dec_ref(v___x_1790_);
v___y_1762_ = v___x_1791_;
goto v___jp_1761_;
}
else
{
size_t v___x_1797_; size_t v___x_1798_; lean_object* v___x_1799_; lean_object* v_snd_1800_; 
v___x_1797_ = ((size_t)0ULL);
v___x_1798_ = lean_usize_of_nat(v___x_1792_);
v___x_1799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_1757_, v___x_1790_, v___x_1797_, v___x_1798_, v___x_1795_);
lean_dec_ref(v___x_1790_);
v_snd_1800_ = lean_ctor_get(v___x_1799_, 1);
lean_inc(v_snd_1800_);
lean_dec_ref(v___x_1799_);
v___y_1762_ = v_snd_1800_;
goto v___jp_1761_;
}
}
else
{
size_t v___x_1801_; size_t v___x_1802_; lean_object* v___x_1803_; lean_object* v_snd_1804_; 
v___x_1801_ = ((size_t)0ULL);
v___x_1802_ = lean_usize_of_nat(v___x_1792_);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_1757_, v___x_1790_, v___x_1801_, v___x_1802_, v___x_1795_);
lean_dec_ref(v___x_1790_);
v_snd_1804_ = lean_ctor_get(v___x_1803_, 1);
lean_inc(v_snd_1804_);
lean_dec_ref(v___x_1803_);
v___y_1762_ = v_snd_1804_;
goto v___jp_1761_;
}
}
v___jp_1761_:
{
size_t v_sz_1763_; size_t v___x_1764_; lean_object* v___x_1765_; 
v_sz_1763_ = lean_array_size(v___y_1762_);
v___x_1764_ = ((size_t)0ULL);
v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0(v_sz_1763_, v___x_1764_, v___y_1762_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v___x_1766_; 
lean_dec_ref_known(v___x_1760_, 14);
lean_dec_ref_known(v___x_1720_, 1);
lean_dec(v_stx_1693_);
lean_dec_ref(v_ev_1692_);
lean_dec_ref(v_typeExpr_1691_);
v___x_1766_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_1754_ = v___x_1766_;
goto v___jp_1753_;
}
else
{
lean_object* v_val_1767_; size_t v_sz_1768_; lean_object* v___x_1769_; 
v_val_1767_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_val_1767_);
lean_dec_ref_known(v___x_1765_, 1);
v_sz_1768_ = lean_array_size(v_val_1767_);
v___x_1769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(v_ev_1692_, v_sz_1768_, v___x_1764_, v_val_1767_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v___x_1760_, v_a_1699_);
lean_dec_ref_known(v___x_1760_, 14);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1771_; lean_object* v_fst_1772_; lean_object* v_snd_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___x_1769_, 1);
v___x_1771_ = l_Array_unzip___redArg(v_a_1770_);
lean_dec(v_a_1770_);
v_fst_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_fst_1772_);
v_snd_1773_ = lean_ctor_get(v___x_1771_, 1);
lean_inc(v_snd_1773_);
lean_dec_ref(v___x_1771_);
v___x_1774_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6, &l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6);
lean_inc_ref(v_typeExpr_1691_);
v___x_1775_ = l_Lean_Expr_app___override(v___x_1774_, v_typeExpr_1691_);
v___x_1776_ = lean_array_get_size(v_snd_1773_);
v___x_1777_ = lean_nat_dec_lt(v___x_1717_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_dec(v_snd_1773_);
lean_dec_ref(v_typeExpr_1691_);
v___y_1749_ = v_fst_1772_;
v___y_1750_ = v___x_1775_;
goto v___jp_1748_;
}
else
{
size_t v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_usize_of_nat(v___x_1776_);
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2(v_typeExpr_1691_, v_snd_1773_, v___x_1778_, v___x_1764_, v___x_1775_);
lean_dec(v_snd_1773_);
v___y_1749_ = v_fst_1772_;
v___y_1750_ = v___x_1779_;
goto v___jp_1748_;
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec_ref_known(v___x_1720_, 1);
lean_dec(v_stx_1693_);
lean_dec_ref(v_typeExpr_1691_);
v_a_1780_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1769_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1769_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
}
v___jp_1721_:
{
lean_object* v___x_1724_; lean_object* v_infoState_1725_; uint8_t v_enabled_1726_; 
v___x_1724_ = lean_st_ref_get(v_a_1699_);
v_infoState_1725_ = lean_ctor_get(v___x_1724_, 7);
lean_inc_ref(v_infoState_1725_);
lean_dec(v___x_1724_);
v_enabled_1726_ = lean_ctor_get_uint8(v_infoState_1725_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1725_);
if (v_enabled_1726_ == 0)
{
lean_object* v___x_1727_; 
lean_dec_ref(v_snd_1723_);
lean_dec_ref_known(v___x_1720_, 1);
lean_dec(v_stx_1693_);
v___x_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1727_, 0, v_a_1722_);
return v___x_1727_;
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; uint8_t v___x_1730_; lean_object* v___x_1731_; 
v___x_1728_ = lean_box(0);
v___x_1729_ = lean_box(0);
v___x_1730_ = 0;
v___x_1731_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_1693_, v_snd_1723_, v___x_1720_, v___x_1728_, v___x_1729_, v___x_1730_, v___x_1730_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1738_ == 0)
{
lean_object* v_unused_1739_; 
v_unused_1739_ = lean_ctor_get(v___x_1731_, 0);
lean_dec(v_unused_1739_);
v___x_1733_ = v___x_1731_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_dec(v___x_1731_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v_a_1722_);
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1722_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec_ref(v_a_1722_);
v_a_1740_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1731_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1731_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
v___jp_1748_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_array_to_list(v___y_1749_);
lean_inc_ref(v___y_1750_);
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
lean_ctor_set(v___x_1752_, 1, v___y_1750_);
v_a_1722_ = v___x_1752_;
v_snd_1723_ = v___y_1750_;
goto v___jp_1721_;
}
v___jp_1753_:
{
return v___y_1754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___boxed(lean_object* v_typeExpr_1805_, lean_object* v_ev_1806_, lean_object* v_stx_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(v_typeExpr_1805_, v_ev_1806_, v_stx_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
lean_dec(v_a_1811_);
lean_dec_ref(v_a_1810_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx(lean_object* v_00_u03b1_1816_, lean_object* v_typeExpr_1817_, lean_object* v_ev_1818_, lean_object* v_stx_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(v_typeExpr_1817_, v_ev_1818_, v_stx_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___boxed(lean_object* v_00_u03b1_1828_, lean_object* v_typeExpr_1829_, lean_object* v_ev_1830_, lean_object* v_stx_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx(v_00_u03b1_1828_, v_typeExpr_1829_, v_ev_1830_, v_stx_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1(lean_object* v_00_u03b1_1840_, lean_object* v_ev_1841_, size_t v_sz_1842_, size_t v_i_1843_, lean_object* v_bs_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(v_ev_1841_, v_sz_1842_, v_i_1843_, v_bs_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___boxed(lean_object* v_00_u03b1_1853_, lean_object* v_ev_1854_, lean_object* v_sz_1855_, lean_object* v_i_1856_, lean_object* v_bs_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
size_t v_sz_boxed_1865_; size_t v_i_boxed_1866_; lean_object* v_res_1867_; 
v_sz_boxed_1865_ = lean_unbox_usize(v_sz_1855_);
lean_dec(v_sz_1855_);
v_i_boxed_1866_ = lean_unbox_usize(v_i_1856_);
lean_dec(v_i_1856_);
v_res_1867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1(v_00_u03b1_1853_, v_ev_1854_, v_sz_boxed_1865_, v_i_boxed_1866_, v_bs_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0(lean_object* v_typeExpr_1868_, lean_object* v_as_1869_, size_t v_i_1870_, size_t v_stop_1871_, lean_object* v_b_1872_){
_start:
{
uint8_t v___x_1873_; 
v___x_1873_ = lean_usize_dec_eq(v_i_1870_, v_stop_1871_);
if (v___x_1873_ == 0)
{
size_t v___x_1874_; size_t v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1874_ = ((size_t)1ULL);
v___x_1875_ = lean_usize_sub(v_i_1870_, v___x_1874_);
v___x_1876_ = lean_array_uget_borrowed(v_as_1869_, v___x_1875_);
v___x_1877_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3);
lean_inc(v___x_1876_);
lean_inc_ref(v_typeExpr_1868_);
v___x_1878_ = l_Lean_mkApp3(v___x_1877_, v_typeExpr_1868_, v___x_1876_, v_b_1872_);
v_i_1870_ = v___x_1875_;
v_b_1872_ = v___x_1878_;
goto _start;
}
else
{
lean_dec_ref(v_typeExpr_1868_);
return v_b_1872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0___boxed(lean_object* v_typeExpr_1880_, lean_object* v_as_1881_, lean_object* v_i_1882_, lean_object* v_stop_1883_, lean_object* v_b_1884_){
_start:
{
size_t v_i_boxed_1885_; size_t v_stop_boxed_1886_; lean_object* v_res_1887_; 
v_i_boxed_1885_ = lean_unbox_usize(v_i_1882_);
lean_dec(v_i_1882_);
v_stop_boxed_1886_ = lean_unbox_usize(v_stop_1883_);
lean_dec(v_stop_1883_);
v_res_1887_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0(v_typeExpr_1880_, v_as_1881_, v_i_boxed_1885_, v_stop_boxed_1886_, v_b_1884_);
lean_dec_ref(v_as_1881_);
return v_res_1887_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2(void){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1892_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__1));
v___x_1893_ = l_Lean_Expr_const___override(v___x_1892_, v___x_1891_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg(lean_object* v_typeExpr_1898_, lean_object* v_ev_1899_, lean_object* v_stx_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v_fileName_1908_; lean_object* v_fileMap_1909_; lean_object* v_options_1910_; lean_object* v_currRecDepth_1911_; lean_object* v_maxRecDepth_1912_; lean_object* v_ref_1913_; lean_object* v_currNamespace_1914_; lean_object* v_openDecls_1915_; lean_object* v_initHeartbeats_1916_; lean_object* v_maxHeartbeats_1917_; lean_object* v_quotContext_1918_; lean_object* v_currMacroScope_1919_; uint8_t v_diag_1920_; lean_object* v_cancelTk_x3f_1921_; uint8_t v_suppressElabErrors_1922_; lean_object* v_inheritedTraceOptions_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v_a_1930_; lean_object* v_snd_1931_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v_fileName_1908_ = lean_ctor_get(v_a_1905_, 0);
v_fileMap_1909_ = lean_ctor_get(v_a_1905_, 1);
v_options_1910_ = lean_ctor_get(v_a_1905_, 2);
v_currRecDepth_1911_ = lean_ctor_get(v_a_1905_, 3);
v_maxRecDepth_1912_ = lean_ctor_get(v_a_1905_, 4);
v_ref_1913_ = lean_ctor_get(v_a_1905_, 5);
v_currNamespace_1914_ = lean_ctor_get(v_a_1905_, 6);
v_openDecls_1915_ = lean_ctor_get(v_a_1905_, 7);
v_initHeartbeats_1916_ = lean_ctor_get(v_a_1905_, 8);
v_maxHeartbeats_1917_ = lean_ctor_get(v_a_1905_, 9);
v_quotContext_1918_ = lean_ctor_get(v_a_1905_, 10);
v_currMacroScope_1919_ = lean_ctor_get(v_a_1905_, 11);
v_diag_1920_ = lean_ctor_get_uint8(v_a_1905_, sizeof(void*)*14);
v_cancelTk_x3f_1921_ = lean_ctor_get(v_a_1905_, 12);
v_suppressElabErrors_1922_ = lean_ctor_get_uint8(v_a_1905_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1923_ = lean_ctor_get(v_a_1905_, 13);
v___x_1924_ = lean_unsigned_to_nat(0u);
v___x_1925_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1926_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2);
lean_inc_ref(v_typeExpr_1898_);
v___x_1927_ = l_Lean_Expr_app___override(v___x_1926_, v_typeExpr_1898_);
v___x_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
lean_inc(v_stx_1900_);
v___x_1967_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_1900_);
v___x_1968_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__5));
lean_inc(v___x_1967_);
v___x_1969_ = l_Lean_Syntax_isOfKind(v___x_1967_, v___x_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; 
lean_dec(v___x_1967_);
lean_dec_ref_known(v___x_1928_, 1);
lean_dec(v_stx_1900_);
lean_dec_ref(v_ev_1899_);
lean_dec_ref(v_typeExpr_1898_);
v___x_1970_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_1966_ = v___x_1970_;
goto v___jp_1965_;
}
else
{
lean_object* v_ref_1971_; lean_object* v___x_1972_; lean_object* v___y_1974_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
v_ref_1971_ = l_Lean_replaceRef(v_stx_1900_, v_ref_1913_);
lean_inc_ref(v_inheritedTraceOptions_1923_);
lean_inc(v_cancelTk_x3f_1921_);
lean_inc(v_currMacroScope_1919_);
lean_inc(v_quotContext_1918_);
lean_inc(v_maxHeartbeats_1917_);
lean_inc(v_initHeartbeats_1916_);
lean_inc(v_openDecls_1915_);
lean_inc(v_currNamespace_1914_);
lean_inc(v_maxRecDepth_1912_);
lean_inc(v_currRecDepth_1911_);
lean_inc_ref(v_options_1910_);
lean_inc_ref(v_fileMap_1909_);
lean_inc_ref(v_fileName_1908_);
v___x_1972_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1972_, 0, v_fileName_1908_);
lean_ctor_set(v___x_1972_, 1, v_fileMap_1909_);
lean_ctor_set(v___x_1972_, 2, v_options_1910_);
lean_ctor_set(v___x_1972_, 3, v_currRecDepth_1911_);
lean_ctor_set(v___x_1972_, 4, v_maxRecDepth_1912_);
lean_ctor_set(v___x_1972_, 5, v_ref_1971_);
lean_ctor_set(v___x_1972_, 6, v_currNamespace_1914_);
lean_ctor_set(v___x_1972_, 7, v_openDecls_1915_);
lean_ctor_set(v___x_1972_, 8, v_initHeartbeats_1916_);
lean_ctor_set(v___x_1972_, 9, v_maxHeartbeats_1917_);
lean_ctor_set(v___x_1972_, 10, v_quotContext_1918_);
lean_ctor_set(v___x_1972_, 11, v_currMacroScope_1919_);
lean_ctor_set(v___x_1972_, 12, v_cancelTk_x3f_1921_);
lean_ctor_set(v___x_1972_, 13, v_inheritedTraceOptions_1923_);
lean_ctor_set_uint8(v___x_1972_, sizeof(void*)*14, v_diag_1920_);
lean_ctor_set_uint8(v___x_1972_, sizeof(void*)*14 + 1, v_suppressElabErrors_1922_);
v___x_2001_ = lean_unsigned_to_nat(1u);
v___x_2002_ = l_Lean_Syntax_getArg(v___x_1967_, v___x_2001_);
lean_dec(v___x_1967_);
v___x_2003_ = l_Lean_Syntax_getArgs(v___x_2002_);
lean_dec(v___x_2002_);
v___x_2004_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__7));
v___x_2005_ = lean_array_get_size(v___x_2003_);
v___x_2006_ = lean_nat_dec_lt(v___x_1924_, v___x_2005_);
if (v___x_2006_ == 0)
{
lean_dec_ref(v___x_2003_);
v___y_1974_ = v___x_2004_;
goto v___jp_1973_;
}
else
{
lean_object* v___x_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v___x_2007_ = lean_box(v___x_1969_);
v___x_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
lean_ctor_set(v___x_2008_, 1, v___x_2004_);
v___x_2009_ = lean_nat_dec_le(v___x_2005_, v___x_2005_);
if (v___x_2009_ == 0)
{
if (v___x_2006_ == 0)
{
lean_dec_ref_known(v___x_2008_, 2);
lean_dec_ref(v___x_2003_);
v___y_1974_ = v___x_2004_;
goto v___jp_1973_;
}
else
{
size_t v___x_2010_; size_t v___x_2011_; lean_object* v___x_2012_; lean_object* v_snd_2013_; 
v___x_2010_ = ((size_t)0ULL);
v___x_2011_ = lean_usize_of_nat(v___x_2005_);
v___x_2012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_1969_, v___x_2003_, v___x_2010_, v___x_2011_, v___x_2008_);
lean_dec_ref(v___x_2003_);
v_snd_2013_ = lean_ctor_get(v___x_2012_, 1);
lean_inc(v_snd_2013_);
lean_dec_ref(v___x_2012_);
v___y_1974_ = v_snd_2013_;
goto v___jp_1973_;
}
}
else
{
size_t v___x_2014_; size_t v___x_2015_; lean_object* v___x_2016_; lean_object* v_snd_2017_; 
v___x_2014_ = ((size_t)0ULL);
v___x_2015_ = lean_usize_of_nat(v___x_2005_);
v___x_2016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_1969_, v___x_2003_, v___x_2014_, v___x_2015_, v___x_2008_);
lean_dec_ref(v___x_2003_);
v_snd_2017_ = lean_ctor_get(v___x_2016_, 1);
lean_inc(v_snd_2017_);
lean_dec_ref(v___x_2016_);
v___y_1974_ = v_snd_2017_;
goto v___jp_1973_;
}
}
v___jp_1973_:
{
size_t v_sz_1975_; size_t v___x_1976_; lean_object* v___x_1977_; 
v_sz_1975_ = lean_array_size(v___y_1974_);
v___x_1976_ = ((size_t)0ULL);
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0(v_sz_1975_, v___x_1976_, v___y_1974_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v___x_1978_; 
lean_dec_ref_known(v___x_1972_, 14);
lean_dec_ref_known(v___x_1928_, 1);
lean_dec(v_stx_1900_);
lean_dec_ref(v_ev_1899_);
lean_dec_ref(v_typeExpr_1898_);
v___x_1978_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_1966_ = v___x_1978_;
goto v___jp_1965_;
}
else
{
lean_object* v_val_1979_; size_t v_sz_1980_; lean_object* v___x_1981_; 
v_val_1979_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_val_1979_);
lean_dec_ref_known(v___x_1977_, 1);
v_sz_1980_ = lean_array_size(v_val_1979_);
v___x_1981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(v_ev_1899_, v_sz_1980_, v___x_1976_, v_val_1979_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v___x_1972_, v_a_1906_);
lean_dec_ref_known(v___x_1972_, 14);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1983_; lean_object* v_fst_1984_; lean_object* v_snd_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref_known(v___x_1981_, 1);
v___x_1983_ = l_Array_unzip___redArg(v_a_1982_);
lean_dec(v_a_1982_);
v_fst_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_fst_1984_);
v_snd_1985_ = lean_ctor_get(v___x_1983_, 1);
lean_inc(v_snd_1985_);
lean_dec_ref(v___x_1983_);
v___x_1986_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0));
v___x_1987_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6, &l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6);
lean_inc_ref(v_typeExpr_1898_);
v___x_1988_ = l_Lean_Expr_app___override(v___x_1987_, v_typeExpr_1898_);
v___x_1989_ = lean_array_get_size(v_snd_1985_);
v___x_1990_ = lean_nat_dec_lt(v___x_1924_, v___x_1989_);
if (v___x_1990_ == 0)
{
lean_dec(v_snd_1985_);
v___y_1957_ = v___x_1986_;
v___y_1958_ = v_fst_1984_;
v___y_1959_ = v___x_1988_;
goto v___jp_1956_;
}
else
{
size_t v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = lean_usize_of_nat(v___x_1989_);
lean_inc_ref(v_typeExpr_1898_);
v___x_1992_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0(v_typeExpr_1898_, v_snd_1985_, v___x_1991_, v___x_1976_, v___x_1988_);
lean_dec(v_snd_1985_);
v___y_1957_ = v___x_1986_;
v___y_1958_ = v_fst_1984_;
v___y_1959_ = v___x_1992_;
goto v___jp_1956_;
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec_ref_known(v___x_1928_, 1);
lean_dec(v_stx_1900_);
lean_dec_ref(v_typeExpr_1898_);
v_a_1993_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1981_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1981_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
}
v___jp_1929_:
{
lean_object* v___x_1932_; lean_object* v_infoState_1933_; uint8_t v_enabled_1934_; 
v___x_1932_ = lean_st_ref_get(v_a_1906_);
v_infoState_1933_ = lean_ctor_get(v___x_1932_, 7);
lean_inc_ref(v_infoState_1933_);
lean_dec(v___x_1932_);
v_enabled_1934_ = lean_ctor_get_uint8(v_infoState_1933_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1933_);
if (v_enabled_1934_ == 0)
{
lean_object* v___x_1935_; 
lean_dec_ref(v_snd_1931_);
lean_dec_ref_known(v___x_1928_, 1);
lean_dec(v_stx_1900_);
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v_a_1930_);
return v___x_1935_;
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; lean_object* v___x_1939_; 
v___x_1936_ = lean_box(0);
v___x_1937_ = lean_box(0);
v___x_1938_ = 0;
v___x_1939_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_1900_, v_snd_1931_, v___x_1928_, v___x_1936_, v___x_1937_, v___x_1938_, v___x_1938_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1946_ == 0)
{
lean_object* v_unused_1947_; 
v_unused_1947_ = lean_ctor_get(v___x_1939_, 0);
lean_dec(v_unused_1947_);
v___x_1941_ = v___x_1939_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_dec(v___x_1939_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v_a_1930_);
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1930_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec_ref(v_a_1930_);
v_a_1948_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1939_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1939_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
v___jp_1956_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1960_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__3));
lean_inc_ref(v___y_1957_);
v___x_1961_ = l_Lean_Name_mkStr2(v___y_1957_, v___x_1960_);
v___x_1962_ = l_Lean_Expr_const___override(v___x_1961_, v___x_1925_);
v___x_1963_ = l_Lean_mkAppB(v___x_1962_, v_typeExpr_1898_, v___y_1959_);
lean_inc_ref(v___x_1963_);
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___y_1958_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v_a_1930_ = v___x_1964_;
v_snd_1931_ = v___x_1963_;
goto v___jp_1929_;
}
v___jp_1965_:
{
return v___y_1966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___boxed(lean_object* v_typeExpr_2018_, lean_object* v_ev_2019_, lean_object* v_stx_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg(v_typeExpr_2018_, v_ev_2019_, v_stx_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_);
lean_dec(v_a_2026_);
lean_dec_ref(v_a_2025_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx(lean_object* v_00_u03b1_2029_, lean_object* v_typeExpr_2030_, lean_object* v_ev_2031_, lean_object* v_stx_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg(v_typeExpr_2030_, v_ev_2031_, v_stx_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___boxed(lean_object* v_00_u03b1_2041_, lean_object* v_typeExpr_2042_, lean_object* v_ev_2043_, lean_object* v_stx_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx(v_00_u03b1_2041_, v_typeExpr_2042_, v_ev_2043_, v_stx_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_);
lean_dec(v_a_2050_);
lean_dec_ref(v_a_2049_);
lean_dec(v_a_2048_);
lean_dec_ref(v_a_2047_);
lean_dec(v_a_2046_);
lean_dec_ref(v_a_2045_);
return v_res_2052_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2056_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_2057_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8);
v___x_2058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
lean_ctor_set(v___x_2058_, 1, v___x_2056_);
return v___x_2058_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2059_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2);
v___x_2060_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__1));
v___x_2061_ = l_Lean_Expr_const___override(v___x_2060_, v___x_2059_);
return v___x_2061_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2);
v___x_2082_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11));
v___x_2083_ = l_Lean_Expr_const___override(v___x_2082_, v___x_2081_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg(lean_object* v_typeExpr_2084_, lean_object* v_typeExpr_x27_2085_, lean_object* v_ev_2086_, lean_object* v_ev_x27_2087_, lean_object* v_stx_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v_fileName_2096_; lean_object* v_fileMap_2097_; lean_object* v_options_2098_; lean_object* v_currRecDepth_2099_; lean_object* v_maxRecDepth_2100_; lean_object* v_ref_2101_; lean_object* v_currNamespace_2102_; lean_object* v_openDecls_2103_; lean_object* v_initHeartbeats_2104_; lean_object* v_maxHeartbeats_2105_; lean_object* v_quotContext_2106_; lean_object* v_currMacroScope_2107_; uint8_t v_diag_2108_; lean_object* v_cancelTk_x3f_2109_; uint8_t v_suppressElabErrors_2110_; lean_object* v_inheritedTraceOptions_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v_a_2117_; lean_object* v_snd_2118_; lean_object* v___y_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v_fileName_2096_ = lean_ctor_get(v_a_2093_, 0);
v_fileMap_2097_ = lean_ctor_get(v_a_2093_, 1);
v_options_2098_ = lean_ctor_get(v_a_2093_, 2);
v_currRecDepth_2099_ = lean_ctor_get(v_a_2093_, 3);
v_maxRecDepth_2100_ = lean_ctor_get(v_a_2093_, 4);
v_ref_2101_ = lean_ctor_get(v_a_2093_, 5);
v_currNamespace_2102_ = lean_ctor_get(v_a_2093_, 6);
v_openDecls_2103_ = lean_ctor_get(v_a_2093_, 7);
v_initHeartbeats_2104_ = lean_ctor_get(v_a_2093_, 8);
v_maxHeartbeats_2105_ = lean_ctor_get(v_a_2093_, 9);
v_quotContext_2106_ = lean_ctor_get(v_a_2093_, 10);
v_currMacroScope_2107_ = lean_ctor_get(v_a_2093_, 11);
v_diag_2108_ = lean_ctor_get_uint8(v_a_2093_, sizeof(void*)*14);
v_cancelTk_x3f_2109_ = lean_ctor_get(v_a_2093_, 12);
v_suppressElabErrors_2110_ = lean_ctor_get_uint8(v_a_2093_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2111_ = lean_ctor_get(v_a_2093_, 13);
v___x_2112_ = lean_unsigned_to_nat(0u);
v___x_2113_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3);
lean_inc_ref(v_typeExpr_x27_2085_);
lean_inc_ref(v_typeExpr_2084_);
v___x_2114_ = l_Lean_mkAppB(v___x_2113_, v_typeExpr_2084_, v_typeExpr_x27_2085_);
v___x_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_inc(v_stx_2088_);
v___x_2145_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_2088_);
v___x_2146_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5));
lean_inc(v___x_2145_);
v___x_2147_ = l_Lean_Syntax_isOfKind(v___x_2145_, v___x_2146_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; 
lean_dec(v___x_2145_);
lean_dec_ref_known(v___x_2115_, 1);
lean_dec(v_stx_2088_);
lean_dec_ref(v_ev_x27_2087_);
lean_dec_ref(v_ev_2086_);
lean_dec_ref(v_typeExpr_x27_2085_);
lean_dec_ref(v_typeExpr_2084_);
v___x_2148_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2144_ = v___x_2148_;
goto v___jp_2143_;
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2149_ = l_Lean_Syntax_getArg(v___x_2145_, v___x_2112_);
v___x_2150_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7));
lean_inc(v___x_2149_);
v___x_2151_ = l_Lean_Syntax_isOfKind(v___x_2149_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; 
lean_dec(v___x_2149_);
lean_dec(v___x_2145_);
lean_dec_ref_known(v___x_2115_, 1);
lean_dec(v_stx_2088_);
lean_dec_ref(v_ev_x27_2087_);
lean_dec_ref(v_ev_2086_);
lean_dec_ref(v_typeExpr_x27_2085_);
lean_dec_ref(v_typeExpr_2084_);
v___x_2152_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2144_ = v___x_2152_;
goto v___jp_2143_;
}
else
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2153_ = lean_unsigned_to_nat(1u);
v___x_2154_ = l_Lean_Syntax_getArg(v___x_2149_, v___x_2153_);
lean_dec(v___x_2149_);
v___x_2155_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__9));
lean_inc(v___x_2154_);
v___x_2156_ = l_Lean_Syntax_isOfKind(v___x_2154_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; 
lean_dec(v___x_2154_);
lean_dec(v___x_2145_);
lean_dec_ref_known(v___x_2115_, 1);
lean_dec(v_stx_2088_);
lean_dec_ref(v_ev_x27_2087_);
lean_dec_ref(v_ev_2086_);
lean_dec_ref(v_typeExpr_x27_2085_);
lean_dec_ref(v_typeExpr_2084_);
v___x_2157_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2144_ = v___x_2157_;
goto v___jp_2143_;
}
else
{
lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; 
v___x_2158_ = l_Lean_Syntax_getArg(v___x_2154_, v___x_2112_);
lean_dec(v___x_2154_);
v___x_2159_ = lean_box(0);
v___x_2160_ = l_Lean_Syntax_matchesIdent(v___x_2158_, v___x_2159_);
lean_dec(v___x_2158_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; 
lean_dec(v___x_2145_);
lean_dec_ref_known(v___x_2115_, 1);
lean_dec(v_stx_2088_);
lean_dec_ref(v_ev_x27_2087_);
lean_dec_ref(v_ev_2086_);
lean_dec_ref(v_typeExpr_x27_2085_);
lean_dec_ref(v_typeExpr_2084_);
v___x_2161_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2144_ = v___x_2161_;
goto v___jp_2143_;
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2162_ = l_Lean_Syntax_getArg(v___x_2145_, v___x_2153_);
lean_dec(v___x_2145_);
v___x_2163_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_2162_);
v___x_2164_ = l_Lean_Syntax_matchesNull(v___x_2162_, v___x_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; 
lean_dec(v___x_2162_);
lean_dec_ref_known(v___x_2115_, 1);
lean_dec(v_stx_2088_);
lean_dec_ref(v_ev_x27_2087_);
lean_dec_ref(v_ev_2086_);
lean_dec_ref(v_typeExpr_x27_2085_);
lean_dec_ref(v_typeExpr_2084_);
v___x_2165_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2144_ = v___x_2165_;
goto v___jp_2143_;
}
else
{
lean_object* v___x_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2166_ = lean_unsigned_to_nat(2u);
v___x_2167_ = l_Lean_Syntax_getArg(v___x_2162_, v___x_2166_);
lean_inc(v___x_2167_);
v___x_2168_ = l_Lean_Syntax_matchesNull(v___x_2167_, v___x_2153_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; 
lean_dec(v___x_2167_);
lean_dec(v___x_2162_);
lean_dec_ref_known(v___x_2115_, 1);
lean_dec(v_stx_2088_);
lean_dec_ref(v_ev_x27_2087_);
lean_dec_ref(v_ev_2086_);
lean_dec_ref(v_typeExpr_x27_2085_);
lean_dec_ref(v_typeExpr_2084_);
v___x_2169_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2144_ = v___x_2169_;
goto v___jp_2143_;
}
else
{
lean_object* v_ref_2170_; lean_object* v___x_2171_; lean_object* v_x_2172_; lean_object* v___x_2173_; 
v_ref_2170_ = l_Lean_replaceRef(v_stx_2088_, v_ref_2101_);
lean_inc_ref(v_inheritedTraceOptions_2111_);
lean_inc(v_cancelTk_x3f_2109_);
lean_inc(v_currMacroScope_2107_);
lean_inc(v_quotContext_2106_);
lean_inc(v_maxHeartbeats_2105_);
lean_inc(v_initHeartbeats_2104_);
lean_inc(v_openDecls_2103_);
lean_inc(v_currNamespace_2102_);
lean_inc(v_maxRecDepth_2100_);
lean_inc(v_currRecDepth_2099_);
lean_inc_ref(v_options_2098_);
lean_inc_ref(v_fileMap_2097_);
lean_inc_ref(v_fileName_2096_);
v___x_2171_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2171_, 0, v_fileName_2096_);
lean_ctor_set(v___x_2171_, 1, v_fileMap_2097_);
lean_ctor_set(v___x_2171_, 2, v_options_2098_);
lean_ctor_set(v___x_2171_, 3, v_currRecDepth_2099_);
lean_ctor_set(v___x_2171_, 4, v_maxRecDepth_2100_);
lean_ctor_set(v___x_2171_, 5, v_ref_2170_);
lean_ctor_set(v___x_2171_, 6, v_currNamespace_2102_);
lean_ctor_set(v___x_2171_, 7, v_openDecls_2103_);
lean_ctor_set(v___x_2171_, 8, v_initHeartbeats_2104_);
lean_ctor_set(v___x_2171_, 9, v_maxHeartbeats_2105_);
lean_ctor_set(v___x_2171_, 10, v_quotContext_2106_);
lean_ctor_set(v___x_2171_, 11, v_currMacroScope_2107_);
lean_ctor_set(v___x_2171_, 12, v_cancelTk_x3f_2109_);
lean_ctor_set(v___x_2171_, 13, v_inheritedTraceOptions_2111_);
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*14, v_diag_2108_);
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*14 + 1, v_suppressElabErrors_2110_);
v_x_2172_ = l_Lean_Syntax_getArg(v___x_2162_, v___x_2112_);
lean_dec(v___x_2162_);
lean_inc(v_a_2094_);
lean_inc_ref(v___x_2171_);
lean_inc(v_a_2092_);
lean_inc_ref(v_a_2091_);
lean_inc(v_a_2090_);
lean_inc_ref(v_a_2089_);
v___x_2173_ = lean_apply_8(v_ev_2086_, v_x_2172_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v___x_2171_, v_a_2094_, lean_box(0));
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v_fst_2175_; lean_object* v_snd_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2205_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2173_, 1);
v_fst_2175_ = lean_ctor_get(v_a_2174_, 0);
v_snd_2176_ = lean_ctor_get(v_a_2174_, 1);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_a_2174_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2178_ = v_a_2174_;
v_isShared_2179_ = v_isSharedCheck_2205_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_snd_2176_);
lean_inc(v_fst_2175_);
lean_dec(v_a_2174_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2205_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v_x_x27_2180_; lean_object* v___x_2181_; 
v_x_x27_2180_ = l_Lean_Syntax_getArg(v___x_2167_, v___x_2112_);
lean_dec(v___x_2167_);
lean_inc(v_a_2094_);
lean_inc(v_a_2092_);
lean_inc_ref(v_a_2091_);
lean_inc(v_a_2090_);
lean_inc_ref(v_a_2089_);
v___x_2181_ = lean_apply_8(v_ev_x27_2087_, v_x_x27_2180_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v___x_2171_, v_a_2094_, lean_box(0));
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v_fst_2183_; lean_object* v_snd_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2196_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
lean_dec_ref_known(v___x_2181_, 1);
v_fst_2183_ = lean_ctor_get(v_a_2182_, 0);
v_snd_2184_ = lean_ctor_get(v_a_2182_, 1);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_a_2182_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2186_ = v_a_2182_;
v_isShared_2187_ = v_isSharedCheck_2196_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_snd_2184_);
lean_inc(v_fst_2183_);
lean_dec(v_a_2182_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2196_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 1, v_fst_2183_);
lean_ctor_set(v___x_2186_, 0, v_fst_2175_);
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_fst_2175_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_fst_2183_);
v___x_2189_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2193_; 
v___x_2190_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12, &l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12);
v___x_2191_ = l_Lean_mkApp4(v___x_2190_, v_typeExpr_2084_, v_typeExpr_x27_2085_, v_snd_2176_, v_snd_2184_);
lean_inc_ref(v___x_2191_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 1, v___x_2191_);
lean_ctor_set(v___x_2178_, 0, v___x_2189_);
v___x_2193_ = v___x_2178_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v___x_2191_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
v_a_2117_ = v___x_2193_;
v_snd_2118_ = v___x_2191_;
goto v___jp_2116_;
}
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_del_object(v___x_2178_);
lean_dec(v_snd_2176_);
lean_dec(v_fst_2175_);
lean_dec_ref_known(v___x_2115_, 1);
lean_dec(v_stx_2088_);
lean_dec_ref(v_typeExpr_x27_2085_);
lean_dec_ref(v_typeExpr_2084_);
v_a_2197_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2181_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2181_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec_ref_known(v___x_2171_, 14);
lean_dec(v___x_2167_);
lean_dec_ref_known(v___x_2115_, 1);
lean_dec(v_stx_2088_);
lean_dec_ref(v_ev_x27_2087_);
lean_dec_ref(v_typeExpr_x27_2085_);
lean_dec_ref(v_typeExpr_2084_);
v_a_2206_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2173_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2173_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
}
}
}
}
v___jp_2116_:
{
lean_object* v___x_2119_; lean_object* v_infoState_2120_; uint8_t v_enabled_2121_; 
v___x_2119_ = lean_st_ref_get(v_a_2094_);
v_infoState_2120_ = lean_ctor_get(v___x_2119_, 7);
lean_inc_ref(v_infoState_2120_);
lean_dec(v___x_2119_);
v_enabled_2121_ = lean_ctor_get_uint8(v_infoState_2120_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2120_);
if (v_enabled_2121_ == 0)
{
lean_object* v___x_2122_; 
lean_dec_ref(v_snd_2118_);
lean_dec_ref_known(v___x_2115_, 1);
lean_dec(v_stx_2088_);
v___x_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2122_, 0, v_a_2117_);
return v___x_2122_;
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; lean_object* v___x_2126_; 
v___x_2123_ = lean_box(0);
v___x_2124_ = lean_box(0);
v___x_2125_ = 0;
v___x_2126_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_2088_, v_snd_2118_, v___x_2115_, v___x_2123_, v___x_2124_, v___x_2125_, v___x_2125_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; 
v_unused_2134_ = lean_ctor_get(v___x_2126_, 0);
lean_dec(v_unused_2134_);
v___x_2128_ = v___x_2126_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_dec(v___x_2126_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v_a_2117_);
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2117_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec_ref(v_a_2117_);
v_a_2135_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2126_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2126_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
v___jp_2143_:
{
return v___y_2144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___boxed(lean_object* v_typeExpr_2214_, lean_object* v_typeExpr_x27_2215_, lean_object* v_ev_2216_, lean_object* v_ev_x27_2217_, lean_object* v_stx_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg(v_typeExpr_2214_, v_typeExpr_x27_2215_, v_ev_2216_, v_ev_x27_2217_, v_stx_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx(lean_object* v_00_u03b1_2227_, lean_object* v_00_u03b1_x27_2228_, lean_object* v_typeExpr_2229_, lean_object* v_typeExpr_x27_2230_, lean_object* v_ev_2231_, lean_object* v_ev_x27_2232_, lean_object* v_stx_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg(v_typeExpr_2229_, v_typeExpr_x27_2230_, v_ev_2231_, v_ev_x27_2232_, v_stx_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___boxed(lean_object* v_00_u03b1_2242_, lean_object* v_00_u03b1_x27_2243_, lean_object* v_typeExpr_2244_, lean_object* v_typeExpr_x27_2245_, lean_object* v_ev_2246_, lean_object* v_ev_x27_2247_, lean_object* v_stx_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx(v_00_u03b1_2242_, v_00_u03b1_x27_2243_, v_typeExpr_2244_, v_typeExpr_x27_2245_, v_ev_2246_, v_ev_x27_2247_, v_stx_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_object* v_00_u03b1_2257_, lean_object* v_c_2258_, lean_object* v_f_2259_, lean_object* v_x_2260_){
_start:
{
lean_object* v_fst_2261_; lean_object* v_snd_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2273_; 
v_fst_2261_ = lean_ctor_get(v_x_2260_, 0);
v_snd_2262_ = lean_ctor_get(v_x_2260_, 1);
v_isSharedCheck_2273_ = !lean_is_exclusive(v_x_2260_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2264_ = v_x_2260_;
v_isShared_2265_ = v_isSharedCheck_2273_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_snd_2262_);
lean_inc(v_fst_2261_);
lean_dec(v_x_2260_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2273_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2266_ = lean_apply_1(v_f_2259_, v_fst_2261_);
v___x_2267_ = lean_box(0);
v___x_2268_ = l_Lean_Expr_const___override(v_c_2258_, v___x_2267_);
v___x_2269_ = l_Lean_Expr_app___override(v___x_2268_, v_snd_2262_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 1, v___x_2269_);
lean_ctor_set(v___x_2264_, 0, v___x_2266_);
v___x_2271_ = v___x_2264_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v___x_2269_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1(uint8_t v_v_2274_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2275_, 0, v_v_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1___boxed(lean_object* v_v_2276_){
_start:
{
uint8_t v_v_boxed_2277_; lean_object* v_res_2278_; 
v_v_boxed_2277_ = lean_unbox(v_v_2276_);
v_res_2278_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1(v_v_boxed_2277_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__2(lean_object* v_v_2279_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2280_, 0, v_v_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__3(lean_object* v_v_2281_){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2282_, 0, v_v_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__4(lean_object* v_v_2283_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2284_, 0, v_v_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__5(lean_object* v_v_2285_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2286_, 0, v_v_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx(lean_object* v_stx_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v___y_2327_; lean_object* v___y_2328_; uint8_t v___y_2329_; lean_object* v___x_2340_; 
v___x_2340_ = l_Lean_Meta_saveState___redArg(v_a_2322_, v_a_2324_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2342_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
lean_inc(v_stx_2318_);
v___x_2342_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx(v_stx_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2353_; 
lean_dec(v_a_2341_);
lean_dec(v_stx_2318_);
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2353_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2353_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___f_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___f_2347_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__1));
v___x_2348_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3));
v___x_2349_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_box(0), v___x_2348_, v___f_2347_, v_a_2343_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___x_2349_);
v___x_2351_ = v___x_2345_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2541_; 
v_a_2354_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2356_ = v___x_2342_;
v_isShared_2357_ = v_isSharedCheck_2541_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2342_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2541_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___f_2358_; lean_object* v___f_2359_; lean_object* v___f_2360_; lean_object* v___y_2362_; lean_object* v___y_2363_; uint8_t v___y_2364_; lean_object* v___y_2406_; lean_object* v___y_2407_; uint8_t v___y_2408_; lean_object* v___f_2449_; lean_object* v___y_2451_; lean_object* v___y_2452_; uint8_t v___y_2453_; lean_object* v___x_2495_; 
v___f_2358_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__4));
v___f_2359_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__5));
v___f_2360_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__6));
v___f_2449_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__11));
lean_inc(v_a_2354_);
if (v_isShared_2357_ == 0)
{
v___x_2495_ = v___x_2356_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2354_);
v___x_2495_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2494_;
}
v___jp_2361_:
{
if (v___y_2364_ == 0)
{
lean_object* v___x_2365_; 
lean_dec_ref(v___y_2362_);
v___x_2365_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2363_, v_a_2322_, v_a_2324_);
lean_dec_ref(v___y_2363_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v___x_2366_; 
lean_dec_ref_known(v___x_2365_, 1);
v___x_2366_ = l_Lean_Meta_saveState___redArg(v_a_2322_, v_a_2324_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2368_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx(v_stx_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2378_; 
lean_dec(v_a_2367_);
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2371_ = v___x_2368_;
v_isShared_2372_ = v_isSharedCheck_2378_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2368_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2378_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2376_; 
v___x_2373_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8));
v___x_2374_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_box(0), v___x_2373_, v___f_2360_, v_a_2369_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v___x_2374_);
v___x_2376_ = v___x_2371_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2388_; 
v_a_2379_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2381_ = v___x_2368_;
v_isShared_2382_ = v_isSharedCheck_2388_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2368_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2388_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
lean_inc(v_a_2379_);
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
uint8_t v___x_2385_; 
v___x_2385_ = l_Lean_Exception_isInterrupt(v_a_2379_);
if (v___x_2385_ == 0)
{
uint8_t v___x_2386_; 
v___x_2386_ = l_Lean_Exception_isRuntime(v_a_2379_);
v___y_2327_ = v___x_2384_;
v___y_2328_ = v_a_2367_;
v___y_2329_ = v___x_2386_;
goto v___jp_2326_;
}
else
{
lean_dec(v_a_2379_);
v___y_2327_ = v___x_2384_;
v___y_2328_ = v_a_2367_;
v___y_2329_ = v___x_2385_;
goto v___jp_2326_;
}
}
}
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec(v_stx_2318_);
v_a_2389_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2366_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2366_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec(v_stx_2318_);
v_a_2397_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2365_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2365_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
else
{
lean_dec_ref(v___y_2363_);
lean_dec(v_stx_2318_);
return v___y_2362_;
}
}
v___jp_2405_:
{
if (v___y_2408_ == 0)
{
lean_object* v___x_2409_; 
lean_dec_ref(v___y_2406_);
v___x_2409_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2407_, v_a_2322_, v_a_2324_);
lean_dec_ref(v___y_2407_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v___x_2410_; 
lean_dec_ref_known(v___x_2409_, 1);
v___x_2410_ = l_Lean_Meta_saveState___redArg(v_a_2322_, v_a_2324_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2412_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2411_);
lean_dec_ref_known(v___x_2410_, 1);
lean_inc(v_stx_2318_);
v___x_2412_ = l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx(v_stx_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2422_; 
lean_dec(v_a_2411_);
lean_dec(v_stx_2318_);
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2415_ = v___x_2412_;
v_isShared_2416_ = v_isSharedCheck_2422_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2412_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2422_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2420_; 
v___x_2417_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10));
v___x_2418_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_box(0), v___x_2417_, v___f_2359_, v_a_2413_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 0, v___x_2418_);
v___x_2420_ = v___x_2415_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2418_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2432_; 
v_a_2423_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2425_ = v___x_2412_;
v_isShared_2426_ = v_isSharedCheck_2432_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2412_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2432_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
lean_inc(v_a_2423_);
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
uint8_t v___x_2429_; 
v___x_2429_ = l_Lean_Exception_isInterrupt(v_a_2423_);
if (v___x_2429_ == 0)
{
uint8_t v___x_2430_; 
v___x_2430_ = l_Lean_Exception_isRuntime(v_a_2423_);
v___y_2362_ = v___x_2428_;
v___y_2363_ = v_a_2411_;
v___y_2364_ = v___x_2430_;
goto v___jp_2361_;
}
else
{
lean_dec(v_a_2423_);
v___y_2362_ = v___x_2428_;
v___y_2363_ = v_a_2411_;
v___y_2364_ = v___x_2429_;
goto v___jp_2361_;
}
}
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec(v_stx_2318_);
v_a_2433_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2410_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2410_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
lean_dec(v_stx_2318_);
v_a_2441_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2409_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2409_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
else
{
lean_dec_ref(v___y_2407_);
lean_dec(v_stx_2318_);
return v___y_2406_;
}
}
v___jp_2450_:
{
if (v___y_2453_ == 0)
{
lean_object* v___x_2454_; 
lean_dec_ref(v___y_2451_);
v___x_2454_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2452_, v_a_2322_, v_a_2324_);
lean_dec_ref(v___y_2452_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v___x_2455_; 
lean_dec_ref_known(v___x_2454_, 1);
v___x_2455_ = l_Lean_Meta_saveState___redArg(v_a_2322_, v_a_2324_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2457_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2455_, 1);
lean_inc(v_stx_2318_);
v___x_2457_ = l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx(v_stx_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2467_; 
lean_dec(v_a_2456_);
lean_dec(v_stx_2318_);
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2460_ = v___x_2457_;
v_isShared_2461_ = v_isSharedCheck_2467_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2457_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2467_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
v___x_2462_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13));
v___x_2463_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_box(0), v___x_2462_, v___f_2449_, v_a_2458_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v___x_2463_);
v___x_2465_ = v___x_2460_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2477_; 
v_a_2468_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2470_ = v___x_2457_;
v_isShared_2471_ = v_isSharedCheck_2477_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2457_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2477_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
lean_inc(v_a_2468_);
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
uint8_t v___x_2474_; 
v___x_2474_ = l_Lean_Exception_isInterrupt(v_a_2468_);
if (v___x_2474_ == 0)
{
uint8_t v___x_2475_; 
v___x_2475_ = l_Lean_Exception_isRuntime(v_a_2468_);
v___y_2406_ = v___x_2473_;
v___y_2407_ = v_a_2456_;
v___y_2408_ = v___x_2475_;
goto v___jp_2405_;
}
else
{
lean_dec(v_a_2468_);
v___y_2406_ = v___x_2473_;
v___y_2407_ = v_a_2456_;
v___y_2408_ = v___x_2474_;
goto v___jp_2405_;
}
}
}
}
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec(v_stx_2318_);
v_a_2478_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2455_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2455_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec(v_stx_2318_);
v_a_2486_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2454_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2454_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
else
{
lean_dec_ref(v___y_2452_);
lean_dec(v_stx_2318_);
return v___y_2451_;
}
}
v_reusejp_2494_:
{
uint8_t v___y_2497_; uint8_t v___x_2538_; 
v___x_2538_ = l_Lean_Exception_isInterrupt(v_a_2354_);
if (v___x_2538_ == 0)
{
uint8_t v___x_2539_; 
v___x_2539_ = l_Lean_Exception_isRuntime(v_a_2354_);
v___y_2497_ = v___x_2539_;
goto v___jp_2496_;
}
else
{
lean_dec(v_a_2354_);
v___y_2497_ = v___x_2538_;
goto v___jp_2496_;
}
v___jp_2496_:
{
if (v___y_2497_ == 0)
{
lean_object* v___x_2498_; 
lean_dec_ref(v___x_2495_);
v___x_2498_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2341_, v_a_2322_, v_a_2324_);
lean_dec(v_a_2341_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v___x_2499_; 
lean_dec_ref_known(v___x_2498_, 1);
v___x_2499_ = l_Lean_Meta_saveState___redArg(v_a_2322_, v_a_2324_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2501_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2499_, 1);
lean_inc(v_stx_2318_);
v___x_2501_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(v_stx_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2511_; 
lean_dec(v_a_2500_);
lean_dec(v_stx_2318_);
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2504_ = v___x_2501_;
v_isShared_2505_ = v_isSharedCheck_2511_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2501_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2511_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2506_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15));
v___x_2507_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_box(0), v___x_2506_, v___f_2358_, v_a_2502_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 0, v___x_2507_);
v___x_2509_ = v___x_2504_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2521_; 
v_a_2512_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2514_ = v___x_2501_;
v_isShared_2515_ = v_isSharedCheck_2521_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2501_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2521_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
lean_inc(v_a_2512_);
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
uint8_t v___x_2518_; 
v___x_2518_ = l_Lean_Exception_isInterrupt(v_a_2512_);
if (v___x_2518_ == 0)
{
uint8_t v___x_2519_; 
v___x_2519_ = l_Lean_Exception_isRuntime(v_a_2512_);
v___y_2451_ = v___x_2517_;
v___y_2452_ = v_a_2500_;
v___y_2453_ = v___x_2519_;
goto v___jp_2450_;
}
else
{
lean_dec(v_a_2512_);
v___y_2451_ = v___x_2517_;
v___y_2452_ = v_a_2500_;
v___y_2453_ = v___x_2518_;
goto v___jp_2450_;
}
}
}
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec(v_stx_2318_);
v_a_2522_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2499_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2499_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_dec(v_stx_2318_);
v_a_2530_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2498_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2498_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
else
{
lean_dec(v_a_2341_);
lean_dec(v_stx_2318_);
return v___x_2495_;
}
}
}
}
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec(v_stx_2318_);
v_a_2542_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2340_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2340_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
v___jp_2326_:
{
if (v___y_2329_ == 0)
{
lean_object* v___x_2330_; 
lean_dec_ref(v___y_2327_);
v___x_2330_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2328_, v_a_2322_, v_a_2324_);
lean_dec_ref(v___y_2328_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v___x_2331_; 
lean_dec_ref_known(v___x_2330_, 1);
v___x_2331_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
return v___x_2331_;
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
v_a_2332_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2330_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2330_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
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
else
{
lean_dec_ref(v___y_2328_);
return v___y_2327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___boxed(lean_object* v_stx_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx(v_stx_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
lean_dec(v_a_2556_);
lean_dec_ref(v_a_2555_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
return v_res_2558_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1(void){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2560_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2);
v___x_2561_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__0));
v___x_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
lean_ctor_set(v___x_2562_, 1, v___x_2560_);
return v___x_2562_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instBool(void){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1);
return v___x_2563_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1(void){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2565_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2);
v___x_2566_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__0));
v___x_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
lean_ctor_set(v___x_2567_, 1, v___x_2565_);
return v___x_2567_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instNat(void){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1);
return v___x_2568_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1(void){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2570_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2);
v___x_2571_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__0));
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
lean_ctor_set(v___x_2572_, 1, v___x_2570_);
return v___x_2572_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instInt(void){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1);
return v___x_2573_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1(void){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2575_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2);
v___x_2576_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__0));
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
lean_ctor_set(v___x_2577_, 1, v___x_2575_);
return v___x_2577_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instString(void){
_start:
{
lean_object* v___x_2578_; 
v___x_2578_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1);
return v___x_2578_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1(void){
_start:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2580_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2);
v___x_2581_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__0));
v___x_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
lean_ctor_set(v___x_2582_, 1, v___x_2580_);
return v___x_2582_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instName(void){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instOption___redArg(lean_object* v_inst_2584_){
_start:
{
lean_object* v_evalTerm_2585_; lean_object* v_typeExpr_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2596_; 
v_evalTerm_2585_ = lean_ctor_get(v_inst_2584_, 0);
v_typeExpr_2586_ = lean_ctor_get(v_inst_2584_, 1);
v_isSharedCheck_2596_ = !lean_is_exclusive(v_inst_2584_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2588_ = v_inst_2584_;
v_isShared_2589_ = v_isSharedCheck_2596_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_typeExpr_2586_);
lean_inc(v_evalTerm_2585_);
lean_dec(v_inst_2584_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2596_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2594_; 
lean_inc_ref(v_typeExpr_2586_);
v___x_2590_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___boxed), 11, 3);
lean_closure_set(v___x_2590_, 0, lean_box(0));
lean_closure_set(v___x_2590_, 1, v_typeExpr_2586_);
lean_closure_set(v___x_2590_, 2, v_evalTerm_2585_);
v___x_2591_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2);
v___x_2592_ = l_Lean_Expr_app___override(v___x_2591_, v_typeExpr_2586_);
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 1, v___x_2592_);
lean_ctor_set(v___x_2588_, 0, v___x_2590_);
v___x_2594_ = v___x_2588_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2590_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instOption(lean_object* v_00_u03b1_2597_, lean_object* v_inst_2598_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Lean_Elab_ConfigEval_EvalTerm_instOption___redArg(v_inst_2598_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instList___redArg(lean_object* v_inst_2600_){
_start:
{
lean_object* v_evalTerm_2601_; lean_object* v_typeExpr_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2612_; 
v_evalTerm_2601_ = lean_ctor_get(v_inst_2600_, 0);
v_typeExpr_2602_ = lean_ctor_get(v_inst_2600_, 1);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_inst_2600_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2604_ = v_inst_2600_;
v_isShared_2605_ = v_isSharedCheck_2612_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_typeExpr_2602_);
lean_inc(v_evalTerm_2601_);
lean_dec(v_inst_2600_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2612_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2610_; 
lean_inc_ref(v_typeExpr_2602_);
v___x_2606_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___boxed), 11, 3);
lean_closure_set(v___x_2606_, 0, lean_box(0));
lean_closure_set(v___x_2606_, 1, v_typeExpr_2602_);
lean_closure_set(v___x_2606_, 2, v_evalTerm_2601_);
v___x_2607_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1);
v___x_2608_ = l_Lean_Expr_app___override(v___x_2607_, v_typeExpr_2602_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 1, v___x_2608_);
lean_ctor_set(v___x_2604_, 0, v___x_2606_);
v___x_2610_ = v___x_2604_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2606_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instList(lean_object* v_00_u03b1_2613_, lean_object* v_inst_2614_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_Elab_ConfigEval_EvalTerm_instList___redArg(v_inst_2614_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instArray___redArg(lean_object* v_inst_2616_){
_start:
{
lean_object* v_evalTerm_2617_; lean_object* v_typeExpr_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2628_; 
v_evalTerm_2617_ = lean_ctor_get(v_inst_2616_, 0);
v_typeExpr_2618_ = lean_ctor_get(v_inst_2616_, 1);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_inst_2616_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2620_ = v_inst_2616_;
v_isShared_2621_ = v_isSharedCheck_2628_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_typeExpr_2618_);
lean_inc(v_evalTerm_2617_);
lean_dec(v_inst_2616_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2628_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
lean_inc_ref(v_typeExpr_2618_);
v___x_2622_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___boxed), 11, 3);
lean_closure_set(v___x_2622_, 0, lean_box(0));
lean_closure_set(v___x_2622_, 1, v_typeExpr_2618_);
lean_closure_set(v___x_2622_, 2, v_evalTerm_2617_);
v___x_2623_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2);
v___x_2624_ = l_Lean_Expr_app___override(v___x_2623_, v_typeExpr_2618_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 1, v___x_2624_);
lean_ctor_set(v___x_2620_, 0, v___x_2622_);
v___x_2626_ = v___x_2620_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instArray(lean_object* v_00_u03b1_2629_, lean_object* v_inst_2630_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_Elab_ConfigEval_EvalTerm_instArray___redArg(v_inst_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instProd___redArg(lean_object* v_inst_2632_, lean_object* v_inst_2633_){
_start:
{
lean_object* v_evalTerm_2634_; lean_object* v_typeExpr_2635_; lean_object* v_evalTerm_2636_; lean_object* v_typeExpr_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2647_; 
v_evalTerm_2634_ = lean_ctor_get(v_inst_2632_, 0);
lean_inc_ref(v_evalTerm_2634_);
v_typeExpr_2635_ = lean_ctor_get(v_inst_2632_, 1);
lean_inc_ref(v_typeExpr_2635_);
lean_dec_ref(v_inst_2632_);
v_evalTerm_2636_ = lean_ctor_get(v_inst_2633_, 0);
v_typeExpr_2637_ = lean_ctor_get(v_inst_2633_, 1);
v_isSharedCheck_2647_ = !lean_is_exclusive(v_inst_2633_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2639_ = v_inst_2633_;
v_isShared_2640_ = v_isSharedCheck_2647_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_typeExpr_2637_);
lean_inc(v_evalTerm_2636_);
lean_dec(v_inst_2633_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2647_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2645_; 
lean_inc_ref(v_typeExpr_2637_);
lean_inc_ref(v_typeExpr_2635_);
v___x_2641_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___boxed), 14, 6);
lean_closure_set(v___x_2641_, 0, lean_box(0));
lean_closure_set(v___x_2641_, 1, lean_box(0));
lean_closure_set(v___x_2641_, 2, v_typeExpr_2635_);
lean_closure_set(v___x_2641_, 3, v_typeExpr_2637_);
lean_closure_set(v___x_2641_, 4, v_evalTerm_2634_);
lean_closure_set(v___x_2641_, 5, v_evalTerm_2636_);
v___x_2642_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3);
v___x_2643_ = l_Lean_mkAppB(v___x_2642_, v_typeExpr_2635_, v_typeExpr_2637_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 1, v___x_2643_);
lean_ctor_set(v___x_2639_, 0, v___x_2641_);
v___x_2645_ = v___x_2639_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2641_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instProd(lean_object* v_00_u03b1_2648_, lean_object* v_00_u03b1_x27_2649_, lean_object* v_inst_2650_, lean_object* v_inst_2651_){
_start:
{
lean_object* v___x_2652_; 
v___x_2652_ = l_Lean_Elab_ConfigEval_EvalTerm_instProd___redArg(v_inst_2650_, v_inst_2651_);
return v___x_2652_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2(void){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2657_ = lean_box(0);
v___x_2658_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1));
v___x_2659_ = l_Lean_Expr_const___override(v___x_2658_, v___x_2657_);
return v___x_2659_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3(void){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2660_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2);
v___x_2661_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__0));
v___x_2662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
lean_ctor_set(v___x_2662_, 1, v___x_2660_);
return v___x_2662_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue(void){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3);
return v___x_2663_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2664_ = lean_box(0);
v___x_2665_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_2666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
lean_ctor_set(v___x_2666_, 1, v___x_2664_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg(){
_start:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2668_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0);
v___x_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___boxed(lean_object* v___y_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0(lean_object* v_00_u03b1_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___boxed(lean_object* v_00_u03b1_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0(v_00_u03b1_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore(lean_object* v_e_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
v___x_2692_ = l_Lean_Expr_cleanupAnnotations(v_e_2686_);
v___x_2693_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8));
v___x_2694_ = l_Lean_Expr_isConstOf(v___x_2692_, v___x_2693_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2695_; uint8_t v___x_2696_; 
v___x_2695_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5));
v___x_2696_ = l_Lean_Expr_isConstOf(v___x_2692_, v___x_2695_);
lean_dec_ref(v___x_2692_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_2697_;
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = lean_box(v___x_2696_);
v___x_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
return v___x_2699_;
}
}
else
{
uint8_t v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
lean_dec_ref(v___x_2692_);
v___x_2700_ = 0;
v___x_2701_ = lean_box(v___x_2700_);
v___x_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
return v___x_2702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore___boxed(lean_object* v_e_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore(v_e_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
lean_dec(v_a_2707_);
lean_dec_ref(v_a_2706_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
return v_res_2709_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2(void){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__1));
v___x_2713_ = l_Lean_stringToMessageData(v___x_2712_);
return v___x_2713_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3(void){
_start:
{
uint8_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2714_ = 0;
v___x_2715_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__1));
v___x_2716_ = l_Lean_MessageData_ofConstName(v___x_2715_, v___x_2714_);
return v___x_2716_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2717_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3);
v___x_2718_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_2719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
lean_ctor_set(v___x_2719_, 1, v___x_2717_);
return v___x_2719_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6(void){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2721_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__5));
v___x_2722_ = l_Lean_stringToMessageData(v___x_2721_);
return v___x_2722_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7(void){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2723_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_2724_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4);
v___x_2725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
lean_ctor_set(v___x_2725_, 1, v___x_2723_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(lean_object* v_e_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_){
_start:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2732_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__0));
v___x_2733_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7);
v___x_2734_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_2732_, v_e_2726_, v___x_2733_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___boxed(lean_object* v_e_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v_e_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_);
lean_dec(v_a_2739_);
lean_dec_ref(v_a_2738_);
lean_dec(v_a_2737_);
lean_dec_ref(v_a_2736_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(lean_object* v_e_2742_){
_start:
{
lean_object* v___y_2745_; lean_object* v___x_2755_; 
lean_inc_ref(v_e_2742_);
v___x_2755_ = l_Lean_Expr_nat_x3f(v_e_2742_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Lean_Expr_rawNatLit_x3f(v_e_2742_);
v___y_2745_ = v___x_2756_;
goto v___jp_2744_;
}
else
{
lean_dec_ref(v_e_2742_);
v___y_2745_ = v___x_2755_;
goto v___jp_2744_;
}
v___jp_2744_:
{
if (lean_obj_tag(v___y_2745_) == 0)
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_2746_;
}
else
{
lean_object* v_val_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
v_val_2747_ = lean_ctor_get(v___y_2745_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___y_2745_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___y_2745_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_val_2747_);
lean_dec(v___y_2745_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
lean_ctor_set_tag(v___x_2749_, 0);
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_val_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg___boxed(lean_object* v_e_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(v_e_2757_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore(lean_object* v_e_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(v_e_2760_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___boxed(lean_object* v_e_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore(v_e_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
return v_res_2773_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1(void){
_start:
{
uint8_t v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2775_ = 0;
v___x_2776_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__1));
v___x_2777_ = l_Lean_MessageData_ofConstName(v___x_2776_, v___x_2775_);
return v___x_2777_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2(void){
_start:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2778_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1);
v___x_2779_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_2780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
lean_ctor_set(v___x_2780_, 1, v___x_2778_);
return v___x_2780_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3(void){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2781_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_2782_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2);
v___x_2783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
lean_ctor_set(v___x_2783_, 1, v___x_2781_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(lean_object* v_e_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2790_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__0));
v___x_2791_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3, &l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3);
v___x_2792_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_2790_, v_e_2784_, v___x_2791_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___boxed(lean_object* v_e_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v_e_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
lean_dec(v_a_2797_);
lean_dec_ref(v_a_2796_);
lean_dec(v_a_2795_);
lean_dec_ref(v_a_2794_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(lean_object* v_msg_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_ref_2806_; lean_object* v___x_2807_; lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2816_; 
v_ref_2806_ = lean_ctor_get(v___y_2803_, 5);
v___x_2807_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6(v_msg_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2810_ = v___x_2807_;
v_isShared_2811_ = v_isSharedCheck_2816_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2807_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2816_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2812_; lean_object* v___x_2814_; 
lean_inc(v_ref_2806_);
v___x_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2812_, 0, v_ref_2806_);
lean_ctor_set(v___x_2812_, 1, v_a_2808_);
if (v_isShared_2811_ == 0)
{
lean_ctor_set_tag(v___x_2810_, 1);
lean_ctor_set(v___x_2810_, 0, v___x_2812_);
v___x_2814_ = v___x_2810_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2812_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg___boxed(lean_object* v_msg_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(v_msg_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
return v_res_2823_;
}
}
static lean_object* _init_l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = ((lean_object*)(l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__0));
v___x_2826_ = l_Lean_stringToMessageData(v___x_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg(lean_object* v_x_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
if (lean_obj_tag(v_x_2827_) == 0)
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = lean_obj_once(&l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1, &l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1_once, _init_l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1);
v___x_2834_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(v___x_2833_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
return v___x_2834_;
}
else
{
lean_object* v_val_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
v_val_2835_ = lean_ctor_get(v_x_2827_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_x_2827_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v_x_2827_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_val_2835_);
lean_dec(v_x_2827_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set_tag(v___x_2837_, 0);
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_val_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___boxed(lean_object* v_x_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg(v_x_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore(lean_object* v_e_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_){
_start:
{
lean_object* v___y_2864_; lean_object* v___y_2865_; uint8_t v___y_2866_; lean_object* v___x_2922_; 
v___x_2922_ = l_Lean_Meta_saveState___redArg(v_a_2859_, v_a_2861_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref_known(v___x_2922_, 1);
lean_inc_ref(v_e_2857_);
v___x_2924_ = l_Lean_Expr_int_x3f(v_e_2857_);
v___x_2925_ = l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg(v___x_2924_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_dec(v_a_2923_);
lean_dec_ref(v_e_2857_);
return v___x_2925_;
}
else
{
lean_object* v_a_2926_; uint8_t v___y_2928_; uint8_t v___x_2968_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
v___x_2968_ = l_Lean_Exception_isInterrupt(v_a_2926_);
if (v___x_2968_ == 0)
{
uint8_t v___x_2969_; 
v___x_2969_ = l_Lean_Exception_isRuntime(v_a_2926_);
v___y_2928_ = v___x_2969_;
goto v___jp_2927_;
}
else
{
lean_dec(v_a_2926_);
v___y_2928_ = v___x_2968_;
goto v___jp_2927_;
}
v___jp_2927_:
{
if (v___y_2928_ == 0)
{
lean_object* v___x_2929_; 
lean_dec_ref_known(v___x_2925_, 1);
v___x_2929_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2923_, v_a_2859_, v_a_2861_);
lean_dec(v_a_2923_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v___x_2930_; 
lean_dec_ref_known(v___x_2929_, 1);
v___x_2930_ = l_Lean_Meta_saveState___redArg(v_a_2859_, v_a_2861_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2932_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
lean_dec_ref_known(v___x_2930_, 1);
lean_inc_ref(v_e_2857_);
v___x_2932_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(v_e_2857_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2941_; 
lean_dec(v_a_2931_);
lean_dec_ref(v_e_2857_);
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2935_ = v___x_2932_;
v_isShared_2936_ = v_isSharedCheck_2941_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2932_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2941_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2937_; lean_object* v___x_2939_; 
v___x_2937_ = lean_nat_to_int(v_a_2933_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 0, v___x_2937_);
v___x_2939_ = v___x_2935_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2937_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2951_; 
v_a_2942_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2944_ = v___x_2932_;
v_isShared_2945_ = v_isSharedCheck_2951_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2932_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2951_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
lean_inc(v_a_2942_);
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
uint8_t v___x_2948_; 
v___x_2948_ = l_Lean_Exception_isInterrupt(v_a_2942_);
if (v___x_2948_ == 0)
{
uint8_t v___x_2949_; 
v___x_2949_ = l_Lean_Exception_isRuntime(v_a_2942_);
v___y_2864_ = v_a_2931_;
v___y_2865_ = v___x_2947_;
v___y_2866_ = v___x_2949_;
goto v___jp_2863_;
}
else
{
lean_dec(v_a_2942_);
v___y_2864_ = v_a_2931_;
v___y_2865_ = v___x_2947_;
v___y_2866_ = v___x_2948_;
goto v___jp_2863_;
}
}
}
}
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_dec_ref(v_e_2857_);
v_a_2952_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2930_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2930_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_dec_ref(v_e_2857_);
v_a_2960_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2929_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2929_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
else
{
lean_dec(v_a_2923_);
lean_dec_ref(v_e_2857_);
return v___x_2925_;
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec_ref(v_e_2857_);
v_a_2970_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2922_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2922_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
v___jp_2863_:
{
if (v___y_2866_ == 0)
{
lean_object* v___x_2867_; 
lean_dec_ref(v___y_2865_);
v___x_2867_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2864_, v_a_2859_, v_a_2861_);
lean_dec_ref(v___y_2864_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v___x_2868_; uint8_t v___x_2869_; 
lean_dec_ref_known(v___x_2867_, 1);
v___x_2868_ = l_Lean_Expr_cleanupAnnotations(v_e_2857_);
v___x_2869_ = l_Lean_Expr_isApp(v___x_2868_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; 
lean_dec_ref(v___x_2868_);
v___x_2870_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_2870_;
}
else
{
lean_object* v_arg_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; 
v_arg_2871_ = lean_ctor_get(v___x_2868_, 1);
lean_inc_ref(v_arg_2871_);
v___x_2872_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2868_);
v___x_2873_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1));
v___x_2874_ = l_Lean_Expr_isConstOf(v___x_2872_, v___x_2873_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; uint8_t v___x_2876_; 
v___x_2875_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2));
v___x_2876_ = l_Lean_Expr_isConstOf(v___x_2872_, v___x_2875_);
lean_dec_ref(v___x_2872_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; 
lean_dec_ref(v_arg_2871_);
v___x_2877_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_2877_;
}
else
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v_arg_2871_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2887_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2881_ = v___x_2878_;
v_isShared_2882_ = v_isSharedCheck_2887_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2887_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2883_; lean_object* v___x_2885_; 
v___x_2883_ = lean_nat_to_int(v_a_2879_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v___x_2883_);
v___x_2885_ = v___x_2881_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2883_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
v_a_2888_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2878_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2878_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
}
else
{
lean_object* v___x_2896_; 
lean_dec_ref(v___x_2872_);
v___x_2896_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v_arg_2871_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2905_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2899_ = v___x_2896_;
v_isShared_2900_ = v_isSharedCheck_2905_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2896_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2905_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2901_; lean_object* v___x_2903_; 
v___x_2901_ = lean_int_neg_succ_of_nat(v_a_2897_);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 0, v___x_2901_);
v___x_2903_ = v___x_2899_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2901_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
v_a_2906_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2896_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2896_);
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
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref(v_e_2857_);
v_a_2914_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2867_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2867_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
else
{
lean_dec_ref(v___y_2864_);
lean_dec_ref(v_e_2857_);
return v___y_2865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___boxed(lean_object* v_e_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore(v_e_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec(v_a_2980_);
lean_dec_ref(v_a_2979_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0(lean_object* v_00_u03b1_2985_, lean_object* v_x_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v___x_2992_; 
v___x_2992_ = l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg(v_x_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___boxed(lean_object* v_00_u03b1_2993_, lean_object* v_x_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0(v_00_u03b1_2993_, v_x_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0(lean_object* v_00_u03b1_3001_, lean_object* v_msg_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(v_msg_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3009_, lean_object* v_msg_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0(v_00_u03b1_3009_, v_msg_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
return v_res_3016_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1(void){
_start:
{
uint8_t v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3018_ = 0;
v___x_3019_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__1));
v___x_3020_ = l_Lean_MessageData_ofConstName(v___x_3019_, v___x_3018_);
return v___x_3020_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2(void){
_start:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3021_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1);
v___x_3022_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
lean_ctor_set(v___x_3023_, 1, v___x_3021_);
return v___x_3023_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3(void){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3024_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3025_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2);
v___x_3026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
lean_ctor_set(v___x_3026_, 1, v___x_3024_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr(lean_object* v_e_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3033_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__0));
v___x_3034_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3, &l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3);
v___x_3035_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_3033_, v_e_3027_, v___x_3034_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___boxed(lean_object* v_e_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr(v_e_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
lean_dec(v_a_3040_);
lean_dec_ref(v_a_3039_);
lean_dec(v_a_3038_);
lean_dec_ref(v_a_3037_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg(lean_object* v_x_3043_){
_start:
{
if (lean_obj_tag(v_x_3043_) == 9)
{
lean_object* v_a_3045_; 
v_a_3045_ = lean_ctor_get(v_x_3043_, 0);
lean_inc_ref(v_a_3045_);
lean_dec_ref_known(v_x_3043_, 1);
if (lean_obj_tag(v_a_3045_) == 1)
{
lean_object* v_val_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
v_val_3046_ = lean_ctor_get(v_a_3045_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v_a_3045_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v_a_3045_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_val_3046_);
lean_dec(v_a_3045_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
lean_ctor_set_tag(v___x_3048_, 0);
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_val_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
else
{
lean_object* v___x_3054_; 
lean_dec_ref(v_a_3045_);
v___x_3054_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3054_;
}
}
else
{
lean_object* v___x_3055_; 
lean_dec_ref(v_x_3043_);
v___x_3055_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg___boxed(lean_object* v_x_3056_, lean_object* v_a_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg(v_x_3056_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore(lean_object* v_x_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg(v_x_3059_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___boxed(lean_object* v_x_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore(v_x_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
return v_res_3072_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1(void){
_start:
{
uint8_t v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = 0;
v___x_3075_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__1));
v___x_3076_ = l_Lean_MessageData_ofConstName(v___x_3075_, v___x_3074_);
return v___x_3076_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1);
v___x_3078_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
lean_ctor_set(v___x_3079_, 1, v___x_3077_);
return v___x_3079_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3081_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2);
v___x_3082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
lean_ctor_set(v___x_3082_, 1, v___x_3080_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr(lean_object* v_e_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3089_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__0));
v___x_3090_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3, &l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3);
v___x_3091_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_3089_, v_e_3083_, v___x_3090_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___boxed(lean_object* v_e_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr(v_e_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_);
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg(lean_object* v_e_3099_){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l_Lean_Expr_name_x3f(v_e_3099_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v___x_3102_; 
v___x_3102_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3102_;
}
else
{
lean_object* v_val_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
v_val_3103_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3101_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_val_3103_);
lean_dec(v___x_3101_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
lean_ctor_set_tag(v___x_3105_, 0);
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_val_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg___boxed(lean_object* v_e_3111_, lean_object* v_a_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg(v_e_3111_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore(lean_object* v_e_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_){
_start:
{
lean_object* v___x_3120_; 
v___x_3120_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg(v_e_3114_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___boxed(lean_object* v_e_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore(v_e_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_);
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
lean_dec(v_a_3123_);
lean_dec_ref(v_a_3122_);
return v_res_3127_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1(void){
_start:
{
uint8_t v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3129_ = 0;
v___x_3130_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1));
v___x_3131_ = l_Lean_MessageData_ofConstName(v___x_3130_, v___x_3129_);
return v___x_3131_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2(void){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3132_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1);
v___x_3133_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3133_);
lean_ctor_set(v___x_3134_, 1, v___x_3132_);
return v___x_3134_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3(void){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3135_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3136_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2);
v___x_3137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
lean_ctor_set(v___x_3137_, 1, v___x_3135_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr(lean_object* v_e_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_){
_start:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3144_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__0));
v___x_3145_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3, &l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3);
v___x_3146_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_3144_, v_e_3138_, v___x_3145_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___boxed(lean_object* v_e_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr(v_e_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
lean_dec(v_a_3151_);
lean_dec_ref(v_a_3150_);
lean_dec(v_a_3149_);
lean_dec_ref(v_a_3148_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg(lean_object* v_ev_3157_, lean_object* v_e_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_){
_start:
{
lean_object* v___x_3164_; uint8_t v___x_3165_; 
v___x_3164_ = l_Lean_Expr_cleanupAnnotations(v_e_3158_);
v___x_3165_ = l_Lean_Expr_isApp(v___x_3164_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; 
lean_dec_ref(v___x_3164_);
lean_dec_ref(v_ev_3157_);
v___x_3166_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3166_;
}
else
{
lean_object* v_arg_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; uint8_t v___x_3170_; 
v_arg_3167_ = lean_ctor_get(v___x_3164_, 1);
lean_inc_ref(v_arg_3167_);
v___x_3168_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3164_);
v___x_3169_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8));
v___x_3170_ = l_Lean_Expr_isConstOf(v___x_3168_, v___x_3169_);
if (v___x_3170_ == 0)
{
uint8_t v___x_3171_; 
v___x_3171_ = l_Lean_Expr_isApp(v___x_3168_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3172_; 
lean_dec_ref(v___x_3168_);
lean_dec_ref(v_arg_3167_);
lean_dec_ref(v_ev_3157_);
v___x_3172_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3172_;
}
else
{
lean_object* v___x_3173_; lean_object* v___x_3174_; uint8_t v___x_3175_; 
v___x_3173_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3168_);
v___x_3174_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0));
v___x_3175_ = l_Lean_Expr_isConstOf(v___x_3173_, v___x_3174_);
lean_dec_ref(v___x_3173_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; 
lean_dec_ref(v_arg_3167_);
lean_dec_ref(v_ev_3157_);
v___x_3176_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3176_;
}
else
{
lean_object* v___x_3177_; 
lean_inc(v_a_3162_);
lean_inc_ref(v_a_3161_);
lean_inc(v_a_3160_);
lean_inc_ref(v_a_3159_);
v___x_3177_ = lean_apply_6(v_ev_3157_, v_arg_3167_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_, lean_box(0));
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3186_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3186_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3186_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3182_; lean_object* v___x_3184_; 
v___x_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3182_, 0, v_a_3178_);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v___x_3182_);
v___x_3184_ = v___x_3180_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3182_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
v_a_3187_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3177_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3177_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
}
}
else
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
lean_dec_ref(v___x_3168_);
lean_dec_ref(v_arg_3167_);
lean_dec_ref(v_ev_3157_);
v___x_3195_ = lean_box(0);
v___x_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
return v___x_3196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___boxed(lean_object* v_ev_3197_, lean_object* v_e_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg(v_ev_3197_, v_e_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_);
lean_dec(v_a_3202_);
lean_dec_ref(v_a_3201_);
lean_dec(v_a_3200_);
lean_dec_ref(v_a_3199_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore(lean_object* v_00_u03b1_3205_, lean_object* v_ev_3206_, lean_object* v_e_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg(v_ev_3206_, v_e_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___boxed(lean_object* v_00_u03b1_3214_, lean_object* v_ev_3215_, lean_object* v_e_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore(v_00_u03b1_3214_, v_ev_3215_, v_e_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
lean_dec(v_a_3220_);
lean_dec_ref(v_a_3219_);
lean_dec(v_a_3218_);
lean_dec_ref(v_a_3217_);
return v_res_3222_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0(void){
_start:
{
uint8_t v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3223_ = 0;
v___x_3224_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__1));
v___x_3225_ = l_Lean_MessageData_ofConstName(v___x_3224_, v___x_3223_);
return v___x_3225_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0, &l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0);
v___x_3227_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
lean_ctor_set(v___x_3228_, 1, v___x_3226_);
return v___x_3228_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3230_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1);
v___x_3231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
lean_ctor_set(v___x_3231_, 1, v___x_3229_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg(lean_object* v_ev_3232_, lean_object* v_e_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Lean_Meta_saveState___redArg(v_a_3235_, v_a_3237_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3240_);
lean_dec_ref_known(v___x_3239_, 1);
lean_inc_ref(v_ev_3232_);
v___x_3241_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___boxed), 8, 2);
lean_closure_set(v___x_3241_, 0, lean_box(0));
lean_closure_set(v___x_3241_, 1, v_ev_3232_);
v___x_3242_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2);
lean_inc_ref(v_e_3233_);
v___x_3243_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_3241_, v_e_3233_, v___x_3242_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_dec(v_a_3240_);
lean_dec_ref(v_e_3233_);
lean_dec_ref(v_ev_3232_);
return v___x_3243_;
}
else
{
lean_object* v_a_3244_; uint8_t v___y_3246_; uint8_t v___x_3281_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
lean_inc(v_a_3244_);
v___x_3281_ = l_Lean_Exception_isInterrupt(v_a_3244_);
if (v___x_3281_ == 0)
{
uint8_t v___x_3282_; 
v___x_3282_ = l_Lean_Exception_isRuntime(v_a_3244_);
v___y_3246_ = v___x_3282_;
goto v___jp_3245_;
}
else
{
lean_dec(v_a_3244_);
v___y_3246_ = v___x_3281_;
goto v___jp_3245_;
}
v___jp_3245_:
{
if (v___y_3246_ == 0)
{
lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3279_; 
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3279_ == 0)
{
lean_object* v_unused_3280_; 
v_unused_3280_ = lean_ctor_get(v___x_3243_, 0);
lean_dec(v_unused_3280_);
v___x_3248_ = v___x_3243_;
v_isShared_3249_ = v_isSharedCheck_3279_;
goto v_resetjp_3247_;
}
else
{
lean_dec(v___x_3243_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3279_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3250_; 
v___x_3250_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3240_, v_a_3235_, v_a_3237_);
lean_dec(v_a_3240_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v___x_3251_; 
lean_dec_ref_known(v___x_3250_, 1);
lean_inc(v_a_3237_);
lean_inc_ref(v_a_3236_);
lean_inc(v_a_3235_);
lean_inc_ref(v_a_3234_);
v___x_3251_ = lean_apply_6(v_ev_3232_, v_e_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, lean_box(0));
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3262_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3254_ = v___x_3251_;
v_isShared_3255_ = v_isSharedCheck_3262_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3251_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3262_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 0, v_a_3252_);
v___x_3257_ = v___x_3248_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3259_; 
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 0, v___x_3257_);
v___x_3259_ = v___x_3254_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v___x_3257_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_del_object(v___x_3248_);
v_a_3263_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3251_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3251_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3263_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_del_object(v___x_3248_);
lean_dec_ref(v_e_3233_);
lean_dec_ref(v_ev_3232_);
v_a_3271_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3250_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3250_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
}
else
{
lean_dec(v_a_3240_);
lean_dec_ref(v_e_3233_);
lean_dec_ref(v_ev_3232_);
return v___x_3243_;
}
}
}
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec_ref(v_e_3233_);
lean_dec_ref(v_ev_3232_);
v_a_3283_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3239_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3239_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___boxed(lean_object* v_ev_3291_, lean_object* v_e_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg(v_ev_3291_, v_e_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
lean_dec(v_a_3296_);
lean_dec_ref(v_a_3295_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr(lean_object* v_00_u03b1_3299_, lean_object* v_ev_3300_, lean_object* v_e_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg(v_ev_3300_, v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___boxed(lean_object* v_00_u03b1_3308_, lean_object* v_ev_3309_, lean_object* v_e_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr(v_00_u03b1_3308_, v_ev_3309_, v_e_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
lean_dec(v_a_3314_);
lean_dec_ref(v_a_3313_);
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3311_);
return v_res_3316_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1(void){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3318_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__0));
v___x_3319_ = l_Lean_stringToMessageData(v___x_3318_);
return v___x_3319_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2(void){
_start:
{
uint8_t v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3320_ = 0;
v___x_3321_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__0));
v___x_3322_ = l_Lean_MessageData_ofConstName(v___x_3321_, v___x_3320_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(lean_object* v_ev_3323_, lean_object* v_e_3324_, uint8_t v_didWHNF_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_){
_start:
{
lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___x_3358_; uint8_t v___x_3359_; 
lean_inc_ref(v_e_3324_);
v___x_3358_ = l_Lean_Expr_cleanupAnnotations(v_e_3324_);
v___x_3359_ = l_Lean_Expr_isApp(v___x_3358_);
if (v___x_3359_ == 0)
{
lean_dec_ref(v___x_3358_);
v___y_3332_ = v_a_3326_;
v___y_3333_ = v_a_3327_;
v___y_3334_ = v_a_3328_;
v___y_3335_ = v_a_3329_;
goto v___jp_3331_;
}
else
{
lean_object* v_arg_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v_arg_3360_ = lean_ctor_get(v___x_3358_, 1);
lean_inc_ref(v_arg_3360_);
v___x_3361_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3358_);
v___x_3362_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5));
v___x_3363_ = l_Lean_Expr_isConstOf(v___x_3361_, v___x_3362_);
if (v___x_3363_ == 0)
{
uint8_t v___x_3364_; 
v___x_3364_ = l_Lean_Expr_isApp(v___x_3361_);
if (v___x_3364_ == 0)
{
lean_dec_ref(v___x_3361_);
lean_dec_ref(v_arg_3360_);
v___y_3332_ = v_a_3326_;
v___y_3333_ = v_a_3327_;
v___y_3334_ = v_a_3328_;
v___y_3335_ = v_a_3329_;
goto v___jp_3331_;
}
else
{
lean_object* v_arg_3365_; lean_object* v___x_3366_; uint8_t v___x_3367_; 
v_arg_3365_ = lean_ctor_get(v___x_3361_, 1);
lean_inc_ref(v_arg_3365_);
v___x_3366_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3361_);
v___x_3367_ = l_Lean_Expr_isApp(v___x_3366_);
if (v___x_3367_ == 0)
{
lean_dec_ref(v___x_3366_);
lean_dec_ref(v_arg_3365_);
lean_dec_ref(v_arg_3360_);
v___y_3332_ = v_a_3326_;
v___y_3333_ = v_a_3327_;
v___y_3334_ = v_a_3328_;
v___y_3335_ = v_a_3329_;
goto v___jp_3331_;
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3369_; uint8_t v___x_3370_; 
v___x_3368_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3366_);
v___x_3369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2));
v___x_3370_ = l_Lean_Expr_isConstOf(v___x_3368_, v___x_3369_);
lean_dec_ref(v___x_3368_);
if (v___x_3370_ == 0)
{
lean_dec_ref(v_arg_3365_);
lean_dec_ref(v_arg_3360_);
v___y_3332_ = v_a_3326_;
v___y_3333_ = v_a_3327_;
v___y_3334_ = v_a_3328_;
v___y_3335_ = v_a_3329_;
goto v___jp_3331_;
}
else
{
lean_object* v___x_3371_; 
lean_dec_ref(v_e_3324_);
lean_inc_ref(v_ev_3323_);
lean_inc(v_a_3329_);
lean_inc_ref(v_a_3328_);
lean_inc(v_a_3327_);
lean_inc_ref(v_a_3326_);
v___x_3371_ = lean_apply_6(v_ev_3323_, v_arg_3365_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, lean_box(0));
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; lean_object* v___x_3373_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_a_3372_);
lean_dec_ref_known(v___x_3371_, 1);
v___x_3373_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(v_ev_3323_, v_arg_3360_, v___x_3363_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3382_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3376_ = v___x_3373_;
v_isShared_3377_ = v_isSharedCheck_3382_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3373_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3382_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3378_; lean_object* v___x_3380_; 
v___x_3378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3378_, 0, v_a_3372_);
lean_ctor_set(v___x_3378_, 1, v_a_3374_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 0, v___x_3378_);
v___x_3380_ = v___x_3376_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3378_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
else
{
lean_dec(v_a_3372_);
return v___x_3373_;
}
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
lean_dec_ref(v_arg_3360_);
lean_dec_ref(v_ev_3323_);
v_a_3383_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3371_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3371_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
lean_dec_ref(v___x_3361_);
lean_dec_ref(v_arg_3360_);
lean_dec_ref(v_e_3324_);
lean_dec_ref(v_ev_3323_);
v___x_3391_ = lean_box(0);
v___x_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
return v___x_3392_;
}
}
v___jp_3331_:
{
if (v_didWHNF_3325_ == 0)
{
lean_object* v___x_3336_; 
lean_inc(v___y_3335_);
lean_inc_ref(v___y_3334_);
lean_inc(v___y_3333_);
lean_inc_ref(v___y_3332_);
v___x_3336_ = lean_whnf(v_e_3324_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v_a_3337_; uint8_t v___x_3338_; 
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
lean_inc(v_a_3337_);
lean_dec_ref_known(v___x_3336_, 1);
v___x_3338_ = 1;
v_e_3324_ = v_a_3337_;
v_didWHNF_3325_ = v___x_3338_;
v_a_3326_ = v___y_3332_;
v_a_3327_ = v___y_3333_;
v_a_3328_ = v___y_3334_;
v_a_3329_ = v___y_3335_;
goto _start;
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
lean_dec_ref(v_ev_3323_);
v_a_3340_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3336_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3336_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
else
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
lean_dec_ref(v_ev_3323_);
v___x_3348_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1);
v___x_3349_ = l_Lean_indentExpr(v_e_3324_);
v___x_3350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3348_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___x_3351_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3350_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
v___x_3353_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2);
v___x_3354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3352_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3354_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
v___x_3357_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(v___x_3356_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
return v___x_3357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___boxed(lean_object* v_ev_3393_, lean_object* v_e_3394_, lean_object* v_didWHNF_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
uint8_t v_didWHNF_boxed_3401_; lean_object* v_res_3402_; 
v_didWHNF_boxed_3401_ = lean_unbox(v_didWHNF_3395_);
v_res_3402_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(v_ev_3393_, v_e_3394_, v_didWHNF_boxed_3401_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
lean_dec(v_a_3399_);
lean_dec_ref(v_a_3398_);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3396_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr(lean_object* v_00_u03b1_3403_, lean_object* v_ev_3404_, lean_object* v_e_3405_, uint8_t v_didWHNF_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_){
_start:
{
lean_object* v___x_3412_; 
v___x_3412_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(v_ev_3404_, v_e_3405_, v_didWHNF_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___boxed(lean_object* v_00_u03b1_3413_, lean_object* v_ev_3414_, lean_object* v_e_3415_, lean_object* v_didWHNF_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_){
_start:
{
uint8_t v_didWHNF_boxed_3422_; lean_object* v_res_3423_; 
v_didWHNF_boxed_3422_ = lean_unbox(v_didWHNF_3416_);
v_res_3423_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr(v_00_u03b1_3413_, v_ev_3414_, v_e_3415_, v_didWHNF_boxed_3422_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_);
lean_dec(v_a_3420_);
lean_dec_ref(v_a_3419_);
lean_dec(v_a_3418_);
lean_dec_ref(v_a_3417_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0(lean_object* v_ev_3430_, lean_object* v_e_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v_e_x27_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___x_3462_; uint8_t v___x_3463_; 
v___x_3462_ = l_Lean_Expr_cleanupAnnotations(v_e_3431_);
v___x_3463_ = l_Lean_Expr_isApp(v___x_3462_);
if (v___x_3463_ == 0)
{
lean_object* v___x_3464_; 
lean_dec_ref(v___x_3462_);
lean_dec_ref(v_ev_3430_);
v___x_3464_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3464_;
}
else
{
lean_object* v_arg_3465_; lean_object* v___x_3466_; uint8_t v___x_3467_; 
v_arg_3465_ = lean_ctor_get(v___x_3462_, 1);
lean_inc_ref(v_arg_3465_);
v___x_3466_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3462_);
v___x_3467_ = l_Lean_Expr_isApp(v___x_3466_);
if (v___x_3467_ == 0)
{
lean_object* v___x_3468_; 
lean_dec_ref(v___x_3466_);
lean_dec_ref(v_arg_3465_);
lean_dec_ref(v_ev_3430_);
v___x_3468_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3468_;
}
else
{
lean_object* v___x_3469_; lean_object* v___x_3470_; uint8_t v___x_3471_; 
v___x_3469_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3466_);
v___x_3470_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0));
v___x_3471_ = l_Lean_Expr_isConstOf(v___x_3469_, v___x_3470_);
if (v___x_3471_ == 0)
{
lean_object* v___x_3472_; uint8_t v___x_3473_; 
v___x_3472_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1));
v___x_3473_ = l_Lean_Expr_isConstOf(v___x_3469_, v___x_3472_);
lean_dec_ref(v___x_3469_);
if (v___x_3473_ == 0)
{
lean_object* v___x_3474_; 
lean_dec_ref(v_arg_3465_);
lean_dec_ref(v_ev_3430_);
v___x_3474_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3474_;
}
else
{
v_e_x27_3438_ = v_arg_3465_;
v___y_3439_ = v___y_3432_;
v___y_3440_ = v___y_3433_;
v___y_3441_ = v___y_3434_;
v___y_3442_ = v___y_3435_;
goto v___jp_3437_;
}
}
else
{
lean_dec_ref(v___x_3469_);
v_e_x27_3438_ = v_arg_3465_;
v___y_3439_ = v___y_3432_;
v___y_3440_ = v___y_3433_;
v___y_3441_ = v___y_3434_;
v___y_3442_ = v___y_3435_;
goto v___jp_3437_;
}
}
}
v___jp_3437_:
{
uint8_t v___x_3443_; lean_object* v___x_3444_; 
v___x_3443_ = 0;
v___x_3444_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(v_ev_3430_, v_e_x27_3438_, v___x_3443_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3453_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3447_ = v___x_3444_;
v_isShared_3448_ = v_isSharedCheck_3453_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3444_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3453_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3449_; lean_object* v___x_3451_; 
v___x_3449_ = lean_array_mk(v_a_3445_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v___x_3449_);
v___x_3451_ = v___x_3447_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3449_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
else
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
v_a_3454_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3456_ = v___x_3444_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3444_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___boxed(lean_object* v_ev_3475_, lean_object* v_e_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0(v_ev_3475_, v_e_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
return v_res_3482_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0(void){
_start:
{
uint8_t v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3483_ = 0;
v___x_3484_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__1));
v___x_3485_ = l_Lean_MessageData_ofConstName(v___x_3484_, v___x_3483_);
return v___x_3485_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1(void){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3486_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0, &l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0);
v___x_3487_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
lean_ctor_set(v___x_3488_, 1, v___x_3486_);
return v___x_3488_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3489_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3490_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1);
v___x_3491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3490_);
lean_ctor_set(v___x_3491_, 1, v___x_3489_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg(lean_object* v_ev_3492_, lean_object* v_e_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_){
_start:
{
lean_object* v___f_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___f_3499_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3499_, 0, v_ev_3492_);
v___x_3500_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2);
v___x_3501_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___f_3499_, v_e_3493_, v___x_3500_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___boxed(lean_object* v_ev_3502_, lean_object* v_e_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg(v_ev_3502_, v_e_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr(lean_object* v_00_u03b1_3510_, lean_object* v_ev_3511_, lean_object* v_e_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg(v_ev_3511_, v_e_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___boxed(lean_object* v_00_u03b1_3519_, lean_object* v_ev_3520_, lean_object* v_e_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr(v_00_u03b1_3519_, v_ev_3520_, v_e_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_);
lean_dec(v_a_3525_);
lean_dec_ref(v_a_3524_);
lean_dec(v_a_3523_);
lean_dec_ref(v_a_3522_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore(lean_object* v_e_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_){
_start:
{
lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; uint8_t v___y_3539_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; uint8_t v___y_3555_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; uint8_t v___y_3600_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; uint8_t v___y_3647_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; uint8_t v___y_3694_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___x_3770_; uint8_t v___x_3771_; 
lean_inc_ref(v_e_3528_);
v___x_3770_ = l_Lean_Expr_cleanupAnnotations(v_e_3528_);
v___x_3771_ = l_Lean_Expr_isApp(v___x_3770_);
if (v___x_3771_ == 0)
{
lean_dec_ref(v___x_3770_);
v___y_3735_ = v_a_3529_;
v___y_3736_ = v_a_3530_;
v___y_3737_ = v_a_3531_;
v___y_3738_ = v_a_3532_;
goto v___jp_3734_;
}
else
{
lean_object* v_arg_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; uint8_t v___x_3775_; 
v_arg_3772_ = lean_ctor_get(v___x_3770_, 1);
lean_inc_ref(v_arg_3772_);
v___x_3773_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3770_);
v___x_3774_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8));
v___x_3775_ = l_Lean_Expr_isConstOf(v___x_3773_, v___x_3774_);
if (v___x_3775_ == 0)
{
lean_object* v___x_3776_; uint8_t v___x_3777_; 
v___x_3776_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10));
v___x_3777_ = l_Lean_Expr_isConstOf(v___x_3773_, v___x_3776_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; uint8_t v___x_3779_; 
v___x_3778_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13));
v___x_3779_ = l_Lean_Expr_isConstOf(v___x_3773_, v___x_3778_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; uint8_t v___x_3781_; 
v___x_3780_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15));
v___x_3781_ = l_Lean_Expr_isConstOf(v___x_3773_, v___x_3780_);
if (v___x_3781_ == 0)
{
lean_object* v___x_3782_; uint8_t v___x_3783_; 
v___x_3782_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3));
v___x_3783_ = l_Lean_Expr_isConstOf(v___x_3773_, v___x_3782_);
lean_dec_ref(v___x_3773_);
if (v___x_3783_ == 0)
{
lean_dec_ref(v_arg_3772_);
v___y_3735_ = v_a_3529_;
v___y_3736_ = v_a_3530_;
v___y_3737_ = v_a_3531_;
v___y_3738_ = v_a_3532_;
goto v___jp_3734_;
}
else
{
lean_object* v___x_3784_; 
lean_dec_ref(v_e_3528_);
v___x_3784_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v_arg_3772_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3794_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3787_ = v___x_3784_;
v_isShared_3788_ = v_isSharedCheck_3794_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3784_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3794_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3789_; uint8_t v___x_3790_; lean_object* v___x_3792_; 
v___x_3789_ = lean_alloc_ctor(1, 0, 1);
v___x_3790_ = lean_unbox(v_a_3785_);
lean_dec(v_a_3785_);
lean_ctor_set_uint8(v___x_3789_, 0, v___x_3790_);
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v___x_3789_);
v___x_3792_ = v___x_3787_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v___x_3789_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
else
{
lean_object* v_a_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3802_; 
v_a_3795_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3797_ = v___x_3784_;
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_a_3795_);
lean_dec(v___x_3784_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
if (v_isShared_3798_ == 0)
{
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_a_3795_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
}
else
{
lean_object* v___x_3803_; 
lean_dec_ref(v___x_3773_);
lean_dec_ref(v_e_3528_);
v___x_3803_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v_arg_3772_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3812_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3806_ = v___x_3803_;
v_isShared_3807_ = v_isSharedCheck_3812_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3803_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3812_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3808_; lean_object* v___x_3810_; 
v___x_3808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3808_, 0, v_a_3804_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 0, v___x_3808_);
v___x_3810_ = v___x_3806_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3808_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
v_a_3813_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3803_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3803_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
}
else
{
lean_object* v___x_3821_; 
lean_dec_ref(v___x_3773_);
lean_dec_ref(v_e_3528_);
v___x_3821_ = l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr(v_arg_3772_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3830_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3824_ = v___x_3821_;
v_isShared_3825_ = v_isSharedCheck_3830_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3821_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3830_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3826_; lean_object* v___x_3828_; 
v___x_3826_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3826_, 0, v_a_3822_);
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v___x_3826_);
v___x_3828_ = v___x_3824_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v___x_3826_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3838_; 
v_a_3831_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3833_ = v___x_3821_;
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3821_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3831_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
}
else
{
lean_object* v___x_3839_; 
lean_dec_ref(v___x_3773_);
lean_dec_ref(v_e_3528_);
v___x_3839_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr(v_arg_3772_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3848_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3842_ = v___x_3839_;
v_isShared_3843_ = v_isSharedCheck_3848_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3839_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3848_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3844_; lean_object* v___x_3846_; 
v___x_3844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3844_, 0, v_a_3840_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 0, v___x_3844_);
v___x_3846_ = v___x_3842_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3844_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
v_a_3849_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3839_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3839_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
else
{
lean_object* v___x_3857_; 
lean_dec_ref(v___x_3773_);
lean_dec_ref(v_e_3528_);
v___x_3857_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr(v_arg_3772_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3866_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3860_ = v___x_3857_;
v_isShared_3861_ = v_isSharedCheck_3866_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3857_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3866_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3862_; lean_object* v___x_3864_; 
v___x_3862_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3862_, 0, v_a_3858_);
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_3862_);
v___x_3864_ = v___x_3860_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3862_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
else
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
v_a_3867_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3857_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3857_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
}
v___jp_3534_:
{
if (v___y_3539_ == 0)
{
lean_object* v___x_3540_; 
lean_dec_ref(v___y_3535_);
v___x_3540_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3538_, v___y_3537_, v___y_3536_);
lean_dec_ref(v___y_3538_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v___x_3541_; 
lean_dec_ref_known(v___x_3540_, 1);
v___x_3541_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3541_;
}
else
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
v_a_3542_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_3540_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3540_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3547_; 
if (v_isShared_3545_ == 0)
{
v___x_3547_ = v___x_3544_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_a_3542_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
else
{
lean_dec_ref(v___y_3538_);
return v___y_3535_;
}
}
v___jp_3550_:
{
if (v___y_3555_ == 0)
{
lean_object* v___x_3556_; 
lean_dec_ref(v___y_3551_);
v___x_3556_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3552_, v___y_3554_, v___y_3553_);
lean_dec_ref(v___y_3552_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v___x_3557_; 
lean_dec_ref_known(v___x_3556_, 1);
v___x_3557_ = l_Lean_Meta_saveState___redArg(v___y_3554_, v___y_3553_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v___x_3559_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref_known(v___x_3557_, 1);
v___x_3559_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg(v_e_3528_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3568_; 
lean_dec(v_a_3558_);
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3562_ = v___x_3559_;
v_isShared_3563_ = v_isSharedCheck_3568_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3559_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3568_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3564_; lean_object* v___x_3566_; 
v___x_3564_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3564_, 0, v_a_3560_);
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 0, v___x_3564_);
v___x_3566_ = v___x_3562_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3564_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3578_; 
v_a_3569_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3571_ = v___x_3559_;
v_isShared_3572_ = v_isSharedCheck_3578_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3559_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3578_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
lean_inc(v_a_3569_);
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
uint8_t v___x_3575_; 
v___x_3575_ = l_Lean_Exception_isInterrupt(v_a_3569_);
if (v___x_3575_ == 0)
{
uint8_t v___x_3576_; 
v___x_3576_ = l_Lean_Exception_isRuntime(v_a_3569_);
v___y_3535_ = v___x_3574_;
v___y_3536_ = v___y_3553_;
v___y_3537_ = v___y_3554_;
v___y_3538_ = v_a_3558_;
v___y_3539_ = v___x_3576_;
goto v___jp_3534_;
}
else
{
lean_dec(v_a_3569_);
v___y_3535_ = v___x_3574_;
v___y_3536_ = v___y_3553_;
v___y_3537_ = v___y_3554_;
v___y_3538_ = v_a_3558_;
v___y_3539_ = v___x_3575_;
goto v___jp_3534_;
}
}
}
}
}
else
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
lean_dec_ref(v_e_3528_);
v_a_3579_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3581_ = v___x_3557_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3557_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3579_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
else
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3594_; 
lean_dec_ref(v_e_3528_);
v_a_3587_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3589_ = v___x_3556_;
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3556_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
if (v_isShared_3590_ == 0)
{
v___x_3592_ = v___x_3589_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3587_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
else
{
lean_dec_ref(v___y_3552_);
lean_dec_ref(v_e_3528_);
return v___y_3551_;
}
}
v___jp_3595_:
{
if (v___y_3600_ == 0)
{
lean_object* v___x_3601_; 
lean_dec_ref(v___y_3596_);
v___x_3601_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3597_, v___y_3599_, v___y_3598_);
lean_dec_ref(v___y_3597_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v___x_3602_; 
lean_dec_ref_known(v___x_3601_, 1);
v___x_3602_ = l_Lean_Meta_saveState___redArg(v___y_3599_, v___y_3598_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3603_; lean_object* v___x_3604_; 
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_a_3603_);
lean_dec_ref_known(v___x_3602_, 1);
lean_inc_ref(v_e_3528_);
v___x_3604_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg(v_e_3528_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3613_; 
lean_dec(v_a_3603_);
lean_dec_ref(v_e_3528_);
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3607_ = v___x_3604_;
v_isShared_3608_ = v_isSharedCheck_3613_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3604_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3613_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3609_; lean_object* v___x_3611_; 
v___x_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3609_, 0, v_a_3605_);
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 0, v___x_3609_);
v___x_3611_ = v___x_3607_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3609_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3623_; 
v_a_3614_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3616_ = v___x_3604_;
v_isShared_3617_ = v_isSharedCheck_3623_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3604_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3623_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
lean_inc(v_a_3614_);
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
uint8_t v___x_3620_; 
v___x_3620_ = l_Lean_Exception_isInterrupt(v_a_3614_);
if (v___x_3620_ == 0)
{
uint8_t v___x_3621_; 
v___x_3621_ = l_Lean_Exception_isRuntime(v_a_3614_);
v___y_3551_ = v___x_3619_;
v___y_3552_ = v_a_3603_;
v___y_3553_ = v___y_3598_;
v___y_3554_ = v___y_3599_;
v___y_3555_ = v___x_3621_;
goto v___jp_3550_;
}
else
{
lean_dec(v_a_3614_);
v___y_3551_ = v___x_3619_;
v___y_3552_ = v_a_3603_;
v___y_3553_ = v___y_3598_;
v___y_3554_ = v___y_3599_;
v___y_3555_ = v___x_3620_;
goto v___jp_3550_;
}
}
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec_ref(v_e_3528_);
v_a_3624_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3602_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3602_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec_ref(v_e_3528_);
v_a_3632_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3601_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3601_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
else
{
lean_dec_ref(v___y_3597_);
lean_dec_ref(v_e_3528_);
return v___y_3596_;
}
}
v___jp_3640_:
{
if (v___y_3647_ == 0)
{
lean_object* v___x_3648_; 
lean_dec_ref(v___y_3643_);
v___x_3648_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3646_, v___y_3644_, v___y_3642_);
lean_dec_ref(v___y_3646_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v___x_3649_; 
lean_dec_ref_known(v___x_3648_, 1);
v___x_3649_ = l_Lean_Meta_saveState___redArg(v___y_3644_, v___y_3642_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3651_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_a_3650_);
lean_dec_ref_known(v___x_3649_, 1);
lean_inc_ref(v_e_3528_);
v___x_3651_ = l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore(v_e_3528_, v___y_3645_, v___y_3644_, v___y_3641_, v___y_3642_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3660_; 
lean_dec(v_a_3650_);
lean_dec_ref(v_e_3528_);
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3654_ = v___x_3651_;
v_isShared_3655_ = v_isSharedCheck_3660_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___x_3651_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3660_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3656_; lean_object* v___x_3658_; 
v___x_3656_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3656_, 0, v_a_3652_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 0, v___x_3656_);
v___x_3658_ = v___x_3654_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3656_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3670_; 
v_a_3661_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3663_ = v___x_3651_;
v_isShared_3664_ = v_isSharedCheck_3670_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3651_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3670_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
lean_inc(v_a_3661_);
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3661_);
v___x_3666_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
uint8_t v___x_3667_; 
v___x_3667_ = l_Lean_Exception_isInterrupt(v_a_3661_);
if (v___x_3667_ == 0)
{
uint8_t v___x_3668_; 
v___x_3668_ = l_Lean_Exception_isRuntime(v_a_3661_);
v___y_3596_ = v___x_3666_;
v___y_3597_ = v_a_3650_;
v___y_3598_ = v___y_3642_;
v___y_3599_ = v___y_3644_;
v___y_3600_ = v___x_3668_;
goto v___jp_3595_;
}
else
{
lean_dec(v_a_3661_);
v___y_3596_ = v___x_3666_;
v___y_3597_ = v_a_3650_;
v___y_3598_ = v___y_3642_;
v___y_3599_ = v___y_3644_;
v___y_3600_ = v___x_3667_;
goto v___jp_3595_;
}
}
}
}
}
else
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3678_; 
lean_dec_ref(v_e_3528_);
v_a_3671_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3673_ = v___x_3649_;
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3649_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3676_; 
if (v_isShared_3674_ == 0)
{
v___x_3676_ = v___x_3673_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3671_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_dec_ref(v_e_3528_);
v_a_3679_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3648_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3648_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
else
{
lean_dec_ref(v___y_3646_);
lean_dec_ref(v_e_3528_);
return v___y_3643_;
}
}
v___jp_3687_:
{
if (v___y_3694_ == 0)
{
lean_object* v___x_3695_; 
lean_dec_ref(v___y_3689_);
v___x_3695_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3690_, v___y_3692_, v___y_3691_);
lean_dec_ref(v___y_3690_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v___x_3696_; 
lean_dec_ref_known(v___x_3695_, 1);
v___x_3696_ = l_Lean_Meta_saveState___redArg(v___y_3692_, v___y_3691_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v_a_3697_; lean_object* v___x_3698_; 
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
lean_inc(v_a_3697_);
lean_dec_ref_known(v___x_3696_, 1);
lean_inc_ref(v_e_3528_);
v___x_3698_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(v_e_3528_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3707_; 
lean_dec(v_a_3697_);
lean_dec_ref(v_e_3528_);
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
v___x_3703_ = lean_alloc_ctor(3, 1, 0);
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
v___y_3641_ = v___y_3688_;
v___y_3642_ = v___y_3691_;
v___y_3643_ = v___x_3713_;
v___y_3644_ = v___y_3692_;
v___y_3645_ = v___y_3693_;
v___y_3646_ = v_a_3697_;
v___y_3647_ = v___x_3715_;
goto v___jp_3640_;
}
else
{
lean_dec(v_a_3708_);
v___y_3641_ = v___y_3688_;
v___y_3642_ = v___y_3691_;
v___y_3643_ = v___x_3713_;
v___y_3644_ = v___y_3692_;
v___y_3645_ = v___y_3693_;
v___y_3646_ = v_a_3697_;
v___y_3647_ = v___x_3714_;
goto v___jp_3640_;
}
}
}
}
}
else
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3725_; 
lean_dec_ref(v_e_3528_);
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
lean_dec_ref(v_e_3528_);
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
lean_dec_ref(v___y_3690_);
lean_dec_ref(v_e_3528_);
return v___y_3689_;
}
}
v___jp_3734_:
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_Meta_saveState___redArg(v___y_3736_, v___y_3738_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; lean_object* v___x_3741_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3740_);
lean_dec_ref_known(v___x_3739_, 1);
lean_inc_ref(v_e_3528_);
v___x_3741_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore(v_e_3528_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3751_; 
lean_dec(v_a_3740_);
lean_dec_ref(v_e_3528_);
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3744_ = v___x_3741_;
v_isShared_3745_ = v_isSharedCheck_3751_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3741_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3751_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3746_; uint8_t v___x_3747_; lean_object* v___x_3749_; 
v___x_3746_ = lean_alloc_ctor(1, 0, 1);
v___x_3747_ = lean_unbox(v_a_3742_);
lean_dec(v_a_3742_);
lean_ctor_set_uint8(v___x_3746_, 0, v___x_3747_);
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 0, v___x_3746_);
v___x_3749_ = v___x_3744_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3746_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3761_; 
v_a_3752_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3754_ = v___x_3741_;
v_isShared_3755_ = v_isSharedCheck_3761_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3741_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3761_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
lean_inc(v_a_3752_);
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
uint8_t v___x_3758_; 
v___x_3758_ = l_Lean_Exception_isInterrupt(v_a_3752_);
if (v___x_3758_ == 0)
{
uint8_t v___x_3759_; 
v___x_3759_ = l_Lean_Exception_isRuntime(v_a_3752_);
v___y_3688_ = v___y_3737_;
v___y_3689_ = v___x_3757_;
v___y_3690_ = v_a_3740_;
v___y_3691_ = v___y_3738_;
v___y_3692_ = v___y_3736_;
v___y_3693_ = v___y_3735_;
v___y_3694_ = v___x_3759_;
goto v___jp_3687_;
}
else
{
lean_dec(v_a_3752_);
v___y_3688_ = v___y_3737_;
v___y_3689_ = v___x_3757_;
v___y_3690_ = v_a_3740_;
v___y_3691_ = v___y_3738_;
v___y_3692_ = v___y_3736_;
v___y_3693_ = v___y_3735_;
v___y_3694_ = v___x_3758_;
goto v___jp_3687_;
}
}
}
}
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
lean_dec_ref(v_e_3528_);
v_a_3762_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3739_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3739_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore___boxed(lean_object* v_e_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_){
_start:
{
lean_object* v_res_3881_; 
v_res_3881_ = l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore(v_e_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_);
lean_dec(v_a_3879_);
lean_dec_ref(v_a_3878_);
lean_dec(v_a_3877_);
lean_dec_ref(v_a_3876_);
return v_res_3881_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1(void){
_start:
{
uint8_t v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3883_ = 0;
v___x_3884_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1));
v___x_3885_ = l_Lean_MessageData_ofConstName(v___x_3884_, v___x_3883_);
return v___x_3885_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2(void){
_start:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3886_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1);
v___x_3887_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3887_);
lean_ctor_set(v___x_3888_, 1, v___x_3886_);
return v___x_3888_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3(void){
_start:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3889_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3890_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2);
v___x_3891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
lean_ctor_set(v___x_3891_, 1, v___x_3889_);
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr(lean_object* v_e_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_){
_start:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3898_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__0));
v___x_3899_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3, &l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3);
v___x_3900_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_3898_, v_e_3892_, v___x_3899_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___boxed(lean_object* v_e_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr(v_e_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
lean_dec(v_a_3905_);
lean_dec_ref(v_a_3904_);
lean_dec(v_a_3903_);
lean_dec_ref(v_a_3902_);
return v_res_3907_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1(void){
_start:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3909_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3);
v___x_3910_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__0));
v___x_3911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3910_);
lean_ctor_set(v___x_3911_, 1, v___x_3909_);
return v___x_3911_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instBool(void){
_start:
{
lean_object* v___x_3912_; 
v___x_3912_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1);
return v___x_3912_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1(void){
_start:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3914_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3);
v___x_3915_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__0));
v___x_3916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
lean_ctor_set(v___x_3916_, 1, v___x_3914_);
return v___x_3916_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instNat(void){
_start:
{
lean_object* v___x_3917_; 
v___x_3917_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1);
return v___x_3917_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1(void){
_start:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3919_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3);
v___x_3920_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__0));
v___x_3921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
lean_ctor_set(v___x_3921_, 1, v___x_3919_);
return v___x_3921_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instInt(void){
_start:
{
lean_object* v___x_3922_; 
v___x_3922_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1);
return v___x_3922_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1(void){
_start:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3924_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3);
v___x_3925_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__0));
v___x_3926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3925_);
lean_ctor_set(v___x_3926_, 1, v___x_3924_);
return v___x_3926_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instString(void){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1);
return v___x_3927_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1(void){
_start:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3929_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3);
v___x_3930_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__0));
v___x_3931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
lean_ctor_set(v___x_3931_, 1, v___x_3929_);
return v___x_3931_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instName(void){
_start:
{
lean_object* v___x_3932_; 
v___x_3932_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instOption___redArg(lean_object* v_inst_3933_){
_start:
{
lean_object* v_evalExpr_3934_; lean_object* v_expectedType_x3f_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3956_; 
v_evalExpr_3934_ = lean_ctor_get(v_inst_3933_, 0);
v_expectedType_x3f_3935_ = lean_ctor_get(v_inst_3933_, 1);
v_isSharedCheck_3956_ = !lean_is_exclusive(v_inst_3933_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3937_ = v_inst_3933_;
v_isShared_3938_ = v_isSharedCheck_3956_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_expectedType_x3f_3935_);
lean_inc(v_evalExpr_3934_);
lean_dec(v_inst_3933_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3956_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3939_; 
v___x_3939_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___boxed), 8, 2);
lean_closure_set(v___x_3939_, 0, lean_box(0));
lean_closure_set(v___x_3939_, 1, v_evalExpr_3934_);
if (lean_obj_tag(v_expectedType_x3f_3935_) == 0)
{
lean_object* v___x_3941_; 
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 0, v___x_3939_);
v___x_3941_ = v___x_3937_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3939_);
lean_ctor_set(v_reuseFailAlloc_3942_, 1, v_expectedType_x3f_3935_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
else
{
lean_object* v_val_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3955_; 
v_val_3943_ = lean_ctor_get(v_expectedType_x3f_3935_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v_expectedType_x3f_3935_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3945_ = v_expectedType_x3f_3935_;
v_isShared_3946_ = v_isSharedCheck_3955_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_val_3943_);
lean_dec(v_expectedType_x3f_3935_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3955_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3950_; 
v___x_3947_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2);
v___x_3948_ = l_Lean_Expr_app___override(v___x_3947_, v_val_3943_);
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 0, v___x_3948_);
v___x_3950_ = v___x_3945_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3948_);
v___x_3950_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
lean_object* v___x_3952_; 
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 1, v___x_3950_);
lean_ctor_set(v___x_3937_, 0, v___x_3939_);
v___x_3952_ = v___x_3937_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3939_);
lean_ctor_set(v_reuseFailAlloc_3953_, 1, v___x_3950_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instOption(lean_object* v_00_u03b1_3957_, lean_object* v_inst_3958_){
_start:
{
lean_object* v___x_3959_; 
v___x_3959_ = l_Lean_Elab_ConfigEval_EvalExpr_instOption___redArg(v_inst_3958_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0(lean_object* v_evalExpr_3960_, lean_object* v_e_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_){
_start:
{
uint8_t v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = 0;
v___x_3968_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(v_evalExpr_3960_, v_e_3961_, v___x_3967_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0___boxed(lean_object* v_evalExpr_3969_, lean_object* v_e_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0(v_evalExpr_3969_, v_e_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg(lean_object* v_inst_3977_){
_start:
{
lean_object* v_evalExpr_3978_; lean_object* v_expectedType_x3f_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_4000_; 
v_evalExpr_3978_ = lean_ctor_get(v_inst_3977_, 0);
v_expectedType_x3f_3979_ = lean_ctor_get(v_inst_3977_, 1);
v_isSharedCheck_4000_ = !lean_is_exclusive(v_inst_3977_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3981_ = v_inst_3977_;
v_isShared_3982_ = v_isSharedCheck_4000_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_expectedType_x3f_3979_);
lean_inc(v_evalExpr_3978_);
lean_dec(v_inst_3977_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_4000_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v___f_3983_; 
v___f_3983_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3983_, 0, v_evalExpr_3978_);
if (lean_obj_tag(v_expectedType_x3f_3979_) == 0)
{
lean_object* v___x_3985_; 
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 0, v___f_3983_);
v___x_3985_ = v___x_3981_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v___f_3983_);
lean_ctor_set(v_reuseFailAlloc_3986_, 1, v_expectedType_x3f_3979_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
else
{
lean_object* v_val_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3999_; 
v_val_3987_ = lean_ctor_get(v_expectedType_x3f_3979_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v_expectedType_x3f_3979_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3989_ = v_expectedType_x3f_3979_;
v_isShared_3990_ = v_isSharedCheck_3999_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_val_3987_);
lean_dec(v_expectedType_x3f_3979_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3999_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3994_; 
v___x_3991_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1);
v___x_3992_ = l_Lean_Expr_app___override(v___x_3991_, v_val_3987_);
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 0, v___x_3992_);
v___x_3994_ = v___x_3989_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3992_);
v___x_3994_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
lean_object* v___x_3996_; 
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 1, v___x_3994_);
lean_ctor_set(v___x_3981_, 0, v___f_3983_);
v___x_3996_ = v___x_3981_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v___f_3983_);
lean_ctor_set(v_reuseFailAlloc_3997_, 1, v___x_3994_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList(lean_object* v_00_u03b1_4001_, lean_object* v_inst_4002_){
_start:
{
lean_object* v___x_4003_; 
v___x_4003_ = l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg(v_inst_4002_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instArray___redArg(lean_object* v_inst_4004_){
_start:
{
lean_object* v_evalExpr_4005_; lean_object* v_expectedType_x3f_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4027_; 
v_evalExpr_4005_ = lean_ctor_get(v_inst_4004_, 0);
v_expectedType_x3f_4006_ = lean_ctor_get(v_inst_4004_, 1);
v_isSharedCheck_4027_ = !lean_is_exclusive(v_inst_4004_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4008_ = v_inst_4004_;
v_isShared_4009_ = v_isSharedCheck_4027_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_expectedType_x3f_4006_);
lean_inc(v_evalExpr_4005_);
lean_dec(v_inst_4004_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4027_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4010_; 
v___x_4010_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___boxed), 8, 2);
lean_closure_set(v___x_4010_, 0, lean_box(0));
lean_closure_set(v___x_4010_, 1, v_evalExpr_4005_);
if (lean_obj_tag(v_expectedType_x3f_4006_) == 0)
{
lean_object* v___x_4012_; 
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 0, v___x_4010_);
v___x_4012_ = v___x_4008_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v___x_4010_);
lean_ctor_set(v_reuseFailAlloc_4013_, 1, v_expectedType_x3f_4006_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
else
{
lean_object* v_val_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4026_; 
v_val_4014_ = lean_ctor_get(v_expectedType_x3f_4006_, 0);
v_isSharedCheck_4026_ = !lean_is_exclusive(v_expectedType_x3f_4006_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_4016_ = v_expectedType_x3f_4006_;
v_isShared_4017_ = v_isSharedCheck_4026_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_val_4014_);
lean_dec(v_expectedType_x3f_4006_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4026_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4021_; 
v___x_4018_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2);
v___x_4019_ = l_Lean_Expr_app___override(v___x_4018_, v_val_4014_);
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 0, v___x_4019_);
v___x_4021_ = v___x_4016_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v___x_4019_);
v___x_4021_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
lean_object* v___x_4023_; 
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 1, v___x_4021_);
lean_ctor_set(v___x_4008_, 0, v___x_4010_);
v___x_4023_ = v___x_4008_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v___x_4010_);
lean_ctor_set(v_reuseFailAlloc_4024_, 1, v___x_4021_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instArray(lean_object* v_00_u03b1_4028_, lean_object* v_inst_4029_){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_Lean_Elab_ConfigEval_EvalExpr_instArray___redArg(v_inst_4029_);
return v___x_4030_;
}
}
lean_object* runtime_initialize_Lean_Elab_ConfigEval_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ConfigEval_Instances(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
