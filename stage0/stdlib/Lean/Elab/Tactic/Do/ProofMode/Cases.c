// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Cases
// Imports: public import Lean.Elab.Tactic.Do.ProofMode.MGoal public import Std.Tactic.Do.Syntax import Lean.Elab.Tactic.Do.ProofMode.Pure import Lean.Elab.Tactic.Do.ProofMode.Focus import Lean.Elab.Tactic.Do.ProofMode.Basic
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_MCasesPat_parse(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(218, 187, 99, 122, 205, 56, 35, 106)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 222, 238, 124, 44, 25, 111, 81)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(158, 126, 187, 23, 173, 74, 254, 143)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 138, 196, 39, 216, 198, 126, 202)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(114, 36, 95, 227, 89, 89, 172, 229)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(144, 46, 212, 242, 236, 17, 131, 103)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 91, 243, 178, 107, 229, 236, 246)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 28, 66, 152, 156, 187, 94, 58)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 199, 97, 198, 237, 142, 216, 64)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Cases"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(132, 203, 16, 8, 13, 8, 155, 203)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(723085142) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(126, 81, 186, 219, 154, 145, 47, 235)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 106, 18, 162, 42, 71, 36, 248)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(65, 159, 14, 128, 226, 106, 69, 48)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(220, 181, 149, 67, 89, 19, 234, 81)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bientails"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(201, 51, 221, 5, 242, 131, 169, 118)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(6, 95, 37, 108, 69, 205, 235, 200)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "IsAnd"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value),LEAN_SCALAR_PTR_LITERAL(244, 83, 223, 78, 97, 64, 238, 46)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "to_and"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value),LEAN_SCALAR_PTR_LITERAL(244, 83, 223, 78, 97, 64, 238, 46)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8_value),LEAN_SCALAR_PTR_LITERAL(151, 250, 181, 158, 145, 194, 213, 0)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "add_goal"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 254, 223, 142, 199, 149, 90, 110)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 144, 153, 201, 175, 133, 231, 95)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Internal error: Hypotheses not a conjunction "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "exists"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 199, 194, 26, 176, 147, 16, 83)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Not an existential quantifier "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "and_1"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 254, 223, 142, 199, 149, 90, 110)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(51, 17, 228, 163, 140, 254, 212, 125)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Pure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "thm"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___boxed(lean_object**);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "IsPure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(237, 27, 197, 114, 200, 2, 153, 253)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 254, 223, 142, 199, 149, 90, 110)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 195, 94, 67, 62, 251, 248, 42)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clear"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 254, 223, 142, 199, 149, 90, 110)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 45, 21, 8, 254, 99, 220, 141)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "and_2"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 254, 223, 142, 199, 149, 90, 110)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 129, 169, 148, 64, 164, 21, 218)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "and_3"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 254, 223, 142, 199, 149, 90, 110)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(131, 147, 17, 85, 137, 95, 149, 65)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Neither a conjunction nor an existential quantifier "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "cannot further destruct a term after moving it to the Lean context"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(114, 97, 84, 180, 109, 220, 63, 60)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Not a disjunction "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "and_or_elim_r"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(141, 175, 37, 92, 202, 198, 164, 25)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__19_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__19___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__20___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__16_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__17;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mcases"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 192, 12, 149, 146, 251, 197, 23)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__20(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__19_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabMCases"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 109, 55, 23, 237, 161, 174, 103)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_70_; uint8_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_71_ = 0;
v___x_72_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_73_ = l_Lean_registerTraceClass(v___x_70_, v___x_71_, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2____boxed(lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_();
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(lean_object* v_u_105_, lean_object* v_00_u03c3s_106_, lean_object* v_H_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___y_114_; uint8_t v___y_115_; lean_object* v_a_120_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = l_Lean_Expr_consumeMData(v_H_107_);
v___x_124_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v___x_123_);
lean_dec_ref(v___x_123_);
if (lean_obj_tag(v___x_124_) == 1)
{
lean_object* v_val_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_164_; 
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
v_val_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_164_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_164_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_val_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_164_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v_snd_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_162_; 
v_snd_129_ = lean_ctor_get(v_val_125_, 1);
v_isSharedCheck_162_ = !lean_is_exclusive(v_val_125_);
if (v_isSharedCheck_162_ == 0)
{
lean_object* v_unused_163_; 
v_unused_163_ = lean_ctor_get(v_val_125_, 0);
lean_dec(v_unused_163_);
v___x_131_ = v_val_125_;
v_isShared_132_ = v_isSharedCheck_162_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_snd_129_);
lean_dec(v_val_125_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_162_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v_snd_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_160_; 
v_snd_133_ = lean_ctor_get(v_snd_129_, 1);
v_isSharedCheck_160_ = !lean_is_exclusive(v_snd_129_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v_snd_129_, 0);
lean_dec(v_unused_161_);
v___x_135_ = v_snd_129_;
v_isShared_136_ = v_isSharedCheck_160_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_snd_133_);
lean_dec(v_snd_129_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_160_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v_fst_137_; lean_object* v_snd_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_159_; 
v_fst_137_ = lean_ctor_get(v_snd_133_, 0);
v_snd_138_ = lean_ctor_get(v_snd_133_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_snd_133_);
if (v_isSharedCheck_159_ == 0)
{
v___x_140_ = v_snd_133_;
v_isShared_141_ = v_isSharedCheck_159_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_snd_138_);
lean_inc(v_fst_137_);
lean_dec(v_snd_133_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_159_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_142_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4));
v___x_143_ = lean_box(0);
if (v_isShared_132_ == 0)
{
lean_ctor_set_tag(v___x_131_, 1);
lean_ctor_set(v___x_131_, 1, v___x_143_);
lean_ctor_set(v___x_131_, 0, v_u_105_);
v___x_145_ = v___x_131_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_u_105_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_143_);
v___x_145_ = v_reuseFailAlloc_158_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_146_ = l_Lean_mkConst(v___x_142_, v___x_145_);
v___x_147_ = l_Lean_mkAppB(v___x_146_, v_00_u03c3s_106_, v_H_107_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v___x_147_);
lean_ctor_set(v___x_140_, 0, v_snd_138_);
v___x_149_ = v___x_140_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_snd_138_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v___x_147_);
v___x_149_ = v_reuseFailAlloc_157_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_151_; 
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v___x_149_);
lean_ctor_set(v___x_135_, 0, v_fst_137_);
v___x_151_ = v___x_135_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_fst_137_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v___x_149_);
v___x_151_ = v_reuseFailAlloc_156_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_153_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_151_);
v___x_153_ = v___x_127_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_155_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; 
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
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
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
lean_dec(v___x_124_);
v___x_165_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5));
v___x_166_ = lean_box(0);
v___x_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_167_, 0, v_u_105_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
lean_inc_ref(v___x_167_);
v___x_168_ = l_Lean_mkConst(v___x_165_, v___x_167_);
lean_inc_ref(v_00_u03c3s_106_);
v___x_169_ = l_Lean_Expr_app___override(v___x_168_, v_00_u03c3s_106_);
v___x_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
v___x_171_ = 0;
v___x_172_ = lean_box(0);
lean_inc_ref(v_a_108_);
lean_inc_ref(v___x_170_);
v___x_173_ = l_Lean_Meta_mkFreshExprMVar(v___x_170_, v___x_171_, v___x_172_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v___x_175_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_174_);
lean_dec_ref(v___x_173_);
lean_inc_ref(v_a_108_);
v___x_175_ = l_Lean_Meta_mkFreshExprMVar(v___x_170_, v___x_171_, v___x_172_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_202_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_202_ == 0)
{
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_202_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_202_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_180_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7));
lean_inc_ref(v___x_167_);
v___x_181_ = l_Lean_mkConst(v___x_180_, v___x_167_);
lean_inc(v_a_176_);
lean_inc(v_a_174_);
lean_inc_ref(v_H_107_);
lean_inc_ref(v_00_u03c3s_106_);
v___x_182_ = l_Lean_mkApp4(v___x_181_, v_00_u03c3s_106_, v_H_107_, v_a_174_, v_a_176_);
v___x_183_ = lean_box(0);
v___x_184_ = l_Lean_Meta_synthInstance(v___x_182_, v___x_183_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_200_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_200_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_200_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_200_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_189_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9));
v___x_190_ = l_Lean_mkConst(v___x_189_, v___x_167_);
lean_inc(v_a_176_);
lean_inc(v_a_174_);
v___x_191_ = l_Lean_mkApp5(v___x_190_, v_00_u03c3s_106_, v_H_107_, v_a_174_, v_a_176_, v_a_185_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v_a_176_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v_a_174_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
if (v_isShared_179_ == 0)
{
lean_ctor_set_tag(v___x_178_, 1);
lean_ctor_set(v___x_178_, 0, v___x_193_);
v___x_195_ = v___x_178_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_193_);
v___x_195_ = v_reuseFailAlloc_199_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_197_; 
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_195_);
v___x_197_ = v___x_187_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
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
else
{
lean_object* v_a_201_; 
lean_del_object(v___x_178_);
lean_dec(v_a_176_);
lean_dec(v_a_174_);
lean_dec_ref(v___x_167_);
lean_dec_ref(v_H_107_);
lean_dec_ref(v_00_u03c3s_106_);
v_a_201_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_201_);
lean_dec_ref(v___x_184_);
v_a_120_ = v_a_201_;
goto v___jp_119_;
}
}
}
else
{
lean_object* v_a_203_; 
lean_dec(v_a_174_);
lean_dec_ref(v___x_167_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec_ref(v_H_107_);
lean_dec_ref(v_00_u03c3s_106_);
v_a_203_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_a_203_);
lean_dec_ref(v___x_175_);
v_a_120_ = v_a_203_;
goto v___jp_119_;
}
}
else
{
lean_object* v_a_204_; 
lean_dec_ref(v___x_170_);
lean_dec_ref(v___x_167_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec_ref(v_H_107_);
lean_dec_ref(v_00_u03c3s_106_);
v_a_204_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_204_);
lean_dec_ref(v___x_173_);
v_a_120_ = v_a_204_;
goto v___jp_119_;
}
}
v___jp_113_:
{
if (v___y_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_dec_ref(v___y_114_);
v___x_116_ = lean_box(0);
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
return v___x_117_;
}
else
{
lean_object* v___x_118_; 
v___x_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_118_, 0, v___y_114_);
return v___x_118_;
}
}
v___jp_119_:
{
uint8_t v___x_121_; 
v___x_121_ = l_Lean_Exception_isInterrupt(v_a_120_);
if (v___x_121_ == 0)
{
uint8_t v___x_122_; 
lean_inc_ref(v_a_120_);
v___x_122_ = l_Lean_Exception_isRuntime(v_a_120_);
v___y_114_ = v_a_120_;
v___y_115_ = v___x_122_;
goto v___jp_113_;
}
else
{
v___y_114_ = v_a_120_;
v___y_115_ = v___x_121_;
goto v___jp_113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___boxed(lean_object* v_u_205_, lean_object* v_00_u03c3s_206_, lean_object* v_H_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(v_u_205_, v_00_u03c3s_206_, v_H_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal(lean_object* v_u_222_, lean_object* v_goals_223_, lean_object* v_00_u03c3s_224_, lean_object* v_T_225_, lean_object* v_Q_226_, lean_object* v_H_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v___x_233_; lean_object* v_fst_234_; lean_object* v_snd_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_275_; 
lean_inc_ref(v_H_227_);
lean_inc_ref(v_Q_226_);
lean_inc_ref(v_00_u03c3s_224_);
lean_inc(v_u_222_);
v___x_233_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_222_, v_00_u03c3s_224_, v_Q_226_, v_H_227_);
v_fst_234_ = lean_ctor_get(v___x_233_, 0);
v_snd_235_ = lean_ctor_get(v___x_233_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_275_ == 0)
{
v___x_237_ = v___x_233_;
v_isShared_238_ = v_isSharedCheck_275_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_snd_235_);
lean_inc(v_fst_234_);
lean_dec(v___x_233_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_275_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v_goal_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
lean_inc_ref(v_T_225_);
lean_inc(v_fst_234_);
lean_inc_ref(v_00_u03c3s_224_);
lean_inc(v_u_222_);
v_goal_239_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_goal_239_, 0, v_u_222_);
lean_ctor_set(v_goal_239_, 1, v_00_u03c3s_224_);
lean_ctor_set(v_goal_239_, 2, v_fst_234_);
lean_ctor_set(v_goal_239_, 3, v_T_225_);
v___x_240_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_239_);
v___x_241_ = lean_box(0);
v___x_242_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_240_, v___x_241_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_266_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_266_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_266_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_266_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_247_ = lean_st_ref_take(v_goals_223_);
v___x_248_ = l_Lean_Expr_mvarId_x21(v_a_243_);
v___x_249_ = lean_array_push(v___x_247_, v___x_248_);
v___x_250_ = lean_st_ref_set(v_goals_223_, v___x_249_);
v___x_251_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1));
v___x_252_ = lean_box(0);
lean_inc(v_u_222_);
v___x_253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_253_, 0, v_u_222_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = l_Lean_mkConst(v___x_251_, v___x_253_);
lean_inc_ref(v_T_225_);
lean_inc_ref(v_H_227_);
lean_inc_ref(v_Q_226_);
lean_inc_ref(v_00_u03c3s_224_);
v___x_255_ = l_Lean_mkApp7(v___x_254_, v_00_u03c3s_224_, v_fst_234_, v_Q_226_, v_H_227_, v_T_225_, v_snd_235_, v_a_243_);
lean_inc_ref(v_00_u03c3s_224_);
lean_inc(v_u_222_);
v___x_256_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_222_, v_00_u03c3s_224_, v_Q_226_, v_H_227_);
v___x_257_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_257_, 0, v_u_222_);
lean_ctor_set(v___x_257_, 1, v_00_u03c3s_224_);
lean_ctor_set(v___x_257_, 2, v___x_256_);
lean_ctor_set(v___x_257_, 3, v_T_225_);
v___x_258_ = lean_box(0);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v___x_255_);
lean_ctor_set(v___x_237_, 0, v___x_257_);
v___x_260_ = v___x_237_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_255_);
v___x_260_ = v_reuseFailAlloc_265_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_258_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_261_);
v___x_263_ = v___x_245_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_del_object(v___x_237_);
lean_dec(v_snd_235_);
lean_dec(v_fst_234_);
lean_dec_ref(v_H_227_);
lean_dec_ref(v_Q_226_);
lean_dec_ref(v_T_225_);
lean_dec_ref(v_00_u03c3s_224_);
lean_dec(v_u_222_);
v_a_267_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_242_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_242_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___boxed(lean_object* v_u_276_, lean_object* v_goals_277_, lean_object* v_00_u03c3s_278_, lean_object* v_T_279_, lean_object* v_Q_280_, lean_object* v_H_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal(v_u_276_, v_goals_277_, v_00_u03c3s_278_, v_T_279_, v_Q_280_, v_H_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec(v_goals_277_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(lean_object* v_msgData_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v___x_294_; lean_object* v_env_295_; lean_object* v___x_296_; lean_object* v_mctx_297_; lean_object* v_lctx_298_; lean_object* v_options_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_294_ = lean_st_ref_get(v___y_292_);
v_env_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc_ref(v_env_295_);
lean_dec(v___x_294_);
v___x_296_ = lean_st_ref_get(v___y_290_);
v_mctx_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc_ref(v_mctx_297_);
lean_dec(v___x_296_);
v_lctx_298_ = lean_ctor_get(v___y_289_, 2);
v_options_299_ = lean_ctor_get(v___y_291_, 2);
lean_inc_ref(v_options_299_);
lean_inc_ref(v_lctx_298_);
v___x_300_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_300_, 0, v_env_295_);
lean_ctor_set(v___x_300_, 1, v_mctx_297_);
lean_ctor_set(v___x_300_, 2, v_lctx_298_);
lean_ctor_set(v___x_300_, 3, v_options_299_);
v___x_301_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v_msgData_288_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0___boxed(lean_object* v_msgData_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msgData_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(lean_object* v_msg_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_ref_316_; lean_object* v___x_317_; lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_326_; 
v_ref_316_ = lean_ctor_get(v___y_313_, 5);
v___x_317_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
v_a_318_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_326_ == 0)
{
v___x_320_ = v___x_317_;
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_324_; 
lean_inc(v_ref_316_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v_ref_316_);
lean_ctor_set(v___x_322_, 1, v_a_318_);
if (v_isShared_321_ == 0)
{
lean_ctor_set_tag(v___x_320_, 1);
lean_ctor_set(v___x_320_, 0, v___x_322_);
v___x_324_ = v___x_320_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg___boxed(lean_object* v_msg_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v_msg_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
return v_res_333_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0));
v___x_336_ = l_Lean_stringToMessageData(v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(lean_object* v_goal_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_hyps_343_; lean_object* v___x_344_; 
v_hyps_343_ = lean_ctor_get(v_goal_337_, 2);
lean_inc_ref(v_hyps_343_);
lean_dec_ref(v_goal_337_);
v___x_344_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_hyps_343_);
if (lean_obj_tag(v___x_344_) == 1)
{
lean_object* v_val_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_354_; 
lean_dec_ref(v_hyps_343_);
v_val_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_354_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_354_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_val_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_354_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v_snd_349_; lean_object* v_snd_350_; lean_object* v___x_352_; 
v_snd_349_ = lean_ctor_get(v_val_345_, 1);
lean_inc(v_snd_349_);
lean_dec(v_val_345_);
v_snd_350_ = lean_ctor_get(v_snd_349_, 1);
lean_inc(v_snd_350_);
lean_dec(v_snd_349_);
if (v_isShared_348_ == 0)
{
lean_ctor_set_tag(v___x_347_, 0);
lean_ctor_set(v___x_347_, 0, v_snd_350_);
v___x_352_ = v___x_347_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_snd_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec(v___x_344_);
v___x_355_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1, &l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1);
v___x_356_ = l_Lean_MessageData_ofExpr(v_hyps_343_);
v___x_357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_355_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v___x_358_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_357_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___boxed(lean_object* v_goal_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_goal_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0(lean_object* v_00_u03b1_366_, lean_object* v_msg_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v_msg_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___boxed(lean_object* v_00_u03b1_374_, lean_object* v_msg_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0(v_00_u03b1_374_, v_msg_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0(lean_object* v___x_382_, lean_object* v_snd_383_, lean_object* v_k_384_, uint8_t v___x_385_, lean_object* v___x_386_, lean_object* v___x_387_, lean_object* v___x_388_, lean_object* v___x_389_, lean_object* v___x_390_, lean_object* v___x_391_, lean_object* v_H_392_, lean_object* v_x_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_lctx_399_; lean_object* v___x_400_; uint8_t v___x_401_; lean_object* v___x_402_; 
v_lctx_399_ = lean_ctor_get(v___y_394_, 2);
lean_inc_ref(v___x_382_);
v___x_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_382_);
v___x_401_ = 0;
lean_inc(v___y_397_);
lean_inc_ref(v___y_396_);
lean_inc(v___y_395_);
lean_inc_ref(v___y_394_);
lean_inc_ref(v_x_393_);
lean_inc_ref(v_lctx_399_);
v___x_402_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_snd_383_, v_lctx_399_, v_x_393_, v___x_400_, v___x_401_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v___x_403_; 
lean_dec_ref(v___x_402_);
lean_inc(v___y_397_);
lean_inc_ref(v___y_396_);
lean_inc(v___y_395_);
lean_inc_ref(v___y_394_);
lean_inc_ref(v_x_393_);
v___x_403_ = lean_apply_6(v_k_384_, v_x_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, lean_box(0));
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v_snd_405_; lean_object* v_fst_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_491_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
lean_dec_ref(v___x_403_);
v_snd_405_ = lean_ctor_get(v_a_404_, 1);
v_fst_406_ = lean_ctor_get(v_a_404_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v_a_404_);
if (v_isSharedCheck_491_ == 0)
{
v___x_408_ = v_a_404_;
v_isShared_409_ = v_isSharedCheck_491_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_snd_405_);
lean_inc(v_fst_406_);
lean_dec(v_a_404_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_491_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_fst_410_; lean_object* v_snd_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_490_; 
v_fst_410_ = lean_ctor_get(v_snd_405_, 0);
v_snd_411_ = lean_ctor_get(v_snd_405_, 1);
v_isSharedCheck_490_ = !lean_is_exclusive(v_snd_405_);
if (v_isSharedCheck_490_ == 0)
{
v___x_413_ = v_snd_405_;
v_isShared_414_ = v_isSharedCheck_490_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_snd_411_);
lean_inc(v_fst_410_);
lean_dec(v_snd_405_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_490_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; 
lean_inc(v_fst_410_);
v___x_415_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_410_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v_fst_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_480_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_416_);
lean_dec_ref(v___x_415_);
v_fst_417_ = lean_ctor_get(v_a_416_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v_a_416_);
if (v_isSharedCheck_480_ == 0)
{
lean_object* v_unused_481_; 
v_unused_481_ = lean_ctor_get(v_a_416_, 1);
lean_dec(v_unused_481_);
v___x_419_ = v_a_416_;
v_isShared_420_ = v_isSharedCheck_480_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_fst_417_);
lean_dec(v_a_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_480_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; 
lean_inc(v___y_397_);
lean_inc_ref(v___y_396_);
lean_inc(v___y_395_);
lean_inc_ref(v___y_394_);
lean_inc_ref(v___x_382_);
v___x_421_ = l_Lean_Meta_getLevel(v___x_382_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; lean_object* v___x_427_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_a_422_);
lean_dec_ref(v___x_421_);
v___x_423_ = lean_unsigned_to_nat(1u);
v___x_424_ = lean_mk_empty_array_with_capacity(v___x_423_);
v___x_425_ = lean_array_push(v___x_424_, v_x_393_);
v___x_426_ = 1;
v___x_427_ = l_Lean_Meta_mkLambdaFVars(v___x_425_, v_snd_411_, v___x_401_, v___x_385_, v___x_401_, v___x_385_, v___x_426_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec_ref(v___x_425_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_463_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_463_ == 0)
{
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_463_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_463_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v_u_432_; lean_object* v_00_u03c3s_433_; lean_object* v_target_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_461_; 
v_u_432_ = lean_ctor_get(v_fst_410_, 0);
v_00_u03c3s_433_ = lean_ctor_get(v_fst_410_, 1);
v_target_434_ = lean_ctor_get(v_fst_410_, 3);
v_isSharedCheck_461_ = !lean_is_exclusive(v_fst_410_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; 
v_unused_462_ = lean_ctor_get(v_fst_410_, 2);
lean_dec(v_unused_462_);
v___x_436_ = v_fst_410_;
v_isShared_437_ = v_isSharedCheck_461_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_target_434_);
lean_inc(v_00_u03c3s_433_);
lean_inc(v_u_432_);
lean_dec(v_fst_410_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_461_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_438_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_439_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_440_ = l_Lean_Name_mkStr6(v___x_386_, v___x_387_, v___x_388_, v___x_438_, v___x_439_, v___x_389_);
v___x_441_ = lean_box(0);
if (v_isShared_409_ == 0)
{
lean_ctor_set_tag(v___x_408_, 1);
lean_ctor_set(v___x_408_, 1, v___x_441_);
lean_ctor_set(v___x_408_, 0, v_a_422_);
v___x_443_ = v___x_408_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_422_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_441_);
v___x_443_ = v_reuseFailAlloc_460_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
lean_inc(v_u_432_);
v___x_444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_444_, 0, v_u_432_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = l_Lean_mkConst(v___x_440_, v___x_444_);
lean_inc_ref(v_target_434_);
lean_inc(v_fst_417_);
lean_inc_ref(v___x_390_);
v___x_446_ = l_Lean_mkApp6(v___x_445_, v___x_390_, v___x_382_, v_fst_417_, v___x_391_, v_target_434_, v_a_428_);
lean_inc(v_u_432_);
v___x_447_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_432_, v___x_390_, v_fst_417_, v_H_392_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 2, v___x_447_);
v___x_449_ = v___x_436_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_u_432_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_00_u03c3s_433_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_459_, 3, v_target_434_);
v___x_449_ = v_reuseFailAlloc_459_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_451_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 1, v___x_446_);
lean_ctor_set(v___x_419_, 0, v___x_449_);
v___x_451_ = v___x_419_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v___x_446_);
v___x_451_ = v_reuseFailAlloc_458_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_453_; 
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v___x_451_);
lean_ctor_set(v___x_413_, 0, v_fst_406_);
v___x_453_ = v___x_413_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_fst_406_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_451_);
v___x_453_ = v_reuseFailAlloc_457_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_455_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_453_);
v___x_455_ = v___x_430_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
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
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec(v_a_422_);
lean_del_object(v___x_419_);
lean_dec(v_fst_417_);
lean_del_object(v___x_413_);
lean_dec(v_fst_410_);
lean_del_object(v___x_408_);
lean_dec(v_fst_406_);
lean_dec_ref(v_H_392_);
lean_dec_ref(v___x_391_);
lean_dec_ref(v___x_390_);
lean_dec_ref(v___x_389_);
lean_dec_ref(v___x_388_);
lean_dec_ref(v___x_387_);
lean_dec_ref(v___x_386_);
lean_dec_ref(v___x_382_);
v_a_464_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_427_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_427_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_del_object(v___x_419_);
lean_dec(v_fst_417_);
lean_del_object(v___x_413_);
lean_dec(v_snd_411_);
lean_dec(v_fst_410_);
lean_del_object(v___x_408_);
lean_dec(v_fst_406_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec_ref(v_x_393_);
lean_dec_ref(v_H_392_);
lean_dec_ref(v___x_391_);
lean_dec_ref(v___x_390_);
lean_dec_ref(v___x_389_);
lean_dec_ref(v___x_388_);
lean_dec_ref(v___x_387_);
lean_dec_ref(v___x_386_);
lean_dec_ref(v___x_382_);
v_a_472_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_421_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_421_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_del_object(v___x_413_);
lean_dec(v_snd_411_);
lean_dec(v_fst_410_);
lean_del_object(v___x_408_);
lean_dec(v_fst_406_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec_ref(v_x_393_);
lean_dec_ref(v_H_392_);
lean_dec_ref(v___x_391_);
lean_dec_ref(v___x_390_);
lean_dec_ref(v___x_389_);
lean_dec_ref(v___x_388_);
lean_dec_ref(v___x_387_);
lean_dec_ref(v___x_386_);
lean_dec_ref(v___x_382_);
v_a_482_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_415_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_415_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
}
else
{
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec_ref(v_x_393_);
lean_dec_ref(v_H_392_);
lean_dec_ref(v___x_391_);
lean_dec_ref(v___x_390_);
lean_dec_ref(v___x_389_);
lean_dec_ref(v___x_388_);
lean_dec_ref(v___x_387_);
lean_dec_ref(v___x_386_);
lean_dec_ref(v___x_382_);
return v___x_403_;
}
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec_ref(v_x_393_);
lean_dec_ref(v_H_392_);
lean_dec_ref(v___x_391_);
lean_dec_ref(v___x_390_);
lean_dec_ref(v___x_389_);
lean_dec_ref(v___x_388_);
lean_dec_ref(v___x_387_);
lean_dec_ref(v___x_386_);
lean_dec_ref(v_k_384_);
lean_dec_ref(v___x_382_);
v_a_492_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_402_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_402_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_500_ = _args[0];
lean_object* v_snd_501_ = _args[1];
lean_object* v_k_502_ = _args[2];
lean_object* v___x_503_ = _args[3];
lean_object* v___x_504_ = _args[4];
lean_object* v___x_505_ = _args[5];
lean_object* v___x_506_ = _args[6];
lean_object* v___x_507_ = _args[7];
lean_object* v___x_508_ = _args[8];
lean_object* v___x_509_ = _args[9];
lean_object* v_H_510_ = _args[10];
lean_object* v_x_511_ = _args[11];
lean_object* v___y_512_ = _args[12];
lean_object* v___y_513_ = _args[13];
lean_object* v___y_514_ = _args[14];
lean_object* v___y_515_ = _args[15];
lean_object* v___y_516_ = _args[16];
_start:
{
uint8_t v___x_2385__boxed_517_; lean_object* v_res_518_; 
v___x_2385__boxed_517_ = lean_unbox(v___x_503_);
v_res_518_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0(v___x_500_, v_snd_501_, v_k_502_, v___x_2385__boxed_517_, v___x_504_, v___x_505_, v___x_506_, v___x_507_, v___x_508_, v___x_509_, v_H_510_, v_x_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0(lean_object* v_k_519_, lean_object* v_b_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = lean_apply_6(v_k_519_, v_b_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, lean_box(0));
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_527_, lean_object* v_b_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0(v_k_527_, v_b_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(lean_object* v_name_535_, uint8_t v_bi_536_, lean_object* v_type_537_, lean_object* v_k_538_, uint8_t v_kind_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___f_545_; lean_object* v___x_546_; 
v___f_545_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_545_, 0, v_k_538_);
v___x_546_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_535_, v_bi_536_, v_type_537_, v___f_545_, v_kind_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
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
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
v_a_555_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_546_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_546_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___boxed(lean_object* v_name_563_, lean_object* v_bi_564_, lean_object* v_type_565_, lean_object* v_k_566_, lean_object* v_kind_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
uint8_t v_bi_boxed_573_; uint8_t v_kind_boxed_574_; lean_object* v_res_575_; 
v_bi_boxed_573_ = lean_unbox(v_bi_564_);
v_kind_boxed_574_ = lean_unbox(v_kind_567_);
v_res_575_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_563_, v_bi_boxed_573_, v_type_565_, v_k_566_, v_kind_boxed_574_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(lean_object* v_name_576_, lean_object* v_type_577_, lean_object* v_k_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
uint8_t v___x_584_; uint8_t v___x_585_; lean_object* v___x_586_; 
v___x_584_ = 0;
v___x_585_ = 0;
v___x_586_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_576_, v___x_584_, v_type_577_, v_k_578_, v___x_585_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg___boxed(lean_object* v_name_587_, lean_object* v_type_588_, lean_object* v_k_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_name_587_, v_type_588_, v_k_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
return v_res_595_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2));
v___x_604_ = l_Lean_stringToMessageData(v___x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(lean_object* v_H_605_, lean_object* v_name_606_, lean_object* v_k_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_613_ = l_Lean_Expr_consumeMData(v_H_605_);
v___x_614_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0));
v___x_615_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_616_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1));
v___x_617_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0));
v___x_618_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1));
v___x_619_ = lean_unsigned_to_nat(3u);
v___x_620_ = l_Lean_Expr_isAppOfArity(v___x_613_, v___x_618_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
lean_dec_ref(v___x_613_);
lean_dec_ref(v_k_607_);
lean_dec(v_name_606_);
v___x_621_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3);
v___x_622_ = l_Lean_MessageData_ofExpr(v_H_605_);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_623_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
return v___x_624_;
}
else
{
lean_object* v___x_625_; 
lean_inc(v_a_611_);
lean_inc_ref(v_a_610_);
v___x_625_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_name_606_, v_a_610_, v_a_611_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v_fst_627_; lean_object* v_snd_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___f_635_; lean_object* v___x_636_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref(v___x_625_);
v_fst_627_ = lean_ctor_get(v_a_626_, 0);
lean_inc(v_fst_627_);
v_snd_628_ = lean_ctor_get(v_a_626_, 1);
lean_inc(v_snd_628_);
lean_dec(v_a_626_);
v___x_629_ = l_Lean_Expr_appFn_x21(v___x_613_);
v___x_630_ = l_Lean_Expr_appFn_x21(v___x_629_);
v___x_631_ = l_Lean_Expr_appArg_x21(v___x_630_);
lean_dec_ref(v___x_630_);
v___x_632_ = l_Lean_Expr_appArg_x21(v___x_629_);
lean_dec_ref(v___x_629_);
v___x_633_ = l_Lean_Expr_appArg_x21(v___x_613_);
lean_dec_ref(v___x_613_);
v___x_634_ = lean_box(v___x_620_);
lean_inc_ref(v___x_631_);
v___f_635_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0___boxed), 17, 11);
lean_closure_set(v___f_635_, 0, v___x_631_);
lean_closure_set(v___f_635_, 1, v_snd_628_);
lean_closure_set(v___f_635_, 2, v_k_607_);
lean_closure_set(v___f_635_, 3, v___x_634_);
lean_closure_set(v___f_635_, 4, v___x_614_);
lean_closure_set(v___f_635_, 5, v___x_615_);
lean_closure_set(v___f_635_, 6, v___x_616_);
lean_closure_set(v___f_635_, 7, v___x_617_);
lean_closure_set(v___f_635_, 8, v___x_632_);
lean_closure_set(v___f_635_, 9, v___x_633_);
lean_closure_set(v___f_635_, 10, v_H_605_);
v___x_636_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_fst_627_, v___x_631_, v___f_635_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
return v___x_636_;
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec_ref(v___x_613_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec_ref(v_k_607_);
lean_dec_ref(v_H_605_);
v_a_637_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_625_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_625_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___boxed(lean_object* v_H_645_, lean_object* v_name_646_, lean_object* v_k_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(v_H_645_, v_name_646_, v_k_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists(lean_object* v_00_u03b1_654_, lean_object* v_H_655_, lean_object* v_name_656_, lean_object* v_k_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(v_H_655_, v_name_656_, v_k_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___boxed(lean_object* v_00_u03b1_664_, lean_object* v_H_665_, lean_object* v_name_666_, lean_object* v_k_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists(v_00_u03b1_664_, v_H_665_, v_name_666_, v_k_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0(lean_object* v_00_u03b1_674_, lean_object* v_name_675_, uint8_t v_bi_676_, lean_object* v_type_677_, lean_object* v_k_678_, uint8_t v_kind_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_675_, v_bi_676_, v_type_677_, v_k_678_, v_kind_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___boxed(lean_object* v_00_u03b1_686_, lean_object* v_name_687_, lean_object* v_bi_688_, lean_object* v_type_689_, lean_object* v_k_690_, lean_object* v_kind_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
uint8_t v_bi_boxed_697_; uint8_t v_kind_boxed_698_; lean_object* v_res_699_; 
v_bi_boxed_697_ = lean_unbox(v_bi_688_);
v_kind_boxed_698_ = lean_unbox(v_kind_691_);
v_res_699_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0(v_00_u03b1_686_, v_name_687_, v_bi_boxed_697_, v_type_689_, v_k_690_, v_kind_boxed_698_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0(lean_object* v_00_u03b1_700_, lean_object* v_name_701_, lean_object* v_type_702_, lean_object* v_k_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_name_701_, v_type_702_, v_k_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___boxed(lean_object* v_00_u03b1_710_, lean_object* v_name_711_, lean_object* v_type_712_, lean_object* v_k_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0(v_00_u03b1_710_, v_name_711_, v_type_712_, v_k_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
return v_res_719_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = lean_box(0);
v___x_721_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v___x_720_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg(){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0);
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___boxed(lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0(lean_object* v_00_u03b1_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___boxed(lean_object* v_00_u03b1_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0(v_00_u03b1_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; lean_object* v_ngen_745_; lean_object* v_namePrefix_746_; lean_object* v_idx_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_776_; 
v___x_744_ = lean_st_ref_get(v___y_742_);
v_ngen_745_ = lean_ctor_get(v___x_744_, 2);
lean_inc_ref(v_ngen_745_);
lean_dec(v___x_744_);
v_namePrefix_746_ = lean_ctor_get(v_ngen_745_, 0);
v_idx_747_ = lean_ctor_get(v_ngen_745_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v_ngen_745_);
if (v_isSharedCheck_776_ == 0)
{
v___x_749_ = v_ngen_745_;
v_isShared_750_ = v_isSharedCheck_776_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_idx_747_);
lean_inc(v_namePrefix_746_);
lean_dec(v_ngen_745_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_776_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v_env_752_; lean_object* v_nextMacroScope_753_; lean_object* v_auxDeclNGen_754_; lean_object* v_traceState_755_; lean_object* v_cache_756_; lean_object* v_messages_757_; lean_object* v_infoState_758_; lean_object* v_snapshotTasks_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_774_; 
v___x_751_ = lean_st_ref_take(v___y_742_);
v_env_752_ = lean_ctor_get(v___x_751_, 0);
v_nextMacroScope_753_ = lean_ctor_get(v___x_751_, 1);
v_auxDeclNGen_754_ = lean_ctor_get(v___x_751_, 3);
v_traceState_755_ = lean_ctor_get(v___x_751_, 4);
v_cache_756_ = lean_ctor_get(v___x_751_, 5);
v_messages_757_ = lean_ctor_get(v___x_751_, 6);
v_infoState_758_ = lean_ctor_get(v___x_751_, 7);
v_snapshotTasks_759_ = lean_ctor_get(v___x_751_, 8);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v___x_751_, 2);
lean_dec(v_unused_775_);
v___x_761_ = v___x_751_;
v_isShared_762_ = v_isSharedCheck_774_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_snapshotTasks_759_);
lean_inc(v_infoState_758_);
lean_inc(v_messages_757_);
lean_inc(v_cache_756_);
lean_inc(v_traceState_755_);
lean_inc(v_auxDeclNGen_754_);
lean_inc(v_nextMacroScope_753_);
lean_inc(v_env_752_);
lean_dec(v___x_751_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_774_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_r_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
lean_inc(v_idx_747_);
lean_inc(v_namePrefix_746_);
v_r_763_ = l_Lean_Name_num___override(v_namePrefix_746_, v_idx_747_);
v___x_764_ = lean_unsigned_to_nat(1u);
v___x_765_ = lean_nat_add(v_idx_747_, v___x_764_);
lean_dec(v_idx_747_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_765_);
v___x_767_ = v___x_749_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_namePrefix_746_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_765_);
v___x_767_ = v_reuseFailAlloc_773_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 2, v___x_767_);
v___x_769_ = v___x_761_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_env_752_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_nextMacroScope_753_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v_auxDeclNGen_754_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v_traceState_755_);
lean_ctor_set(v_reuseFailAlloc_772_, 5, v_cache_756_);
lean_ctor_set(v_reuseFailAlloc_772_, 6, v_messages_757_);
lean_ctor_set(v_reuseFailAlloc_772_, 7, v_infoState_758_);
lean_ctor_set(v_reuseFailAlloc_772_, 8, v_snapshotTasks_759_);
v___x_769_ = v_reuseFailAlloc_772_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_st_ref_set(v___y_742_, v___x_769_);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v_r_763_);
return v___x_771_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg___boxed(lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v___y_777_);
lean_dec(v___y_777_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v___y_783_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___boxed(lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0(lean_object* v_u_800_, lean_object* v_00_u03c3s_801_, lean_object* v_H_u2081_x27_802_, lean_object* v_k_803_, lean_object* v_H_u2082_x27_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_810_; lean_object* v_fst_811_; lean_object* v_snd_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_890_; 
lean_inc_ref(v_H_u2082_x27_804_);
lean_inc_ref(v_H_u2081_x27_802_);
lean_inc_ref(v_00_u03c3s_801_);
lean_inc(v_u_800_);
v___x_810_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_800_, v_00_u03c3s_801_, v_H_u2081_x27_802_, v_H_u2082_x27_804_);
v_fst_811_ = lean_ctor_get(v___x_810_, 0);
v_snd_812_ = lean_ctor_get(v___x_810_, 1);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_890_ == 0)
{
v___x_814_ = v___x_810_;
v_isShared_815_ = v_isSharedCheck_890_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_snd_812_);
lean_inc(v_fst_811_);
lean_dec(v___x_810_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_890_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; 
lean_inc(v___y_808_);
lean_inc_ref(v___y_807_);
lean_inc(v___y_806_);
lean_inc_ref(v___y_805_);
lean_inc(v_fst_811_);
v___x_816_ = lean_apply_6(v_k_803_, v_fst_811_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, lean_box(0));
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v_snd_818_; lean_object* v_fst_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_881_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref(v___x_816_);
v_snd_818_ = lean_ctor_get(v_a_817_, 1);
v_fst_819_ = lean_ctor_get(v_a_817_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v_a_817_);
if (v_isSharedCheck_881_ == 0)
{
v___x_821_ = v_a_817_;
v_isShared_822_ = v_isSharedCheck_881_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_snd_818_);
lean_inc(v_fst_819_);
lean_dec(v_a_817_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_881_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v_fst_823_; lean_object* v_snd_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_880_; 
v_fst_823_ = lean_ctor_get(v_snd_818_, 0);
v_snd_824_ = lean_ctor_get(v_snd_818_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v_snd_818_);
if (v_isSharedCheck_880_ == 0)
{
v___x_826_ = v_snd_818_;
v_isShared_827_ = v_isSharedCheck_880_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_snd_824_);
lean_inc(v_fst_823_);
lean_dec(v_snd_818_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_880_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; 
lean_inc(v_fst_823_);
v___x_828_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_823_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_871_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_871_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_871_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_871_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v_fst_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_869_; 
v_fst_833_ = lean_ctor_get(v_a_829_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v_a_829_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; 
v_unused_870_ = lean_ctor_get(v_a_829_, 1);
lean_dec(v_unused_870_);
v___x_835_ = v_a_829_;
v_isShared_836_ = v_isSharedCheck_869_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_fst_833_);
lean_dec(v_a_829_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_869_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v_u_837_; lean_object* v_00_u03c3s_838_; lean_object* v_target_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_867_; 
v_u_837_ = lean_ctor_get(v_fst_823_, 0);
v_00_u03c3s_838_ = lean_ctor_get(v_fst_823_, 1);
v_target_839_ = lean_ctor_get(v_fst_823_, 3);
v_isSharedCheck_867_ = !lean_is_exclusive(v_fst_823_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; 
v_unused_868_ = lean_ctor_get(v_fst_823_, 2);
lean_dec(v_unused_868_);
v___x_841_ = v_fst_823_;
v_isShared_842_ = v_isSharedCheck_867_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_target_839_);
lean_inc(v_00_u03c3s_838_);
lean_inc(v_u_837_);
lean_dec(v_fst_823_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_867_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_843_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1));
v___x_844_ = lean_box(0);
lean_inc(v_u_800_);
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 1);
lean_ctor_set(v___x_814_, 1, v___x_844_);
lean_ctor_set(v___x_814_, 0, v_u_800_);
v___x_846_ = v___x_814_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_u_800_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v___x_844_);
v___x_846_ = v_reuseFailAlloc_866_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_847_ = l_Lean_mkConst(v___x_843_, v___x_846_);
lean_inc_ref(v_target_839_);
lean_inc_ref(v_H_u2082_x27_804_);
lean_inc_ref(v_H_u2081_x27_802_);
lean_inc(v_fst_833_);
lean_inc_ref(v_00_u03c3s_801_);
v___x_848_ = l_Lean_mkApp8(v___x_847_, v_00_u03c3s_801_, v_fst_833_, v_H_u2081_x27_802_, v_H_u2082_x27_804_, v_fst_811_, v_target_839_, v_snd_812_, v_snd_824_);
lean_inc(v_fst_833_);
lean_inc_ref(v_00_u03c3s_801_);
lean_inc(v_u_800_);
v___x_849_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_800_, v_00_u03c3s_801_, v_fst_833_, v_H_u2081_x27_802_);
v___x_850_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_800_, v_00_u03c3s_801_, v___x_849_, v_H_u2082_x27_804_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 2, v___x_850_);
v___x_852_ = v___x_841_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_u_837_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_00_u03c3s_838_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_865_, 3, v_target_839_);
v___x_852_ = v_reuseFailAlloc_865_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_854_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v_fst_833_);
lean_ctor_set(v___x_835_, 0, v_fst_819_);
v___x_854_ = v___x_835_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_fst_819_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_fst_833_);
v___x_854_ = v_reuseFailAlloc_864_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_856_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 1, v___x_848_);
lean_ctor_set(v___x_826_, 0, v___x_852_);
v___x_856_ = v___x_826_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_848_);
v___x_856_ = v_reuseFailAlloc_863_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_858_; 
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 1, v___x_856_);
lean_ctor_set(v___x_821_, 0, v___x_854_);
v___x_858_ = v___x_821_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_856_);
v___x_858_ = v_reuseFailAlloc_862_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_860_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_858_);
v___x_860_ = v___x_831_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
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
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_del_object(v___x_826_);
lean_dec(v_snd_824_);
lean_dec(v_fst_823_);
lean_del_object(v___x_821_);
lean_dec(v_fst_819_);
lean_del_object(v___x_814_);
lean_dec(v_snd_812_);
lean_dec(v_fst_811_);
lean_dec_ref(v_H_u2082_x27_804_);
lean_dec_ref(v_H_u2081_x27_802_);
lean_dec_ref(v_00_u03c3s_801_);
lean_dec(v_u_800_);
v_a_872_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_828_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_828_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_del_object(v___x_814_);
lean_dec(v_snd_812_);
lean_dec(v_fst_811_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec_ref(v_H_u2082_x27_804_);
lean_dec_ref(v_H_u2081_x27_802_);
lean_dec_ref(v_00_u03c3s_801_);
lean_dec(v_u_800_);
v_a_882_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_816_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_816_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___boxed(lean_object* v_u_891_, lean_object* v_00_u03c3s_892_, lean_object* v_H_u2081_x27_893_, lean_object* v_k_894_, lean_object* v_H_u2082_x27_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0(v_u_891_, v_00_u03c3s_892_, v_H_u2081_x27_893_, v_k_894_, v_H_u2082_x27_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(lean_object* v_a_904_, lean_object* v_snd_905_, lean_object* v_k_906_, lean_object* v___x_907_, lean_object* v___x_908_, lean_object* v___x_909_, lean_object* v___x_910_, lean_object* v___x_911_, lean_object* v_00_u03c3s_912_, lean_object* v_hyp_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_h_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_lctx_922_; lean_object* v___x_923_; uint8_t v___x_924_; lean_object* v___x_925_; 
v_lctx_922_ = lean_ctor_get(v___y_917_, 2);
lean_inc_ref(v_a_904_);
v___x_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_923_, 0, v_a_904_);
v___x_924_ = 0;
lean_inc(v___y_920_);
lean_inc_ref(v___y_919_);
lean_inc(v___y_918_);
lean_inc_ref(v___y_917_);
lean_inc_ref(v_h_916_);
lean_inc_ref(v_lctx_922_);
v___x_925_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_snd_905_, v_lctx_922_, v_h_916_, v___x_923_, v___x_924_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v___x_926_; 
lean_dec_ref(v___x_925_);
lean_inc(v___y_920_);
lean_inc_ref(v___y_919_);
lean_inc(v___y_918_);
lean_inc_ref(v___y_917_);
lean_inc_ref(v_h_916_);
lean_inc_ref(v_a_904_);
v___x_926_ = lean_apply_7(v_k_906_, v_a_904_, v_h_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, lean_box(0));
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v_snd_928_; lean_object* v_fst_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_984_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref(v___x_926_);
v_snd_928_ = lean_ctor_get(v_a_927_, 1);
v_fst_929_ = lean_ctor_get(v_a_927_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v_a_927_);
if (v_isSharedCheck_984_ == 0)
{
v___x_931_ = v_a_927_;
v_isShared_932_ = v_isSharedCheck_984_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_snd_928_);
lean_inc(v_fst_929_);
lean_dec(v_a_927_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_984_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v_fst_933_; lean_object* v_snd_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_983_; 
v_fst_933_ = lean_ctor_get(v_snd_928_, 0);
v_snd_934_ = lean_ctor_get(v_snd_928_, 1);
v_isSharedCheck_983_ = !lean_is_exclusive(v_snd_928_);
if (v_isSharedCheck_983_ == 0)
{
v___x_936_ = v_snd_928_;
v_isShared_937_ = v_isSharedCheck_983_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_snd_934_);
lean_inc(v_fst_933_);
lean_dec(v_snd_928_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_983_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; uint8_t v___x_942_; lean_object* v___x_943_; 
v___x_938_ = lean_unsigned_to_nat(1u);
v___x_939_ = lean_mk_empty_array_with_capacity(v___x_938_);
v___x_940_ = lean_array_push(v___x_939_, v_h_916_);
v___x_941_ = 1;
v___x_942_ = 1;
v___x_943_ = l_Lean_Meta_mkLambdaFVars(v___x_940_, v_snd_934_, v___x_924_, v___x_941_, v___x_924_, v___x_941_, v___x_942_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec_ref(v___x_940_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_974_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_974_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_974_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_974_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_u_948_; lean_object* v_00_u03c3s_949_; lean_object* v_hyps_950_; lean_object* v_target_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_973_; 
v_u_948_ = lean_ctor_get(v_fst_933_, 0);
v_00_u03c3s_949_ = lean_ctor_get(v_fst_933_, 1);
v_hyps_950_ = lean_ctor_get(v_fst_933_, 2);
v_target_951_ = lean_ctor_get(v_fst_933_, 3);
v_isSharedCheck_973_ = !lean_is_exclusive(v_fst_933_);
if (v_isSharedCheck_973_ == 0)
{
v___x_953_ = v_fst_933_;
v_isShared_954_ = v_isSharedCheck_973_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_target_951_);
lean_inc(v_hyps_950_);
lean_inc(v_00_u03c3s_949_);
lean_inc(v_u_948_);
lean_dec(v_fst_933_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_973_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v_prf_959_; lean_object* v___x_960_; lean_object* v_goal_962_; 
v___x_955_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0));
v___x_956_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1));
v___x_957_ = l_Lean_Name_mkStr6(v___x_907_, v___x_908_, v___x_909_, v___x_910_, v___x_955_, v___x_956_);
v___x_958_ = l_Lean_mkConst(v___x_957_, v___x_911_);
lean_inc_ref(v_target_951_);
lean_inc_ref(v_hyp_913_);
lean_inc_ref(v_hyps_950_);
lean_inc_ref(v_00_u03c3s_912_);
v_prf_959_ = l_Lean_mkApp7(v___x_958_, v_00_u03c3s_912_, v_hyps_950_, v_hyp_913_, v_target_951_, v_a_904_, v_a_914_, v_a_944_);
v___x_960_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_a_915_, v_00_u03c3s_912_, v_hyps_950_, v_hyp_913_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 2, v___x_960_);
v_goal_962_ = v___x_953_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_u_948_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_00_u03c3s_949_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_972_, 3, v_target_951_);
v_goal_962_ = v_reuseFailAlloc_972_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_964_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 1, v_prf_959_);
lean_ctor_set(v___x_936_, 0, v_goal_962_);
v___x_964_ = v___x_936_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_goal_962_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_prf_959_);
v___x_964_ = v_reuseFailAlloc_971_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_966_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v___x_964_);
v___x_966_ = v___x_931_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_fst_929_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_964_);
v___x_966_ = v_reuseFailAlloc_970_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_968_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_966_);
v___x_968_ = v___x_946_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_del_object(v___x_936_);
lean_dec(v_fst_933_);
lean_del_object(v___x_931_);
lean_dec(v_fst_929_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec_ref(v_hyp_913_);
lean_dec_ref(v_00_u03c3s_912_);
lean_dec(v___x_911_);
lean_dec_ref(v___x_910_);
lean_dec_ref(v___x_909_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v___x_907_);
lean_dec_ref(v_a_904_);
v_a_975_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_943_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_943_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
}
else
{
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec_ref(v_h_916_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec_ref(v_hyp_913_);
lean_dec_ref(v_00_u03c3s_912_);
lean_dec(v___x_911_);
lean_dec_ref(v___x_910_);
lean_dec_ref(v___x_909_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v___x_907_);
lean_dec_ref(v_a_904_);
return v___x_926_;
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec_ref(v_h_916_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec_ref(v_hyp_913_);
lean_dec_ref(v_00_u03c3s_912_);
lean_dec(v___x_911_);
lean_dec_ref(v___x_910_);
lean_dec_ref(v___x_909_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v___x_907_);
lean_dec_ref(v_k_906_);
lean_dec_ref(v_a_904_);
v_a_985_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_925_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_925_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_a_993_ = _args[0];
lean_object* v_snd_994_ = _args[1];
lean_object* v_k_995_ = _args[2];
lean_object* v___x_996_ = _args[3];
lean_object* v___x_997_ = _args[4];
lean_object* v___x_998_ = _args[5];
lean_object* v___x_999_ = _args[6];
lean_object* v___x_1000_ = _args[7];
lean_object* v_00_u03c3s_1001_ = _args[8];
lean_object* v_hyp_1002_ = _args[9];
lean_object* v_a_1003_ = _args[10];
lean_object* v_a_1004_ = _args[11];
lean_object* v_h_1005_ = _args[12];
lean_object* v___y_1006_ = _args[13];
lean_object* v___y_1007_ = _args[14];
lean_object* v___y_1008_ = _args[15];
lean_object* v___y_1009_ = _args[16];
lean_object* v___y_1010_ = _args[17];
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(v_a_993_, v_snd_994_, v_k_995_, v___x_996_, v___x_997_, v___x_998_, v___x_999_, v___x_1000_, v_00_u03c3s_1001_, v_hyp_1002_, v_a_1003_, v_a_1004_, v_h_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
return v_res_1011_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_box(0);
v___x_1013_ = l_Lean_mkSort(v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0);
v___x_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(lean_object* v_00_u03c3s_1023_, lean_object* v_hyp_1024_, lean_object* v_name_1025_, lean_object* v_k_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref(v___x_1032_);
v___x_1034_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1);
v___x_1035_ = 0;
v___x_1036_ = lean_box(0);
lean_inc_ref(v___y_1027_);
v___x_1037_ = l_Lean_Meta_mkFreshExprMVar(v___x_1034_, v___x_1035_, v___x_1036_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref(v___x_1037_);
v___x_1039_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0));
v___x_1040_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_1041_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1));
v___x_1042_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_1043_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3));
v___x_1044_ = lean_box(0);
lean_inc(v_a_1033_);
v___x_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1045_, 0, v_a_1033_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
lean_inc_ref(v___x_1045_);
v___x_1046_ = l_Lean_mkConst(v___x_1043_, v___x_1045_);
lean_inc(v_a_1038_);
lean_inc_ref(v_hyp_1024_);
lean_inc_ref(v_00_u03c3s_1023_);
v___x_1047_ = l_Lean_mkApp3(v___x_1046_, v_00_u03c3s_1023_, v_hyp_1024_, v_a_1038_);
v___x_1048_ = lean_box(0);
lean_inc(v___y_1030_);
lean_inc_ref(v___y_1029_);
lean_inc(v___y_1028_);
lean_inc_ref(v___y_1027_);
v___x_1049_ = l_Lean_Meta_synthInstance(v___x_1047_, v___x_1048_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1051_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref(v___x_1049_);
lean_inc(v___y_1030_);
lean_inc_ref(v___y_1029_);
v___x_1051_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_name_1025_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v_fst_1053_; lean_object* v_snd_1054_; lean_object* v___f_1055_; lean_object* v___x_1056_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref(v___x_1051_);
v_fst_1053_ = lean_ctor_get(v_a_1052_, 0);
lean_inc(v_fst_1053_);
v_snd_1054_ = lean_ctor_get(v_a_1052_, 1);
lean_inc(v_snd_1054_);
lean_dec(v_a_1052_);
lean_inc(v_a_1038_);
v___f_1055_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1055_, 0, v_a_1038_);
lean_closure_set(v___f_1055_, 1, v_snd_1054_);
lean_closure_set(v___f_1055_, 2, v_k_1026_);
lean_closure_set(v___f_1055_, 3, v___x_1039_);
lean_closure_set(v___f_1055_, 4, v___x_1040_);
lean_closure_set(v___f_1055_, 5, v___x_1041_);
lean_closure_set(v___f_1055_, 6, v___x_1042_);
lean_closure_set(v___f_1055_, 7, v___x_1045_);
lean_closure_set(v___f_1055_, 8, v_00_u03c3s_1023_);
lean_closure_set(v___f_1055_, 9, v_hyp_1024_);
lean_closure_set(v___f_1055_, 10, v_a_1050_);
lean_closure_set(v___f_1055_, 11, v_a_1033_);
v___x_1056_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_fst_1053_, v_a_1038_, v___f_1055_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
return v___x_1056_;
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec(v_a_1050_);
lean_dec_ref(v___x_1045_);
lean_dec(v_a_1038_);
lean_dec(v_a_1033_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec_ref(v_k_1026_);
lean_dec_ref(v_hyp_1024_);
lean_dec_ref(v_00_u03c3s_1023_);
v_a_1057_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1051_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1051_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec_ref(v___x_1045_);
lean_dec(v_a_1038_);
lean_dec(v_a_1033_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec_ref(v_k_1026_);
lean_dec(v_name_1025_);
lean_dec_ref(v_hyp_1024_);
lean_dec_ref(v_00_u03c3s_1023_);
v_a_1065_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1049_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1049_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec(v_a_1033_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec_ref(v_k_1026_);
lean_dec(v_name_1025_);
lean_dec_ref(v_hyp_1024_);
lean_dec_ref(v_00_u03c3s_1023_);
v_a_1073_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1037_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1037_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec_ref(v_k_1026_);
lean_dec(v_name_1025_);
lean_dec_ref(v_hyp_1024_);
lean_dec_ref(v_00_u03c3s_1023_);
v_a_1081_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1032_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1032_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___boxed(lean_object* v_00_u03c3s_1089_, lean_object* v_hyp_1090_, lean_object* v_name_1091_, lean_object* v_k_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1089_, v_hyp_1090_, v_name_1091_, v_k_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(lean_object* v_u_1107_, lean_object* v_00_u03c3s_1108_, lean_object* v_k_1109_, lean_object* v_x_1110_, lean_object* v___h_u03c6_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_H_x27_1117_; lean_object* v___x_1118_; 
lean_inc_ref(v_00_u03c3s_1108_);
lean_inc(v_u_1107_);
v_H_x27_1117_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_1107_, v_00_u03c3s_1108_);
lean_inc(v___y_1115_);
lean_inc_ref(v___y_1114_);
lean_inc(v___y_1113_);
lean_inc_ref(v___y_1112_);
v___x_1118_ = lean_apply_6(v_k_1109_, v_H_x27_1117_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, lean_box(0));
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v_snd_1120_; lean_object* v_fst_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1178_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref(v___x_1118_);
v_snd_1120_ = lean_ctor_get(v_a_1119_, 1);
v_fst_1121_ = lean_ctor_get(v_a_1119_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_a_1119_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1123_ = v_a_1119_;
v_isShared_1124_ = v_isSharedCheck_1178_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_snd_1120_);
lean_inc(v_fst_1121_);
lean_dec(v_a_1119_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1178_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v_fst_1125_; lean_object* v_snd_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1177_; 
v_fst_1125_ = lean_ctor_get(v_snd_1120_, 0);
v_snd_1126_ = lean_ctor_get(v_snd_1120_, 1);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_snd_1120_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1128_ = v_snd_1120_;
v_isShared_1129_ = v_isSharedCheck_1177_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_snd_1126_);
lean_inc(v_fst_1125_);
lean_dec(v_snd_1120_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1177_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; 
lean_inc(v_fst_1125_);
v___x_1130_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_1125_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1168_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1168_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1168_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v_fst_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1166_; 
v_fst_1135_ = lean_ctor_get(v_a_1131_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_a_1131_);
if (v_isSharedCheck_1166_ == 0)
{
lean_object* v_unused_1167_; 
v_unused_1167_ = lean_ctor_get(v_a_1131_, 1);
lean_dec(v_unused_1167_);
v___x_1137_ = v_a_1131_;
v_isShared_1138_ = v_isSharedCheck_1166_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_fst_1135_);
lean_dec(v_a_1131_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1166_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v_u_1139_; lean_object* v_00_u03c3s_1140_; lean_object* v_target_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1164_; 
v_u_1139_ = lean_ctor_get(v_fst_1125_, 0);
v_00_u03c3s_1140_ = lean_ctor_get(v_fst_1125_, 1);
v_target_1141_ = lean_ctor_get(v_fst_1125_, 3);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_fst_1125_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; 
v_unused_1165_ = lean_ctor_get(v_fst_1125_, 2);
lean_dec(v_unused_1165_);
v___x_1143_ = v_fst_1125_;
v_isShared_1144_ = v_isSharedCheck_1164_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_target_1141_);
lean_inc(v_00_u03c3s_1140_);
lean_inc(v_u_1139_);
lean_dec(v_fst_1125_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1164_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1145_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1));
v___x_1146_ = lean_box(0);
if (v_isShared_1124_ == 0)
{
lean_ctor_set_tag(v___x_1123_, 1);
lean_ctor_set(v___x_1123_, 1, v___x_1146_);
lean_ctor_set(v___x_1123_, 0, v_u_1107_);
v___x_1148_ = v___x_1123_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_u_1107_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1149_ = l_Lean_mkConst(v___x_1145_, v___x_1148_);
lean_inc_ref(v_target_1141_);
lean_inc(v_fst_1135_);
v___x_1150_ = l_Lean_mkApp4(v___x_1149_, v_00_u03c3s_1108_, v_fst_1135_, v_target_1141_, v_snd_1126_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 2, v_fst_1135_);
v___x_1152_ = v___x_1143_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_u_1139_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_00_u03c3s_1140_);
lean_ctor_set(v_reuseFailAlloc_1162_, 2, v_fst_1135_);
lean_ctor_set(v_reuseFailAlloc_1162_, 3, v_target_1141_);
v___x_1152_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1154_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 1, v___x_1150_);
lean_ctor_set(v___x_1137_, 0, v___x_1152_);
v___x_1154_ = v___x_1137_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1150_);
v___x_1154_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1156_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 1, v___x_1154_);
lean_ctor_set(v___x_1128_, 0, v_fst_1121_);
v___x_1156_ = v___x_1128_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_fst_1121_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1158_; 
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1156_);
v___x_1158_ = v___x_1133_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
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
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_del_object(v___x_1128_);
lean_dec(v_snd_1126_);
lean_dec(v_fst_1125_);
lean_del_object(v___x_1123_);
lean_dec(v_fst_1121_);
lean_dec_ref(v_00_u03c3s_1108_);
lean_dec(v_u_1107_);
v_a_1169_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1130_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1130_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
}
else
{
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec_ref(v_00_u03c3s_1108_);
lean_dec(v_u_1107_);
return v___x_1118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___boxed(lean_object* v_u_1179_, lean_object* v_00_u03c3s_1180_, lean_object* v_k_1181_, lean_object* v_x_1182_, lean_object* v___h_u03c6_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(v_u_1179_, v_00_u03c3s_1180_, v_k_1181_, v_x_1182_, v___h_u03c6_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec_ref(v___h_u03c6_1183_);
lean_dec_ref(v_x_1182_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(lean_object* v_u_1206_, lean_object* v_00_u03c3s_1207_, lean_object* v_k_1208_, lean_object* v_tail_1209_, lean_object* v_fst_1210_, lean_object* v_H_u2081_x27_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___f_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_inc_ref(v_H_u2081_x27_1211_);
lean_inc_ref(v_00_u03c3s_1207_);
lean_inc(v_u_1206_);
v___f_1217_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1217_, 0, v_u_1206_);
lean_closure_set(v___f_1217_, 1, v_00_u03c3s_1207_);
lean_closure_set(v___f_1217_, 2, v_H_u2081_x27_1211_);
lean_closure_set(v___f_1217_, 3, v_k_1208_);
v___x_1218_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1218_, 0, v_tail_1209_);
lean_inc_ref(v_fst_1210_);
lean_inc_ref(v_00_u03c3s_1207_);
lean_inc(v_u_1206_);
v___x_1219_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1206_, v_00_u03c3s_1207_, v_fst_1210_, v___x_1218_, v___f_1217_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1265_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1222_ = v___x_1219_;
v_isShared_1223_ = v_isSharedCheck_1265_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1265_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v_fst_1224_; lean_object* v_snd_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1264_; 
v_fst_1224_ = lean_ctor_get(v_a_1220_, 0);
v_snd_1225_ = lean_ctor_get(v_a_1220_, 1);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_a_1220_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1227_ = v_a_1220_;
v_isShared_1228_ = v_isSharedCheck_1264_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_snd_1225_);
lean_inc(v_fst_1224_);
lean_dec(v_a_1220_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1264_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v_fst_1229_; lean_object* v_snd_1230_; lean_object* v_snd_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1262_; 
v_fst_1229_ = lean_ctor_get(v_snd_1225_, 0);
lean_inc(v_fst_1229_);
v_snd_1230_ = lean_ctor_get(v_fst_1224_, 1);
v_snd_1231_ = lean_ctor_get(v_snd_1225_, 1);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_snd_1225_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v_snd_1225_, 0);
lean_dec(v_unused_1263_);
v___x_1233_ = v_snd_1225_;
v_isShared_1234_ = v_isSharedCheck_1262_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_snd_1231_);
lean_dec(v_snd_1225_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1262_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v_u_1235_; lean_object* v_00_u03c3s_1236_; lean_object* v_target_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1260_; 
v_u_1235_ = lean_ctor_get(v_fst_1229_, 0);
v_00_u03c3s_1236_ = lean_ctor_get(v_fst_1229_, 1);
v_target_1237_ = lean_ctor_get(v_fst_1229_, 3);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_fst_1229_);
if (v_isSharedCheck_1260_ == 0)
{
lean_object* v_unused_1261_; 
v_unused_1261_ = lean_ctor_get(v_fst_1229_, 2);
lean_dec(v_unused_1261_);
v___x_1239_ = v_fst_1229_;
v_isShared_1240_ = v_isSharedCheck_1260_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_target_1237_);
lean_inc(v_00_u03c3s_1236_);
lean_inc(v_u_1235_);
lean_dec(v_fst_1229_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1260_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1241_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1));
v___x_1242_ = lean_box(0);
lean_inc(v_u_1206_);
v___x_1243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1243_, 0, v_u_1206_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = l_Lean_mkConst(v___x_1241_, v___x_1243_);
lean_inc_ref(v_target_1237_);
lean_inc_ref(v_fst_1210_);
lean_inc_ref(v_H_u2081_x27_1211_);
lean_inc(v_snd_1230_);
lean_inc_ref(v_00_u03c3s_1207_);
v___x_1245_ = l_Lean_mkApp6(v___x_1244_, v_00_u03c3s_1207_, v_snd_1230_, v_H_u2081_x27_1211_, v_fst_1210_, v_target_1237_, v_snd_1231_);
lean_inc(v_snd_1230_);
lean_inc_ref(v_00_u03c3s_1207_);
lean_inc(v_u_1206_);
v___x_1246_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1206_, v_00_u03c3s_1207_, v_snd_1230_, v_fst_1210_);
v___x_1247_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1206_, v_00_u03c3s_1207_, v___x_1246_, v_H_u2081_x27_1211_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 2, v___x_1247_);
v___x_1249_ = v___x_1239_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_u_1235_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_00_u03c3s_1236_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1259_, 3, v_target_1237_);
v___x_1249_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1251_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v___x_1245_);
lean_ctor_set(v___x_1233_, 0, v___x_1249_);
v___x_1251_ = v___x_1233_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___x_1245_);
v___x_1251_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1253_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 1, v___x_1251_);
v___x_1253_ = v___x_1227_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_fst_1224_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1255_; 
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 0, v___x_1253_);
v___x_1255_ = v___x_1222_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
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
lean_dec_ref(v_H_u2081_x27_1211_);
lean_dec_ref(v_fst_1210_);
lean_dec_ref(v_00_u03c3s_1207_);
lean_dec(v_u_1206_);
return v___x_1219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___boxed(lean_object* v_u_1266_, lean_object* v_00_u03c3s_1267_, lean_object* v_k_1268_, lean_object* v_tail_1269_, lean_object* v_fst_1270_, lean_object* v_H_u2081_x27_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(v_u_1266_, v_00_u03c3s_1267_, v_k_1268_, v_tail_1269_, v_fst_1270_, v_H_u2081_x27_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
return v_res_1277_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4));
v___x_1288_ = l_Lean_stringToMessageData(v___x_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2___boxed(lean_object* v___x_1289_, lean_object* v_tail_1290_, lean_object* v_u_1291_, lean_object* v___x_1292_, lean_object* v_k_1293_, lean_object* v_x_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2(v___x_1289_, v_tail_1290_, v_u_1291_, v___x_1292_, v_k_1293_, v_x_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
return v_res_1300_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6));
v___x_1303_ = l_Lean_stringToMessageData(v___x_1302_);
return v___x_1303_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10));
v___x_1312_ = l_Lean_stringToMessageData(v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(lean_object* v_u_1319_, lean_object* v_00_u03c3s_1320_, lean_object* v_H_1321_, lean_object* v_pat_1322_, lean_object* v_k_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
switch(lean_obj_tag(v_pat_1322_))
{
case 0:
{
lean_object* v_name_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1376_; 
v_name_1329_ = lean_ctor_get(v_pat_1322_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_pat_1322_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1331_ = v_pat_1322_;
v_isShared_1332_ = v_isSharedCheck_1376_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_name_1329_);
lean_dec(v_pat_1322_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1376_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___y_1334_; uint8_t v___y_1335_; lean_object* v___y_1341_; lean_object* v_a_1342_; lean_object* v___x_1345_; uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1345_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1);
v___x_1346_ = 0;
v___x_1347_ = lean_box(0);
lean_inc_ref(v_a_1324_);
v___x_1348_ = l_Lean_Meta_mkFreshExprMVar(v___x_1345_, v___x_1346_, v___x_1347_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref(v___x_1348_);
v___x_1350_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3));
v___x_1351_ = lean_box(0);
lean_inc(v_u_1319_);
v___x_1352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_u_1319_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = l_Lean_mkConst(v___x_1350_, v___x_1352_);
lean_inc_ref(v_H_1321_);
lean_inc_ref(v_00_u03c3s_1320_);
v___x_1354_ = l_Lean_mkApp3(v___x_1353_, v_00_u03c3s_1320_, v_H_1321_, v_a_1349_);
v___x_1355_ = lean_box(0);
lean_inc(v_a_1327_);
lean_inc_ref(v_a_1326_);
lean_inc(v_a_1325_);
lean_inc_ref(v_a_1324_);
v___x_1356_ = l_Lean_Meta_synthInstance(v___x_1354_, v___x_1355_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec_ref(v___x_1356_);
lean_inc(v_name_1329_);
v___x_1357_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1357_, 0, v_name_1329_);
lean_inc(v_a_1327_);
lean_inc_ref(v_a_1326_);
lean_inc(v_a_1325_);
lean_inc_ref(v_a_1324_);
lean_inc_ref(v_k_1323_);
lean_inc_ref(v_H_1321_);
lean_inc_ref(v_00_u03c3s_1320_);
lean_inc(v_u_1319_);
v___x_1358_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1319_, v_00_u03c3s_1320_, v_H_1321_, v___x_1357_, v_k_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_del_object(v___x_1331_);
lean_dec(v_name_1329_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_H_1321_);
lean_dec_ref(v_00_u03c3s_1320_);
lean_dec(v_u_1319_);
return v___x_1358_;
}
else
{
lean_object* v_a_1359_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1359_);
v___y_1341_ = v___x_1358_;
v_a_1342_ = v_a_1359_;
goto v___jp_1340_;
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_a_1360_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1356_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1356_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
lean_inc(v_a_1360_);
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
v___y_1341_ = v___x_1365_;
v_a_1342_ = v_a_1360_;
goto v___jp_1340_;
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
v_a_1368_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1348_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1348_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
lean_inc(v_a_1368_);
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
v___y_1341_ = v___x_1373_;
v_a_1342_ = v_a_1368_;
goto v___jp_1340_;
}
}
}
v___jp_1333_:
{
if (v___y_1335_ == 0)
{
lean_object* v___x_1337_; 
lean_dec_ref(v___y_1334_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set_tag(v___x_1331_, 5);
v___x_1337_ = v___x_1331_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_name_1329_);
v___x_1337_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
v_pat_1322_ = v___x_1337_;
goto _start;
}
}
else
{
lean_del_object(v___x_1331_);
lean_dec(v_name_1329_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_H_1321_);
lean_dec_ref(v_00_u03c3s_1320_);
lean_dec(v_u_1319_);
return v___y_1334_;
}
}
v___jp_1340_:
{
uint8_t v___x_1343_; 
v___x_1343_ = l_Lean_Exception_isInterrupt(v_a_1342_);
if (v___x_1343_ == 0)
{
uint8_t v___x_1344_; 
v___x_1344_ = l_Lean_Exception_isRuntime(v_a_1342_);
v___y_1334_ = v___y_1341_;
v___y_1335_ = v___x_1344_;
goto v___jp_1333_;
}
else
{
lean_dec_ref(v_a_1342_);
v___y_1334_ = v___y_1341_;
v___y_1335_ = v___x_1343_;
goto v___jp_1333_;
}
}
}
}
case 1:
{
lean_object* v_H_x27_1377_; lean_object* v___x_1378_; 
lean_inc_ref(v_00_u03c3s_1320_);
lean_inc(v_u_1319_);
v_H_x27_1377_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_1319_, v_00_u03c3s_1320_);
lean_inc(v_a_1327_);
lean_inc_ref(v_a_1326_);
lean_inc(v_a_1325_);
lean_inc_ref(v_a_1324_);
v___x_1378_ = lean_apply_6(v_k_1323_, v_H_x27_1377_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, lean_box(0));
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v_snd_1380_; lean_object* v_fst_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1439_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref(v___x_1378_);
v_snd_1380_ = lean_ctor_get(v_a_1379_, 1);
v_fst_1381_ = lean_ctor_get(v_a_1379_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_a_1379_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1383_ = v_a_1379_;
v_isShared_1384_ = v_isSharedCheck_1439_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_snd_1380_);
lean_inc(v_fst_1381_);
lean_dec(v_a_1379_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1439_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v_fst_1385_; lean_object* v_snd_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1438_; 
v_fst_1385_ = lean_ctor_get(v_snd_1380_, 0);
v_snd_1386_ = lean_ctor_get(v_snd_1380_, 1);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_snd_1380_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1388_ = v_snd_1380_;
v_isShared_1389_ = v_isSharedCheck_1438_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_snd_1386_);
lean_inc(v_fst_1385_);
lean_dec(v_snd_1380_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1438_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; 
lean_inc(v_fst_1385_);
v___x_1390_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_1385_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1429_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1429_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1429_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v_fst_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1427_; 
v_fst_1395_ = lean_ctor_get(v_a_1391_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_a_1391_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; 
v_unused_1428_ = lean_ctor_get(v_a_1391_, 1);
lean_dec(v_unused_1428_);
v___x_1397_ = v_a_1391_;
v_isShared_1398_ = v_isSharedCheck_1427_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_fst_1395_);
lean_dec(v_a_1391_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1427_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v_u_1399_; lean_object* v_00_u03c3s_1400_; lean_object* v_target_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1425_; 
v_u_1399_ = lean_ctor_get(v_fst_1385_, 0);
v_00_u03c3s_1400_ = lean_ctor_get(v_fst_1385_, 1);
v_target_1401_ = lean_ctor_get(v_fst_1385_, 3);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_fst_1385_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; 
v_unused_1426_ = lean_ctor_get(v_fst_1385_, 2);
lean_dec(v_unused_1426_);
v___x_1403_ = v_fst_1385_;
v_isShared_1404_ = v_isSharedCheck_1425_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_target_1401_);
lean_inc(v_00_u03c3s_1400_);
lean_inc(v_u_1399_);
lean_dec(v_fst_1385_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1425_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1405_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1));
v___x_1406_ = lean_box(0);
lean_inc(v_u_1319_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set_tag(v___x_1383_, 1);
lean_ctor_set(v___x_1383_, 1, v___x_1406_);
lean_ctor_set(v___x_1383_, 0, v_u_1319_);
v___x_1408_ = v___x_1383_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_u_1319_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1409_ = l_Lean_mkConst(v___x_1405_, v___x_1408_);
lean_inc_ref(v_target_1401_);
lean_inc_ref(v_H_1321_);
lean_inc(v_fst_1395_);
lean_inc_ref(v_00_u03c3s_1320_);
v___x_1410_ = l_Lean_mkApp5(v___x_1409_, v_00_u03c3s_1320_, v_fst_1395_, v_H_1321_, v_target_1401_, v_snd_1386_);
v___x_1411_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1319_, v_00_u03c3s_1320_, v_fst_1395_, v_H_1321_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 2, v___x_1411_);
v___x_1413_ = v___x_1403_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_u_1399_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_00_u03c3s_1400_);
lean_ctor_set(v_reuseFailAlloc_1423_, 2, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1423_, 3, v_target_1401_);
v___x_1413_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1415_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 1, v___x_1410_);
lean_ctor_set(v___x_1397_, 0, v___x_1413_);
v___x_1415_ = v___x_1397_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v___x_1410_);
v___x_1415_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1417_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 1, v___x_1415_);
lean_ctor_set(v___x_1388_, 0, v_fst_1381_);
v___x_1417_ = v___x_1388_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_fst_1381_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1419_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1417_);
v___x_1419_ = v___x_1393_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
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
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_del_object(v___x_1388_);
lean_dec(v_snd_1386_);
lean_dec(v_fst_1385_);
lean_del_object(v___x_1383_);
lean_dec(v_fst_1381_);
lean_dec_ref(v_H_1321_);
lean_dec_ref(v_00_u03c3s_1320_);
lean_dec(v_u_1319_);
v_a_1430_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1390_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1390_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec_ref(v_H_1321_);
lean_dec_ref(v_00_u03c3s_1320_);
lean_dec(v_u_1319_);
return v___x_1378_;
}
}
case 2:
{
lean_object* v_args_1440_; 
v_args_1440_ = lean_ctor_get(v_pat_1322_, 0);
lean_inc(v_args_1440_);
lean_dec_ref(v_pat_1322_);
if (lean_obj_tag(v_args_1440_) == 0)
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_box(1);
v_pat_1322_ = v___x_1441_;
goto _start;
}
else
{
lean_object* v_tail_1443_; 
v_tail_1443_ = lean_ctor_get(v_args_1440_, 1);
if (lean_obj_tag(v_tail_1443_) == 0)
{
lean_object* v_head_1444_; 
v_head_1444_ = lean_ctor_get(v_args_1440_, 0);
lean_inc(v_head_1444_);
lean_dec_ref(v_args_1440_);
v_pat_1322_ = v_head_1444_;
goto _start;
}
else
{
lean_object* v_head_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1539_; 
lean_inc(v_tail_1443_);
v_head_1446_ = lean_ctor_get(v_args_1440_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_args_1440_);
if (v_isSharedCheck_1539_ == 0)
{
lean_object* v_unused_1540_; 
v_unused_1540_ = lean_ctor_get(v_args_1440_, 1);
lean_dec(v_unused_1540_);
v___x_1448_ = v_args_1440_;
v_isShared_1449_ = v_isSharedCheck_1539_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_head_1446_);
lean_dec(v_args_1440_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1539_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1450_; 
lean_inc(v_a_1327_);
lean_inc_ref(v_a_1326_);
lean_inc(v_a_1325_);
lean_inc_ref(v_a_1324_);
lean_inc_ref(v_H_1321_);
lean_inc_ref(v_00_u03c3s_1320_);
lean_inc(v_u_1319_);
v___x_1450_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(v_u_1319_, v_00_u03c3s_1320_, v_H_1321_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref(v___x_1450_);
if (lean_obj_tag(v_a_1451_) == 1)
{
lean_object* v_val_1452_; lean_object* v_snd_1453_; lean_object* v_fst_1454_; lean_object* v_fst_1455_; lean_object* v_snd_1456_; lean_object* v___f_1457_; lean_object* v___x_1458_; 
v_val_1452_ = lean_ctor_get(v_a_1451_, 0);
lean_inc(v_val_1452_);
lean_dec_ref(v_a_1451_);
v_snd_1453_ = lean_ctor_get(v_val_1452_, 1);
lean_inc(v_snd_1453_);
v_fst_1454_ = lean_ctor_get(v_val_1452_, 0);
lean_inc(v_fst_1454_);
lean_dec(v_val_1452_);
v_fst_1455_ = lean_ctor_get(v_snd_1453_, 0);
lean_inc(v_fst_1455_);
v_snd_1456_ = lean_ctor_get(v_snd_1453_, 1);
lean_inc(v_snd_1456_);
lean_dec(v_snd_1453_);
lean_inc(v_fst_1455_);
lean_inc_ref(v_00_u03c3s_1320_);
lean_inc(v_u_1319_);
v___f_1457_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___boxed), 11, 5);
lean_closure_set(v___f_1457_, 0, v_u_1319_);
lean_closure_set(v___f_1457_, 1, v_00_u03c3s_1320_);
lean_closure_set(v___f_1457_, 2, v_k_1323_);
lean_closure_set(v___f_1457_, 3, v_tail_1443_);
lean_closure_set(v___f_1457_, 4, v_fst_1455_);
lean_inc(v_fst_1454_);
lean_inc_ref(v_00_u03c3s_1320_);
lean_inc(v_u_1319_);
v___x_1458_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1319_, v_00_u03c3s_1320_, v_fst_1454_, v_head_1446_, v___f_1457_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1506_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1506_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1506_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v_fst_1463_; lean_object* v_snd_1464_; lean_object* v_fst_1465_; lean_object* v_fst_1466_; lean_object* v_snd_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1505_; 
v_fst_1463_ = lean_ctor_get(v_a_1459_, 0);
lean_inc(v_fst_1463_);
v_snd_1464_ = lean_ctor_get(v_a_1459_, 1);
lean_inc(v_snd_1464_);
lean_dec(v_a_1459_);
v_fst_1465_ = lean_ctor_get(v_snd_1464_, 0);
lean_inc(v_fst_1465_);
v_fst_1466_ = lean_ctor_get(v_fst_1463_, 0);
v_snd_1467_ = lean_ctor_get(v_fst_1463_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_fst_1463_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1469_ = v_fst_1463_;
v_isShared_1470_ = v_isSharedCheck_1505_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_snd_1467_);
lean_inc(v_fst_1466_);
lean_dec(v_fst_1463_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1505_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v_snd_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1503_; 
v_snd_1471_ = lean_ctor_get(v_snd_1464_, 1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_snd_1464_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; 
v_unused_1504_ = lean_ctor_get(v_snd_1464_, 0);
lean_dec(v_unused_1504_);
v___x_1473_ = v_snd_1464_;
v_isShared_1474_ = v_isSharedCheck_1503_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_snd_1471_);
lean_dec(v_snd_1464_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1503_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v_u_1475_; lean_object* v_00_u03c3s_1476_; lean_object* v_target_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1501_; 
v_u_1475_ = lean_ctor_get(v_fst_1465_, 0);
v_00_u03c3s_1476_ = lean_ctor_get(v_fst_1465_, 1);
v_target_1477_ = lean_ctor_get(v_fst_1465_, 3);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_fst_1465_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; 
v_unused_1502_ = lean_ctor_get(v_fst_1465_, 2);
lean_dec(v_unused_1502_);
v___x_1479_ = v_fst_1465_;
v_isShared_1480_ = v_isSharedCheck_1501_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_target_1477_);
lean_inc(v_00_u03c3s_1476_);
lean_inc(v_u_1475_);
lean_dec(v_fst_1465_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1501_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1481_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3));
v___x_1482_ = lean_box(0);
lean_inc(v_u_1319_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 1, v___x_1482_);
lean_ctor_set(v___x_1448_, 0, v_u_1319_);
v___x_1484_ = v___x_1448_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_u_1319_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1485_ = l_Lean_mkConst(v___x_1481_, v___x_1484_);
lean_inc_ref(v_target_1477_);
lean_inc_ref(v_H_1321_);
lean_inc(v_snd_1467_);
lean_inc_ref(v_00_u03c3s_1320_);
v___x_1486_ = l_Lean_mkApp8(v___x_1485_, v_00_u03c3s_1320_, v_snd_1467_, v_fst_1454_, v_fst_1455_, v_H_1321_, v_target_1477_, v_snd_1456_, v_snd_1471_);
v___x_1487_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1319_, v_00_u03c3s_1320_, v_snd_1467_, v_H_1321_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 2, v___x_1487_);
v___x_1489_ = v___x_1479_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_u_1475_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_00_u03c3s_1476_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1499_, 3, v_target_1477_);
v___x_1489_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1491_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 1, v___x_1486_);
lean_ctor_set(v___x_1473_, 0, v___x_1489_);
v___x_1491_ = v___x_1473_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v___x_1486_);
v___x_1491_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1493_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 1, v___x_1491_);
v___x_1493_ = v___x_1469_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_fst_1466_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1495_; 
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1493_);
v___x_1495_ = v___x_1461_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
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
else
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
lean_dec(v_snd_1456_);
lean_dec(v_fst_1455_);
lean_dec(v_fst_1454_);
lean_del_object(v___x_1448_);
lean_dec_ref(v_H_1321_);
lean_dec_ref(v_00_u03c3s_1320_);
lean_dec(v_u_1319_);
v_a_1507_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1458_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1458_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
else
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
lean_dec(v_a_1451_);
lean_del_object(v___x_1448_);
lean_dec_ref(v_00_u03c3s_1320_);
v___x_1515_ = l_Lean_Expr_consumeMData(v_H_1321_);
v___x_1516_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1));
v___x_1517_ = lean_unsigned_to_nat(3u);
v___x_1518_ = l_Lean_Expr_isAppOfArity(v___x_1515_, v___x_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_dec_ref(v___x_1515_);
lean_dec(v_head_1446_);
lean_dec(v_tail_1443_);
lean_dec_ref(v_k_1323_);
lean_dec(v_u_1319_);
v___x_1519_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5);
v___x_1520_ = l_Lean_MessageData_ofExpr(v_H_1321_);
v___x_1521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1519_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_1521_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
return v___x_1522_;
}
else
{
if (lean_obj_tag(v_head_1446_) == 0)
{
lean_object* v_name_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___f_1527_; lean_object* v___x_1528_; 
v_name_1523_ = lean_ctor_get(v_head_1446_, 0);
lean_inc(v_name_1523_);
lean_dec_ref(v_head_1446_);
v___x_1524_ = l_Lean_Expr_appFn_x21(v___x_1515_);
v___x_1525_ = l_Lean_Expr_appArg_x21(v___x_1524_);
lean_dec_ref(v___x_1524_);
v___x_1526_ = l_Lean_Expr_appArg_x21(v___x_1515_);
lean_dec_ref(v___x_1515_);
v___f_1527_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2___boxed), 11, 5);
lean_closure_set(v___f_1527_, 0, v___x_1526_);
lean_closure_set(v___f_1527_, 1, v_tail_1443_);
lean_closure_set(v___f_1527_, 2, v_u_1319_);
lean_closure_set(v___f_1527_, 3, v___x_1525_);
lean_closure_set(v___f_1527_, 4, v_k_1323_);
v___x_1528_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(v_H_1321_, v_name_1523_, v___f_1527_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1528_;
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec_ref(v___x_1515_);
lean_dec(v_head_1446_);
lean_dec(v_tail_1443_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_H_1321_);
lean_dec(v_u_1319_);
v___x_1529_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7);
v___x_1530_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_1529_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
return v___x_1530_;
}
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_del_object(v___x_1448_);
lean_dec(v_head_1446_);
lean_dec(v_tail_1443_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_H_1321_);
lean_dec_ref(v_00_u03c3s_1320_);
lean_dec(v_u_1319_);
v_a_1531_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1450_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1450_);
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
}
}
case 3:
{
lean_object* v_args_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1636_; 
v_args_1541_ = lean_ctor_get(v_pat_1322_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v_pat_1322_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1543_ = v_pat_1322_;
v_isShared_1544_ = v_isSharedCheck_1636_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_args_1541_);
lean_dec(v_pat_1322_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1636_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
if (lean_obj_tag(v_args_1541_) == 0)
{
lean_object* v___x_1545_; 
lean_del_object(v___x_1543_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_H_1321_);
lean_dec_ref(v_00_u03c3s_1320_);
lean_dec(v_u_1319_);
v___x_1545_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
return v___x_1545_;
}
else
{
lean_object* v_tail_1546_; 
v_tail_1546_ = lean_ctor_get(v_args_1541_, 1);
if (lean_obj_tag(v_tail_1546_) == 0)
{
lean_object* v_head_1547_; 
lean_del_object(v___x_1543_);
v_head_1547_ = lean_ctor_get(v_args_1541_, 0);
lean_inc(v_head_1547_);
lean_dec_ref(v_args_1541_);
v_pat_1322_ = v_head_1547_;
goto _start;
}
else
{
lean_object* v_head_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1634_; 
lean_inc(v_tail_1546_);
lean_dec_ref(v_00_u03c3s_1320_);
v_head_1549_ = lean_ctor_get(v_args_1541_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_args_1541_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; 
v_unused_1635_ = lean_ctor_get(v_args_1541_, 1);
lean_dec(v_unused_1635_);
v___x_1551_ = v_args_1541_;
v_isShared_1552_ = v_isSharedCheck_1634_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_head_1549_);
lean_dec(v_args_1541_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1634_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1553_ = l_Lean_Expr_consumeMData(v_H_1321_);
v___x_1554_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9));
v___x_1555_ = lean_unsigned_to_nat(3u);
v___x_1556_ = l_Lean_Expr_isAppOfArity(v___x_1553_, v___x_1554_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
lean_dec_ref(v___x_1553_);
lean_del_object(v___x_1551_);
lean_dec(v_head_1549_);
lean_dec(v_tail_1546_);
lean_del_object(v___x_1543_);
lean_dec_ref(v_k_1323_);
lean_dec(v_u_1319_);
v___x_1557_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11);
v___x_1558_ = l_Lean_MessageData_ofExpr(v_H_1321_);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_1559_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
return v___x_1560_;
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_dec_ref(v_H_1321_);
v___x_1561_ = l_Lean_Expr_appFn_x21(v___x_1553_);
v___x_1562_ = l_Lean_Expr_appFn_x21(v___x_1561_);
v___x_1563_ = l_Lean_Expr_appArg_x21(v___x_1562_);
lean_dec_ref(v___x_1562_);
v___x_1564_ = l_Lean_Expr_appArg_x21(v___x_1561_);
lean_dec_ref(v___x_1561_);
lean_inc(v_a_1327_);
lean_inc_ref(v_a_1326_);
lean_inc(v_a_1325_);
lean_inc_ref(v_a_1324_);
lean_inc_ref(v_k_1323_);
lean_inc_ref(v___x_1564_);
lean_inc_ref(v___x_1563_);
lean_inc(v_u_1319_);
v___x_1565_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1319_, v___x_1563_, v___x_1564_, v_head_1549_, v_k_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v_snd_1567_; lean_object* v_fst_1568_; lean_object* v_snd_1569_; lean_object* v___x_1570_; lean_object* v___x_1572_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref(v___x_1565_);
v_snd_1567_ = lean_ctor_get(v_a_1566_, 1);
lean_inc(v_snd_1567_);
lean_dec(v_a_1566_);
v_fst_1568_ = lean_ctor_get(v_snd_1567_, 0);
lean_inc(v_fst_1568_);
v_snd_1569_ = lean_ctor_get(v_snd_1567_, 1);
lean_inc(v_snd_1569_);
lean_dec(v_snd_1567_);
v___x_1570_ = l_Lean_Expr_appArg_x21(v___x_1553_);
lean_dec_ref(v___x_1553_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v_tail_1546_);
v___x_1572_ = v___x_1543_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_tail_1546_);
v___x_1572_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1573_; 
lean_inc(v_a_1327_);
lean_inc_ref(v_a_1326_);
lean_inc(v_a_1325_);
lean_inc_ref(v_a_1324_);
lean_inc_ref(v___x_1570_);
lean_inc_ref(v___x_1563_);
lean_inc(v_u_1319_);
v___x_1573_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1319_, v___x_1563_, v___x_1570_, v___x_1572_, v_k_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v_snd_1575_; lean_object* v_fst_1576_; lean_object* v_snd_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1631_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref(v___x_1573_);
v_snd_1575_ = lean_ctor_get(v_a_1574_, 1);
lean_inc(v_snd_1575_);
v_fst_1576_ = lean_ctor_get(v_a_1574_, 0);
lean_inc(v_fst_1576_);
lean_dec(v_a_1574_);
v_snd_1577_ = lean_ctor_get(v_snd_1575_, 1);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_snd_1575_);
if (v_isSharedCheck_1631_ == 0)
{
lean_object* v_unused_1632_; 
v_unused_1632_ = lean_ctor_get(v_snd_1575_, 0);
lean_dec(v_unused_1632_);
v___x_1579_ = v_snd_1575_;
v_isShared_1580_ = v_isSharedCheck_1631_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_snd_1577_);
lean_dec(v_snd_1575_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1631_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; 
lean_inc(v_fst_1568_);
v___x_1581_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_1568_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1622_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1622_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1622_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v_fst_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1620_; 
v_fst_1586_ = lean_ctor_get(v_a_1582_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_a_1582_);
if (v_isSharedCheck_1620_ == 0)
{
lean_object* v_unused_1621_; 
v_unused_1621_ = lean_ctor_get(v_a_1582_, 1);
lean_dec(v_unused_1621_);
v___x_1588_ = v_a_1582_;
v_isShared_1589_ = v_isSharedCheck_1620_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_fst_1586_);
lean_dec(v_a_1582_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1620_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v_u_1590_; lean_object* v_00_u03c3s_1591_; lean_object* v_target_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1618_; 
v_u_1590_ = lean_ctor_get(v_fst_1568_, 0);
v_00_u03c3s_1591_ = lean_ctor_get(v_fst_1568_, 1);
v_target_1592_ = lean_ctor_get(v_fst_1568_, 3);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_fst_1568_);
if (v_isSharedCheck_1618_ == 0)
{
lean_object* v_unused_1619_; 
v_unused_1619_ = lean_ctor_get(v_fst_1568_, 2);
lean_dec(v_unused_1619_);
v___x_1594_ = v_fst_1568_;
v_isShared_1595_ = v_isSharedCheck_1618_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_target_1592_);
lean_inc(v_00_u03c3s_1591_);
lean_inc(v_u_1590_);
lean_dec(v_fst_1568_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1618_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1596_ = lean_box(0);
lean_inc(v_u_1319_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 1, v___x_1596_);
lean_ctor_set(v___x_1551_, 0, v_u_1319_);
v___x_1598_ = v___x_1551_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_u_1319_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1603_; 
lean_inc_ref(v___x_1598_);
v___x_1599_ = l_Lean_mkConst(v___x_1554_, v___x_1598_);
lean_inc_ref(v___x_1570_);
lean_inc_ref(v___x_1564_);
lean_inc_ref(v___x_1563_);
v___x_1600_ = l_Lean_mkApp3(v___x_1599_, v___x_1563_, v___x_1564_, v___x_1570_);
lean_inc(v_fst_1586_);
lean_inc_ref(v___x_1563_);
v___x_1601_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1319_, v___x_1563_, v_fst_1586_, v___x_1600_);
lean_inc_ref(v_target_1592_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 2, v___x_1601_);
v___x_1603_ = v___x_1594_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_u_1590_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_00_u03c3s_1591_);
lean_ctor_set(v_reuseFailAlloc_1616_, 2, v___x_1601_);
lean_ctor_set(v_reuseFailAlloc_1616_, 3, v_target_1592_);
v___x_1603_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1604_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13));
v___x_1605_ = l_Lean_mkConst(v___x_1604_, v___x_1598_);
v___x_1606_ = l_Lean_mkApp7(v___x_1605_, v___x_1563_, v_fst_1586_, v___x_1564_, v___x_1570_, v_target_1592_, v_snd_1569_, v_snd_1577_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 1, v___x_1606_);
lean_ctor_set(v___x_1588_, 0, v___x_1603_);
v___x_1608_ = v___x_1588_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1610_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 1, v___x_1608_);
lean_ctor_set(v___x_1579_, 0, v_fst_1576_);
v___x_1610_ = v___x_1579_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_fst_1576_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_object* v___x_1612_; 
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1610_);
v___x_1612_ = v___x_1584_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
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
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_del_object(v___x_1579_);
lean_dec(v_snd_1577_);
lean_dec(v_fst_1576_);
lean_dec_ref(v___x_1570_);
lean_dec(v_snd_1569_);
lean_dec(v_fst_1568_);
lean_dec_ref(v___x_1564_);
lean_dec_ref(v___x_1563_);
lean_del_object(v___x_1551_);
lean_dec(v_u_1319_);
v_a_1623_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1581_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1581_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1570_);
lean_dec(v_snd_1569_);
lean_dec(v_fst_1568_);
lean_dec_ref(v___x_1564_);
lean_dec_ref(v___x_1563_);
lean_del_object(v___x_1551_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec(v_u_1319_);
return v___x_1573_;
}
}
}
else
{
lean_dec_ref(v___x_1564_);
lean_dec_ref(v___x_1563_);
lean_dec_ref(v___x_1553_);
lean_del_object(v___x_1551_);
lean_dec(v_tail_1546_);
lean_del_object(v___x_1543_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec_ref(v_k_1323_);
lean_dec(v_u_1319_);
return v___x_1565_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_h_1637_; lean_object* v___f_1638_; lean_object* v___x_1639_; 
v_h_1637_ = lean_ctor_get(v_pat_1322_, 0);
lean_inc(v_h_1637_);
lean_dec_ref(v_pat_1322_);
lean_inc_ref(v_00_u03c3s_1320_);
v___f_1638_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___boxed), 10, 3);
lean_closure_set(v___f_1638_, 0, v_u_1319_);
lean_closure_set(v___f_1638_, 1, v_00_u03c3s_1320_);
lean_closure_set(v___f_1638_, 2, v_k_1323_);
v___x_1639_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1320_, v_H_1321_, v_h_1637_, v___f_1638_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1639_;
}
default: 
{
lean_object* v_h_1640_; lean_object* v___x_1641_; 
lean_dec(v_u_1319_);
v_h_1640_ = lean_ctor_get(v_pat_1322_, 0);
lean_inc(v_h_1640_);
lean_dec_ref(v_pat_1322_);
lean_inc(v_a_1327_);
lean_inc_ref(v_a_1326_);
v___x_1641_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_h_1640_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v_fst_1643_; lean_object* v_snd_1644_; lean_object* v___x_1645_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref(v___x_1641_);
v_fst_1643_ = lean_ctor_get(v_a_1642_, 0);
lean_inc(v_fst_1643_);
v_snd_1644_ = lean_ctor_get(v_a_1642_, 1);
lean_inc(v_snd_1644_);
lean_dec(v_a_1642_);
v___x_1645_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v_a_1327_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref(v___x_1645_);
v___x_1647_ = l_Lean_Expr_consumeMData(v_H_1321_);
lean_dec_ref(v_H_1321_);
v___x_1648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1648_, 0, v_fst_1643_);
lean_ctor_set(v___x_1648_, 1, v_a_1646_);
lean_ctor_set(v___x_1648_, 2, v___x_1647_);
v___x_1649_ = 1;
lean_inc(v_a_1327_);
lean_inc_ref(v_a_1326_);
lean_inc(v_a_1325_);
lean_inc_ref(v_a_1324_);
lean_inc_ref(v___x_1648_);
v___x_1650_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_snd_1644_, v_00_u03c3s_1320_, v___x_1648_, v___x_1649_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_dec_ref(v___x_1650_);
v___x_1651_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1648_);
v___x_1652_ = lean_apply_6(v_k_1323_, v___x_1651_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, lean_box(0));
return v___x_1652_;
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec_ref(v___x_1648_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec_ref(v_k_1323_);
v_a_1653_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1650_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1650_);
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
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v_snd_1644_);
lean_dec(v_fst_1643_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_H_1321_);
lean_dec_ref(v_00_u03c3s_1320_);
v_a_1661_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1645_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1645_);
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
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_H_1321_);
lean_dec_ref(v_00_u03c3s_1320_);
v_a_1669_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1641_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1641_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2(lean_object* v___x_1677_, lean_object* v_tail_1678_, lean_object* v_u_1679_, lean_object* v___x_1680_, lean_object* v_k_1681_, lean_object* v_x_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1688_ = lean_unsigned_to_nat(1u);
v___x_1689_ = lean_mk_empty_array_with_capacity(v___x_1688_);
v___x_1690_ = lean_array_push(v___x_1689_, v_x_1682_);
v___x_1691_ = 0;
v___x_1692_ = l_Lean_Expr_betaRev(v___x_1677_, v___x_1690_, v___x_1691_, v___x_1691_);
lean_dec_ref(v___x_1690_);
v___x_1693_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1693_, 0, v_tail_1678_);
v___x_1694_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1679_, v___x_1680_, v___x_1692_, v___x_1693_, v_k_1681_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___boxed(lean_object* v_u_1695_, lean_object* v_00_u03c3s_1696_, lean_object* v_H_1697_, lean_object* v_pat_1698_, lean_object* v_k_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1695_, v_00_u03c3s_1696_, v_H_1697_, v_pat_1698_, v_k_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore(lean_object* v_00_u03b1_1706_, lean_object* v_u_1707_, lean_object* v_00_u03c3s_1708_, lean_object* v_H_1709_, lean_object* v_pat_1710_, lean_object* v_k_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1707_, v_00_u03c3s_1708_, v_H_1709_, v_pat_1710_, v_k_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___boxed(lean_object* v_00_u03b1_1718_, lean_object* v_u_1719_, lean_object* v_00_u03c3s_1720_, lean_object* v_H_1721_, lean_object* v_pat_1722_, lean_object* v_k_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore(v_00_u03b1_1718_, v_u_1719_, v_00_u03c3s_1720_, v_H_1721_, v_pat_1722_, v_k_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(lean_object* v_00_u03b1_1730_, lean_object* v_00_u03c3s_1731_, lean_object* v_hyp_1732_, lean_object* v_name_1733_, lean_object* v_k_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1731_, v_hyp_1732_, v_name_1733_, v_k_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___boxed(lean_object* v_00_u03b1_1741_, lean_object* v_00_u03c3s_1742_, lean_object* v_hyp_1743_, lean_object* v_name_1744_, lean_object* v_k_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(v_00_u03b1_1741_, v_00_u03c3s_1742_, v_hyp_1743_, v_name_1744_, v_k_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg(){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0);
v___x_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg___boxed(lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(lean_object* v_00_u03b1_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___boxed(lean_object* v_00_u03b1_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(v_00_u03b1_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(lean_object* v_x_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_apply_9(v_x_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, lean_box(0));
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0___boxed(lean_object* v_x_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(v_x_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(lean_object* v_mvarId_1801_, lean_object* v_x_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v___f_1812_; lean_object* v___x_1813_; 
v___f_1812_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1812_, 0, v_x_1802_);
lean_closure_set(v___f_1812_, 1, v___y_1803_);
lean_closure_set(v___f_1812_, 2, v___y_1804_);
lean_closure_set(v___f_1812_, 3, v___y_1805_);
lean_closure_set(v___f_1812_, 4, v___y_1806_);
v___x_1813_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1801_, v___f_1812_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
if (lean_obj_tag(v___x_1813_) == 0)
{
return v___x_1813_;
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___boxed(lean_object* v_mvarId_1822_, lean_object* v_x_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_mvarId_1822_, v_x_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3(lean_object* v_00_u03b1_1834_, lean_object* v_mvarId_1835_, lean_object* v_x_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_mvarId_1835_, v_x_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___boxed(lean_object* v_00_u03b1_1847_, lean_object* v_mvarId_1848_, lean_object* v_x_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3(v_00_u03b1_1847_, v_mvarId_1848_, v_x_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__19_spec__21___redArg(lean_object* v_x_1860_, lean_object* v_x_1861_, lean_object* v_x_1862_, lean_object* v_x_1863_){
_start:
{
lean_object* v_ks_1864_; lean_object* v_vs_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1889_; 
v_ks_1864_ = lean_ctor_get(v_x_1860_, 0);
v_vs_1865_ = lean_ctor_get(v_x_1860_, 1);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_x_1860_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1867_ = v_x_1860_;
v_isShared_1868_ = v_isSharedCheck_1889_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_vs_1865_);
lean_inc(v_ks_1864_);
lean_dec(v_x_1860_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1889_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1869_ = lean_array_get_size(v_ks_1864_);
v___x_1870_ = lean_nat_dec_lt(v_x_1861_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
lean_dec(v_x_1861_);
v___x_1871_ = lean_array_push(v_ks_1864_, v_x_1862_);
v___x_1872_ = lean_array_push(v_vs_1865_, v_x_1863_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 1, v___x_1872_);
lean_ctor_set(v___x_1867_, 0, v___x_1871_);
v___x_1874_ = v___x_1867_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1871_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
else
{
lean_object* v_k_x27_1876_; uint8_t v___x_1877_; 
v_k_x27_1876_ = lean_array_fget_borrowed(v_ks_1864_, v_x_1861_);
v___x_1877_ = l_Lean_instBEqMVarId_beq(v_x_1862_, v_k_x27_1876_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1879_; 
if (v_isShared_1868_ == 0)
{
v___x_1879_ = v___x_1867_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_ks_1864_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_vs_1865_);
v___x_1879_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_unsigned_to_nat(1u);
v___x_1881_ = lean_nat_add(v_x_1861_, v___x_1880_);
lean_dec(v_x_1861_);
v_x_1860_ = v___x_1879_;
v_x_1861_ = v___x_1881_;
goto _start;
}
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1884_ = lean_array_fset(v_ks_1864_, v_x_1861_, v_x_1862_);
v___x_1885_ = lean_array_fset(v_vs_1865_, v_x_1861_, v_x_1863_);
lean_dec(v_x_1861_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 1, v___x_1885_);
lean_ctor_set(v___x_1867_, 0, v___x_1884_);
v___x_1887_ = v___x_1867_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1884_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__19___redArg(lean_object* v_n_1890_, lean_object* v_k_1891_, lean_object* v_v_1892_){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_unsigned_to_nat(0u);
v___x_1894_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__19_spec__21___redArg(v_n_1890_, v___x_1893_, v_k_1891_, v_v_1892_);
return v___x_1894_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__0(void){
_start:
{
size_t v___x_1895_; size_t v___x_1896_; size_t v___x_1897_; 
v___x_1895_ = ((size_t)5ULL);
v___x_1896_ = ((size_t)1ULL);
v___x_1897_ = lean_usize_shift_left(v___x_1896_, v___x_1895_);
return v___x_1897_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_1898_; size_t v___x_1899_; size_t v___x_1900_; 
v___x_1898_ = ((size_t)1ULL);
v___x_1899_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__0);
v___x_1900_ = lean_usize_sub(v___x_1899_, v___x_1898_);
return v___x_1900_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__2(void){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg(lean_object* v_x_1902_, size_t v_x_1903_, size_t v_x_1904_, lean_object* v_x_1905_, lean_object* v_x_1906_){
_start:
{
if (lean_obj_tag(v_x_1902_) == 0)
{
lean_object* v_es_1907_; size_t v___x_1908_; size_t v___x_1909_; size_t v___x_1910_; size_t v___x_1911_; lean_object* v_j_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v_es_1907_ = lean_ctor_get(v_x_1902_, 0);
v___x_1908_ = ((size_t)5ULL);
v___x_1909_ = ((size_t)1ULL);
v___x_1910_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__1);
v___x_1911_ = lean_usize_land(v_x_1903_, v___x_1910_);
v_j_1912_ = lean_usize_to_nat(v___x_1911_);
v___x_1913_ = lean_array_get_size(v_es_1907_);
v___x_1914_ = lean_nat_dec_lt(v_j_1912_, v___x_1913_);
if (v___x_1914_ == 0)
{
lean_dec(v_j_1912_);
lean_dec(v_x_1906_);
lean_dec(v_x_1905_);
return v_x_1902_;
}
else
{
lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1951_; 
lean_inc_ref(v_es_1907_);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_x_1902_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; 
v_unused_1952_ = lean_ctor_get(v_x_1902_, 0);
lean_dec(v_unused_1952_);
v___x_1916_ = v_x_1902_;
v_isShared_1917_ = v_isSharedCheck_1951_;
goto v_resetjp_1915_;
}
else
{
lean_dec(v_x_1902_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1951_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v_v_1918_; lean_object* v___x_1919_; lean_object* v_xs_x27_1920_; lean_object* v___y_1922_; 
v_v_1918_ = lean_array_fget(v_es_1907_, v_j_1912_);
v___x_1919_ = lean_box(0);
v_xs_x27_1920_ = lean_array_fset(v_es_1907_, v_j_1912_, v___x_1919_);
switch(lean_obj_tag(v_v_1918_))
{
case 0:
{
lean_object* v_key_1927_; lean_object* v_val_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1938_; 
v_key_1927_ = lean_ctor_get(v_v_1918_, 0);
v_val_1928_ = lean_ctor_get(v_v_1918_, 1);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_v_1918_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1930_ = v_v_1918_;
v_isShared_1931_ = v_isSharedCheck_1938_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_val_1928_);
lean_inc(v_key_1927_);
lean_dec(v_v_1918_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1938_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
uint8_t v___x_1932_; 
v___x_1932_ = l_Lean_instBEqMVarId_beq(v_x_1905_, v_key_1927_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
lean_del_object(v___x_1930_);
v___x_1933_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1927_, v_val_1928_, v_x_1905_, v_x_1906_);
v___x_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
v___y_1922_ = v___x_1934_;
goto v___jp_1921_;
}
else
{
lean_object* v___x_1936_; 
lean_dec(v_val_1928_);
lean_dec(v_key_1927_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 1, v_x_1906_);
lean_ctor_set(v___x_1930_, 0, v_x_1905_);
v___x_1936_ = v___x_1930_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_x_1905_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_x_1906_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
v___y_1922_ = v___x_1936_;
goto v___jp_1921_;
}
}
}
}
case 1:
{
lean_object* v_node_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1949_; 
v_node_1939_ = lean_ctor_get(v_v_1918_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_v_1918_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1941_ = v_v_1918_;
v_isShared_1942_ = v_isSharedCheck_1949_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_node_1939_);
lean_dec(v_v_1918_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1949_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
size_t v___x_1943_; size_t v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1943_ = lean_usize_shift_right(v_x_1903_, v___x_1908_);
v___x_1944_ = lean_usize_add(v_x_1904_, v___x_1909_);
v___x_1945_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg(v_node_1939_, v___x_1943_, v___x_1944_, v_x_1905_, v_x_1906_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v___x_1945_);
v___x_1947_ = v___x_1941_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
v___y_1922_ = v___x_1947_;
goto v___jp_1921_;
}
}
}
default: 
{
lean_object* v___x_1950_; 
v___x_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1950_, 0, v_x_1905_);
lean_ctor_set(v___x_1950_, 1, v_x_1906_);
v___y_1922_ = v___x_1950_;
goto v___jp_1921_;
}
}
v___jp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1923_ = lean_array_fset(v_xs_x27_1920_, v_j_1912_, v___y_1922_);
lean_dec(v_j_1912_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 0, v___x_1923_);
v___x_1925_ = v___x_1916_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
else
{
lean_object* v_ks_1953_; lean_object* v_vs_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1974_; 
v_ks_1953_ = lean_ctor_get(v_x_1902_, 0);
v_vs_1954_ = lean_ctor_get(v_x_1902_, 1);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_x_1902_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1956_ = v_x_1902_;
v_isShared_1957_ = v_isSharedCheck_1974_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_vs_1954_);
lean_inc(v_ks_1953_);
lean_dec(v_x_1902_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1974_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_ks_1953_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_vs_1954_);
v___x_1959_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v_newNode_1960_; uint8_t v___y_1962_; size_t v___x_1968_; uint8_t v___x_1969_; 
v_newNode_1960_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__19___redArg(v___x_1959_, v_x_1905_, v_x_1906_);
v___x_1968_ = ((size_t)7ULL);
v___x_1969_ = lean_usize_dec_le(v___x_1968_, v_x_1904_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1970_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1960_);
v___x_1971_ = lean_unsigned_to_nat(4u);
v___x_1972_ = lean_nat_dec_lt(v___x_1970_, v___x_1971_);
lean_dec(v___x_1970_);
v___y_1962_ = v___x_1972_;
goto v___jp_1961_;
}
else
{
v___y_1962_ = v___x_1969_;
goto v___jp_1961_;
}
v___jp_1961_:
{
if (v___y_1962_ == 0)
{
lean_object* v_ks_1963_; lean_object* v_vs_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v_ks_1963_ = lean_ctor_get(v_newNode_1960_, 0);
lean_inc_ref(v_ks_1963_);
v_vs_1964_ = lean_ctor_get(v_newNode_1960_, 1);
lean_inc_ref(v_vs_1964_);
lean_dec_ref(v_newNode_1960_);
v___x_1965_ = lean_unsigned_to_nat(0u);
v___x_1966_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__2);
v___x_1967_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__20___redArg(v_x_1904_, v_ks_1963_, v_vs_1964_, v___x_1965_, v___x_1966_);
lean_dec_ref(v_vs_1964_);
lean_dec_ref(v_ks_1963_);
return v___x_1967_;
}
else
{
return v_newNode_1960_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__20___redArg(size_t v_depth_1975_, lean_object* v_keys_1976_, lean_object* v_vals_1977_, lean_object* v_i_1978_, lean_object* v_entries_1979_){
_start:
{
lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1980_ = lean_array_get_size(v_keys_1976_);
v___x_1981_ = lean_nat_dec_lt(v_i_1978_, v___x_1980_);
if (v___x_1981_ == 0)
{
lean_dec(v_i_1978_);
return v_entries_1979_;
}
else
{
lean_object* v_k_1982_; lean_object* v_v_1983_; uint64_t v___x_1984_; size_t v_h_1985_; size_t v___x_1986_; lean_object* v___x_1987_; size_t v___x_1988_; size_t v___x_1989_; size_t v___x_1990_; size_t v_h_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v_k_1982_ = lean_array_fget_borrowed(v_keys_1976_, v_i_1978_);
v_v_1983_ = lean_array_fget_borrowed(v_vals_1977_, v_i_1978_);
v___x_1984_ = l_Lean_instHashableMVarId_hash(v_k_1982_);
v_h_1985_ = lean_uint64_to_usize(v___x_1984_);
v___x_1986_ = ((size_t)5ULL);
v___x_1987_ = lean_unsigned_to_nat(1u);
v___x_1988_ = ((size_t)1ULL);
v___x_1989_ = lean_usize_sub(v_depth_1975_, v___x_1988_);
v___x_1990_ = lean_usize_mul(v___x_1986_, v___x_1989_);
v_h_1991_ = lean_usize_shift_right(v_h_1985_, v___x_1990_);
v___x_1992_ = lean_nat_add(v_i_1978_, v___x_1987_);
lean_dec(v_i_1978_);
lean_inc(v_v_1983_);
lean_inc(v_k_1982_);
v___x_1993_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg(v_entries_1979_, v_h_1991_, v_depth_1975_, v_k_1982_, v_v_1983_);
v_i_1978_ = v___x_1992_;
v_entries_1979_ = v___x_1993_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__20___redArg___boxed(lean_object* v_depth_1995_, lean_object* v_keys_1996_, lean_object* v_vals_1997_, lean_object* v_i_1998_, lean_object* v_entries_1999_){
_start:
{
size_t v_depth_boxed_2000_; lean_object* v_res_2001_; 
v_depth_boxed_2000_ = lean_unbox_usize(v_depth_1995_);
lean_dec(v_depth_1995_);
v_res_2001_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__20___redArg(v_depth_boxed_2000_, v_keys_1996_, v_vals_1997_, v_i_1998_, v_entries_1999_);
lean_dec_ref(v_vals_1997_);
lean_dec_ref(v_keys_1996_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___boxed(lean_object* v_x_2002_, lean_object* v_x_2003_, lean_object* v_x_2004_, lean_object* v_x_2005_, lean_object* v_x_2006_){
_start:
{
size_t v_x_20475__boxed_2007_; size_t v_x_20476__boxed_2008_; lean_object* v_res_2009_; 
v_x_20475__boxed_2007_ = lean_unbox_usize(v_x_2003_);
lean_dec(v_x_2003_);
v_x_20476__boxed_2008_ = lean_unbox_usize(v_x_2004_);
lean_dec(v_x_2004_);
v_res_2009_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg(v_x_2002_, v_x_20475__boxed_2007_, v_x_20476__boxed_2008_, v_x_2005_, v_x_2006_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10___redArg(lean_object* v_x_2010_, lean_object* v_x_2011_, lean_object* v_x_2012_){
_start:
{
uint64_t v___x_2013_; size_t v___x_2014_; size_t v___x_2015_; lean_object* v___x_2016_; 
v___x_2013_ = l_Lean_instHashableMVarId_hash(v_x_2011_);
v___x_2014_ = lean_uint64_to_usize(v___x_2013_);
v___x_2015_ = ((size_t)1ULL);
v___x_2016_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg(v_x_2010_, v___x_2014_, v___x_2015_, v_x_2011_, v_x_2012_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(lean_object* v_mvarId_2017_, lean_object* v_val_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v___x_2021_; lean_object* v_mctx_2022_; lean_object* v_cache_2023_; lean_object* v_zetaDeltaFVarIds_2024_; lean_object* v_postponed_2025_; lean_object* v_diag_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2053_; 
v___x_2021_ = lean_st_ref_take(v___y_2019_);
v_mctx_2022_ = lean_ctor_get(v___x_2021_, 0);
v_cache_2023_ = lean_ctor_get(v___x_2021_, 1);
v_zetaDeltaFVarIds_2024_ = lean_ctor_get(v___x_2021_, 2);
v_postponed_2025_ = lean_ctor_get(v___x_2021_, 3);
v_diag_2026_ = lean_ctor_get(v___x_2021_, 4);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2028_ = v___x_2021_;
v_isShared_2029_ = v_isSharedCheck_2053_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_diag_2026_);
lean_inc(v_postponed_2025_);
lean_inc(v_zetaDeltaFVarIds_2024_);
lean_inc(v_cache_2023_);
lean_inc(v_mctx_2022_);
lean_dec(v___x_2021_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2053_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v_depth_2030_; lean_object* v_levelAssignDepth_2031_; lean_object* v_mvarCounter_2032_; lean_object* v_lDepth_2033_; lean_object* v_decls_2034_; lean_object* v_userNames_2035_; lean_object* v_lAssignment_2036_; lean_object* v_eAssignment_2037_; lean_object* v_dAssignment_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2052_; 
v_depth_2030_ = lean_ctor_get(v_mctx_2022_, 0);
v_levelAssignDepth_2031_ = lean_ctor_get(v_mctx_2022_, 1);
v_mvarCounter_2032_ = lean_ctor_get(v_mctx_2022_, 2);
v_lDepth_2033_ = lean_ctor_get(v_mctx_2022_, 3);
v_decls_2034_ = lean_ctor_get(v_mctx_2022_, 4);
v_userNames_2035_ = lean_ctor_get(v_mctx_2022_, 5);
v_lAssignment_2036_ = lean_ctor_get(v_mctx_2022_, 6);
v_eAssignment_2037_ = lean_ctor_get(v_mctx_2022_, 7);
v_dAssignment_2038_ = lean_ctor_get(v_mctx_2022_, 8);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_mctx_2022_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2040_ = v_mctx_2022_;
v_isShared_2041_ = v_isSharedCheck_2052_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_dAssignment_2038_);
lean_inc(v_eAssignment_2037_);
lean_inc(v_lAssignment_2036_);
lean_inc(v_userNames_2035_);
lean_inc(v_decls_2034_);
lean_inc(v_lDepth_2033_);
lean_inc(v_mvarCounter_2032_);
lean_inc(v_levelAssignDepth_2031_);
lean_inc(v_depth_2030_);
lean_dec(v_mctx_2022_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2052_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2042_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10___redArg(v_eAssignment_2037_, v_mvarId_2017_, v_val_2018_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 7, v___x_2042_);
v___x_2044_ = v___x_2040_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_depth_2030_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_levelAssignDepth_2031_);
lean_ctor_set(v_reuseFailAlloc_2051_, 2, v_mvarCounter_2032_);
lean_ctor_set(v_reuseFailAlloc_2051_, 3, v_lDepth_2033_);
lean_ctor_set(v_reuseFailAlloc_2051_, 4, v_decls_2034_);
lean_ctor_set(v_reuseFailAlloc_2051_, 5, v_userNames_2035_);
lean_ctor_set(v_reuseFailAlloc_2051_, 6, v_lAssignment_2036_);
lean_ctor_set(v_reuseFailAlloc_2051_, 7, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2051_, 8, v_dAssignment_2038_);
v___x_2044_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2046_; 
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2044_);
v___x_2046_ = v___x_2028_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_cache_2023_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v_zetaDeltaFVarIds_2024_);
lean_ctor_set(v_reuseFailAlloc_2050_, 3, v_postponed_2025_);
lean_ctor_set(v_reuseFailAlloc_2050_, 4, v_diag_2026_);
v___x_2046_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2047_ = lean_st_ref_set(v___y_2019_, v___x_2046_);
v___x_2048_ = lean_box(0);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
return v___x_2049_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg___boxed(lean_object* v_mvarId_2054_, lean_object* v_val_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_mvarId_2054_, v_val_2055_, v___y_2056_);
lean_dec(v___y_2056_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(lean_object* v_snd_2061_, lean_object* v_hyp_2062_, lean_object* v_a_2063_, lean_object* v_fst_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v___x_2074_; 
lean_inc(v___y_2072_);
lean_inc_ref(v___y_2071_);
lean_inc(v___y_2070_);
lean_inc_ref(v___y_2069_);
lean_inc_ref(v_snd_2061_);
v___x_2074_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_snd_2061_, v_hyp_2062_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v_focusHyp_2078_; lean_object* v_restHyps_2079_; lean_object* v_u_2080_; lean_object* v_00_u03c3s_2081_; lean_object* v_target_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref(v___x_2074_);
v___x_2076_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0));
v___x_2077_ = lean_st_mk_ref(v___x_2076_);
v_focusHyp_2078_ = lean_ctor_get(v_a_2075_, 0);
v_restHyps_2079_ = lean_ctor_get(v_a_2075_, 1);
v_u_2080_ = lean_ctor_get(v_snd_2061_, 0);
v_00_u03c3s_2081_ = lean_ctor_get(v_snd_2061_, 1);
v_target_2082_ = lean_ctor_get(v_snd_2061_, 3);
lean_inc_ref(v_restHyps_2079_);
lean_inc_ref(v_target_2082_);
lean_inc_ref(v_00_u03c3s_2081_);
lean_inc(v___x_2077_);
lean_inc(v_u_2080_);
v___x_2083_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___boxed), 11, 5);
lean_closure_set(v___x_2083_, 0, v_u_2080_);
lean_closure_set(v___x_2083_, 1, v___x_2077_);
lean_closure_set(v___x_2083_, 2, v_00_u03c3s_2081_);
lean_closure_set(v___x_2083_, 3, v_target_2082_);
lean_closure_set(v___x_2083_, 4, v_restHyps_2079_);
lean_inc(v___y_2072_);
lean_inc_ref(v___y_2071_);
lean_inc(v___y_2070_);
lean_inc_ref(v___y_2069_);
lean_inc_ref(v_focusHyp_2078_);
lean_inc_ref(v_00_u03c3s_2081_);
lean_inc(v_u_2080_);
v___x_2084_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_2080_, v_00_u03c3s_2081_, v_focusHyp_2078_, v_a_2063_, v___x_2083_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v_snd_2086_; lean_object* v_snd_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref(v___x_2084_);
v_snd_2086_ = lean_ctor_get(v_a_2085_, 1);
lean_inc(v_snd_2086_);
lean_dec(v_a_2085_);
v_snd_2087_ = lean_ctor_get(v_snd_2086_, 1);
lean_inc(v_snd_2087_);
lean_dec(v_snd_2086_);
v___x_2088_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps(v_a_2075_, v_snd_2061_, v_snd_2087_);
v___x_2089_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_fst_2064_, v___x_2088_, v___y_2070_);
lean_dec_ref(v___x_2089_);
v___x_2090_ = lean_st_ref_get(v___x_2077_);
lean_dec(v___x_2077_);
v___x_2091_ = lean_array_to_list(v___x_2090_);
v___x_2092_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2091_, v___y_2066_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
return v___x_2092_;
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_dec(v___x_2077_);
lean_dec(v_a_2075_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v_fst_2064_);
lean_dec_ref(v_snd_2061_);
v_a_2093_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2084_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2084_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v_fst_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v_snd_2061_);
v_a_2101_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2074_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2074_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___boxed(lean_object* v_snd_2109_, lean_object* v_hyp_2110_, lean_object* v_a_2111_, lean_object* v_fst_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(v_snd_2109_, v_hyp_2110_, v_a_2111_, v_fst_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7_spec__12___redArg(lean_object* v_msg_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_ref_2129_; lean_object* v___x_2130_; lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2139_; 
v_ref_2129_ = lean_ctor_get(v___y_2126_, 5);
v___x_2130_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2133_ = v___x_2130_;
v_isShared_2134_ = v_isSharedCheck_2139_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2130_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2139_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; lean_object* v___x_2137_; 
lean_inc(v_ref_2129_);
v___x_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2135_, 0, v_ref_2129_);
lean_ctor_set(v___x_2135_, 1, v_a_2131_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set_tag(v___x_2133_, 1);
lean_ctor_set(v___x_2133_, 0, v___x_2135_);
v___x_2137_ = v___x_2133_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7_spec__12___redArg___boxed(lean_object* v_msg_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7_spec__12___redArg(v_msg_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(lean_object* v_ref_2147_, lean_object* v_msg_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_fileName_2158_; lean_object* v_fileMap_2159_; lean_object* v_options_2160_; lean_object* v_currRecDepth_2161_; lean_object* v_maxRecDepth_2162_; lean_object* v_ref_2163_; lean_object* v_currNamespace_2164_; lean_object* v_openDecls_2165_; lean_object* v_initHeartbeats_2166_; lean_object* v_maxHeartbeats_2167_; lean_object* v_quotContext_2168_; lean_object* v_currMacroScope_2169_; uint8_t v_diag_2170_; lean_object* v_cancelTk_x3f_2171_; uint8_t v_suppressElabErrors_2172_; lean_object* v_inheritedTraceOptions_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2182_; 
v_fileName_2158_ = lean_ctor_get(v___y_2155_, 0);
v_fileMap_2159_ = lean_ctor_get(v___y_2155_, 1);
v_options_2160_ = lean_ctor_get(v___y_2155_, 2);
v_currRecDepth_2161_ = lean_ctor_get(v___y_2155_, 3);
v_maxRecDepth_2162_ = lean_ctor_get(v___y_2155_, 4);
v_ref_2163_ = lean_ctor_get(v___y_2155_, 5);
v_currNamespace_2164_ = lean_ctor_get(v___y_2155_, 6);
v_openDecls_2165_ = lean_ctor_get(v___y_2155_, 7);
v_initHeartbeats_2166_ = lean_ctor_get(v___y_2155_, 8);
v_maxHeartbeats_2167_ = lean_ctor_get(v___y_2155_, 9);
v_quotContext_2168_ = lean_ctor_get(v___y_2155_, 10);
v_currMacroScope_2169_ = lean_ctor_get(v___y_2155_, 11);
v_diag_2170_ = lean_ctor_get_uint8(v___y_2155_, sizeof(void*)*14);
v_cancelTk_x3f_2171_ = lean_ctor_get(v___y_2155_, 12);
v_suppressElabErrors_2172_ = lean_ctor_get_uint8(v___y_2155_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2173_ = lean_ctor_get(v___y_2155_, 13);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___y_2155_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2175_ = v___y_2155_;
v_isShared_2176_ = v_isSharedCheck_2182_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_inheritedTraceOptions_2173_);
lean_inc(v_cancelTk_x3f_2171_);
lean_inc(v_currMacroScope_2169_);
lean_inc(v_quotContext_2168_);
lean_inc(v_maxHeartbeats_2167_);
lean_inc(v_initHeartbeats_2166_);
lean_inc(v_openDecls_2165_);
lean_inc(v_currNamespace_2164_);
lean_inc(v_ref_2163_);
lean_inc(v_maxRecDepth_2162_);
lean_inc(v_currRecDepth_2161_);
lean_inc(v_options_2160_);
lean_inc(v_fileMap_2159_);
lean_inc(v_fileName_2158_);
lean_dec(v___y_2155_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2182_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v_ref_2177_; lean_object* v___x_2179_; 
v_ref_2177_ = l_Lean_replaceRef(v_ref_2147_, v_ref_2163_);
lean_dec(v_ref_2163_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 5, v_ref_2177_);
v___x_2179_ = v___x_2175_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_fileName_2158_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_fileMap_2159_);
lean_ctor_set(v_reuseFailAlloc_2181_, 2, v_options_2160_);
lean_ctor_set(v_reuseFailAlloc_2181_, 3, v_currRecDepth_2161_);
lean_ctor_set(v_reuseFailAlloc_2181_, 4, v_maxRecDepth_2162_);
lean_ctor_set(v_reuseFailAlloc_2181_, 5, v_ref_2177_);
lean_ctor_set(v_reuseFailAlloc_2181_, 6, v_currNamespace_2164_);
lean_ctor_set(v_reuseFailAlloc_2181_, 7, v_openDecls_2165_);
lean_ctor_set(v_reuseFailAlloc_2181_, 8, v_initHeartbeats_2166_);
lean_ctor_set(v_reuseFailAlloc_2181_, 9, v_maxHeartbeats_2167_);
lean_ctor_set(v_reuseFailAlloc_2181_, 10, v_quotContext_2168_);
lean_ctor_set(v_reuseFailAlloc_2181_, 11, v_currMacroScope_2169_);
lean_ctor_set(v_reuseFailAlloc_2181_, 12, v_cancelTk_x3f_2171_);
lean_ctor_set(v_reuseFailAlloc_2181_, 13, v_inheritedTraceOptions_2173_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, sizeof(void*)*14, v_diag_2170_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, sizeof(void*)*14 + 1, v_suppressElabErrors_2172_);
v___x_2179_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7_spec__12___redArg(v_msg_2148_, v___y_2153_, v___y_2154_, v___x_2179_, v___y_2156_);
lean_dec_ref(v___x_2179_);
return v___x_2180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2183_, lean_object* v_msg_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_ref_2183_, v_msg_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
lean_dec(v___y_2192_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v_ref_2183_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(lean_object* v_cls_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v_options_2201_; uint8_t v_hasTrace_2202_; 
v_options_2201_ = lean_ctor_get(v___y_2199_, 2);
v_hasTrace_2202_ = lean_ctor_get_uint8(v_options_2201_, sizeof(void*)*1);
if (v_hasTrace_2202_ == 0)
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec(v_cls_2198_);
v___x_2203_ = lean_box(v_hasTrace_2202_);
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
return v___x_2204_;
}
else
{
lean_object* v_inheritedTraceOptions_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v_inheritedTraceOptions_2205_ = lean_ctor_get(v___y_2199_, 13);
v___x_2206_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1));
v___x_2207_ = l_Lean_Name_append(v___x_2206_, v_cls_2198_);
v___x_2208_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2205_, v_options_2201_, v___x_2207_);
lean_dec(v___x_2207_);
v___x_2209_ = lean_box(v___x_2208_);
v___x_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
return v___x_2210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___boxed(lean_object* v_cls_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_2211_, v___y_2212_);
lean_dec_ref(v___y_2212_);
return v_res_2214_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2215_; double v___x_2216_; 
v___x_2215_ = lean_unsigned_to_nat(0u);
v___x_2216_ = lean_float_of_nat(v___x_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(lean_object* v_cls_2220_, lean_object* v_msg_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_ref_2227_; lean_object* v___x_2228_; lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2273_; 
v_ref_2227_ = lean_ctor_get(v___y_2224_, 5);
v___x_2228_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2273_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2273_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; lean_object* v_traceState_2234_; lean_object* v_env_2235_; lean_object* v_nextMacroScope_2236_; lean_object* v_ngen_2237_; lean_object* v_auxDeclNGen_2238_; lean_object* v_cache_2239_; lean_object* v_messages_2240_; lean_object* v_infoState_2241_; lean_object* v_snapshotTasks_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2272_; 
v___x_2233_ = lean_st_ref_take(v___y_2225_);
v_traceState_2234_ = lean_ctor_get(v___x_2233_, 4);
v_env_2235_ = lean_ctor_get(v___x_2233_, 0);
v_nextMacroScope_2236_ = lean_ctor_get(v___x_2233_, 1);
v_ngen_2237_ = lean_ctor_get(v___x_2233_, 2);
v_auxDeclNGen_2238_ = lean_ctor_get(v___x_2233_, 3);
v_cache_2239_ = lean_ctor_get(v___x_2233_, 5);
v_messages_2240_ = lean_ctor_get(v___x_2233_, 6);
v_infoState_2241_ = lean_ctor_get(v___x_2233_, 7);
v_snapshotTasks_2242_ = lean_ctor_get(v___x_2233_, 8);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2244_ = v___x_2233_;
v_isShared_2245_ = v_isSharedCheck_2272_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_snapshotTasks_2242_);
lean_inc(v_infoState_2241_);
lean_inc(v_messages_2240_);
lean_inc(v_cache_2239_);
lean_inc(v_traceState_2234_);
lean_inc(v_auxDeclNGen_2238_);
lean_inc(v_ngen_2237_);
lean_inc(v_nextMacroScope_2236_);
lean_inc(v_env_2235_);
lean_dec(v___x_2233_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2272_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
uint64_t v_tid_2246_; lean_object* v_traces_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2271_; 
v_tid_2246_ = lean_ctor_get_uint64(v_traceState_2234_, sizeof(void*)*1);
v_traces_2247_ = lean_ctor_get(v_traceState_2234_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v_traceState_2234_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2249_ = v_traceState_2234_;
v_isShared_2250_ = v_isSharedCheck_2271_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_traces_2247_);
lean_dec(v_traceState_2234_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2271_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; double v___x_2252_; uint8_t v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2251_ = lean_box(0);
v___x_2252_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___closed__0);
v___x_2253_ = 0;
v___x_2254_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___closed__1));
v___x_2255_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2255_, 0, v_cls_2220_);
lean_ctor_set(v___x_2255_, 1, v___x_2251_);
lean_ctor_set(v___x_2255_, 2, v___x_2254_);
lean_ctor_set_float(v___x_2255_, sizeof(void*)*3, v___x_2252_);
lean_ctor_set_float(v___x_2255_, sizeof(void*)*3 + 8, v___x_2252_);
lean_ctor_set_uint8(v___x_2255_, sizeof(void*)*3 + 16, v___x_2253_);
v___x_2256_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___closed__2));
v___x_2257_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2255_);
lean_ctor_set(v___x_2257_, 1, v_a_2229_);
lean_ctor_set(v___x_2257_, 2, v___x_2256_);
lean_inc(v_ref_2227_);
v___x_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2258_, 0, v_ref_2227_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = l_Lean_PersistentArray_push___redArg(v_traces_2247_, v___x_2258_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v___x_2259_);
v___x_2261_ = v___x_2249_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2259_);
lean_ctor_set_uint64(v_reuseFailAlloc_2270_, sizeof(void*)*1, v_tid_2246_);
v___x_2261_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
lean_object* v___x_2263_; 
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 4, v___x_2261_);
v___x_2263_ = v___x_2244_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_env_2235_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_nextMacroScope_2236_);
lean_ctor_set(v_reuseFailAlloc_2269_, 2, v_ngen_2237_);
lean_ctor_set(v_reuseFailAlloc_2269_, 3, v_auxDeclNGen_2238_);
lean_ctor_set(v_reuseFailAlloc_2269_, 4, v___x_2261_);
lean_ctor_set(v_reuseFailAlloc_2269_, 5, v_cache_2239_);
lean_ctor_set(v_reuseFailAlloc_2269_, 6, v_messages_2240_);
lean_ctor_set(v_reuseFailAlloc_2269_, 7, v_infoState_2241_);
lean_ctor_set(v_reuseFailAlloc_2269_, 8, v_snapshotTasks_2242_);
v___x_2263_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2267_; 
v___x_2264_ = lean_st_ref_set(v___y_2225_, v___x_2263_);
v___x_2265_ = lean_box(0);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v___x_2265_);
v___x_2267_ = v___x_2231_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2265_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___boxed(lean_object* v_cls_2274_, lean_object* v_msg_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v_cls_2274_, v_msg_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(lean_object* v_as_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
if (lean_obj_tag(v_as_2282_) == 0)
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = lean_box(0);
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
return v___x_2293_;
}
else
{
lean_object* v_head_2294_; lean_object* v_tail_2295_; lean_object* v_fst_2296_; lean_object* v_snd_2297_; lean_object* v___x_2298_; lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2311_; 
v_head_2294_ = lean_ctor_get(v_as_2282_, 0);
lean_inc(v_head_2294_);
v_tail_2295_ = lean_ctor_get(v_as_2282_, 1);
lean_inc(v_tail_2295_);
lean_dec_ref(v_as_2282_);
v_fst_2296_ = lean_ctor_get(v_head_2294_, 0);
lean_inc(v_fst_2296_);
v_snd_2297_ = lean_ctor_get(v_head_2294_, 1);
lean_inc(v_snd_2297_);
lean_dec(v_head_2294_);
lean_inc(v_fst_2296_);
v___x_2298_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_fst_2296_, v___y_2289_);
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2311_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2311_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
uint8_t v___x_2303_; 
v___x_2303_ = lean_unbox(v_a_2299_);
lean_dec(v_a_2299_);
if (v___x_2303_ == 0)
{
lean_del_object(v___x_2301_);
lean_dec(v_snd_2297_);
lean_dec(v_fst_2296_);
v_as_2282_ = v_tail_2295_;
goto _start;
}
else
{
lean_object* v___x_2306_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set_tag(v___x_2301_, 3);
lean_ctor_set(v___x_2301_, 0, v_snd_2297_);
v___x_2306_ = v___x_2301_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_snd_2297_);
v___x_2306_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = l_Lean_MessageData_ofFormat(v___x_2306_);
v___x_2308_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v_fst_2296_, v___x_2307_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_dec_ref(v___x_2308_);
v_as_2282_ = v_tail_2295_;
goto _start;
}
else
{
lean_dec(v_tail_2295_);
return v___x_2308_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___boxed(lean_object* v_as_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(v_as_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___redArg(lean_object* v_x_2323_, lean_object* v___y_2324_){
_start:
{
if (lean_obj_tag(v_x_2323_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2326_; 
v_a_2325_ = lean_ctor_get(v_x_2323_, 0);
lean_inc(v_a_2325_);
v___x_2326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2326_, 0, v_a_2325_);
lean_ctor_set(v___x_2326_, 1, v___y_2324_);
return v___x_2326_;
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2328_; 
v_a_2327_ = lean_ctor_get(v_x_2323_, 0);
lean_inc(v_a_2327_);
v___x_2328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2328_, 0, v_a_2327_);
lean_ctor_set(v___x_2328_, 1, v___y_2324_);
return v___x_2328_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___redArg___boxed(lean_object* v_x_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___redArg(v_x_2329_, v___y_2330_);
lean_dec_ref(v_x_2329_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(lean_object* v_env_2332_, lean_object* v_stx_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2332_, v_stx_2333_, v___y_2334_, v___y_2335_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
if (lean_obj_tag(v_a_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2346_; 
v_a_2338_ = lean_ctor_get(v___x_2336_, 1);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2346_ == 0)
{
lean_object* v_unused_2347_; 
v_unused_2347_ = lean_ctor_get(v___x_2336_, 0);
lean_dec(v_unused_2347_);
v___x_2340_ = v___x_2336_;
v_isShared_2341_ = v_isSharedCheck_2346_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2336_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2346_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2342_; lean_object* v___x_2344_; 
v___x_2342_ = lean_box(0);
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v___x_2342_);
v___x_2344_ = v___x_2340_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2342_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v_a_2338_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
else
{
lean_object* v_val_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2376_; 
v_val_2348_ = lean_ctor_get(v_a_2337_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_a_2337_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2350_ = v_a_2337_;
v_isShared_2351_ = v_isSharedCheck_2376_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_val_2348_);
lean_dec(v_a_2337_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2376_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v_snd_2352_; 
v_snd_2352_ = lean_ctor_get(v_val_2348_, 1);
lean_inc(v_snd_2352_);
lean_dec(v_val_2348_);
if (lean_obj_tag(v_snd_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2362_; 
lean_del_object(v___x_2350_);
v_a_2353_ = lean_ctor_get(v___x_2336_, 1);
lean_inc(v_a_2353_);
lean_dec_ref(v___x_2336_);
v_a_2354_ = lean_ctor_get(v_snd_2352_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v_snd_2352_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2356_ = v_snd_2352_;
v_isShared_2357_ = v_isSharedCheck_2362_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v_snd_2352_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2362_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___redArg(v___x_2359_, v_a_2353_);
lean_dec_ref(v___x_2359_);
return v___x_2360_;
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2375_; 
v_a_2363_ = lean_ctor_get(v___x_2336_, 1);
lean_inc(v_a_2363_);
lean_dec_ref(v___x_2336_);
v_a_2364_ = lean_ctor_get(v_snd_2352_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_snd_2352_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2366_ = v_snd_2352_;
v_isShared_2367_ = v_isSharedCheck_2375_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v_snd_2352_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2375_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v_a_2364_);
v___x_2369_ = v___x_2350_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2371_; 
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v___x_2369_);
v___x_2371_ = v___x_2366_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___redArg(v___x_2371_, v_a_2363_);
lean_dec_ref(v___x_2371_);
return v___x_2372_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
v_a_2377_ = lean_ctor_get(v___x_2336_, 0);
v_a_2378_ = lean_ctor_get(v___x_2336_, 1);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2336_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_inc(v_a_2377_);
lean_dec(v___x_2336_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2377_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed(lean_object* v_env_2386_, lean_object* v_stx_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(v_env_2386_, v_stx_2387_, v___y_2388_, v___y_2389_);
lean_dec_ref(v___y_2388_);
return v_res_2390_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14_spec__19___redArg(lean_object* v_keys_2391_, lean_object* v_i_2392_, lean_object* v_k_2393_){
_start:
{
lean_object* v___x_2394_; uint8_t v___x_2395_; 
v___x_2394_ = lean_array_get_size(v_keys_2391_);
v___x_2395_ = lean_nat_dec_lt(v_i_2392_, v___x_2394_);
if (v___x_2395_ == 0)
{
lean_dec(v_i_2392_);
return v___x_2395_;
}
else
{
lean_object* v_k_x27_2396_; uint8_t v___x_2397_; 
v_k_x27_2396_ = lean_array_fget_borrowed(v_keys_2391_, v_i_2392_);
v___x_2397_ = l_Lean_instBEqExtraModUse_beq(v_k_2393_, v_k_x27_2396_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = lean_unsigned_to_nat(1u);
v___x_2399_ = lean_nat_add(v_i_2392_, v___x_2398_);
lean_dec(v_i_2392_);
v_i_2392_ = v___x_2399_;
goto _start;
}
else
{
lean_dec(v_i_2392_);
return v___x_2397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14_spec__19___redArg___boxed(lean_object* v_keys_2401_, lean_object* v_i_2402_, lean_object* v_k_2403_){
_start:
{
uint8_t v_res_2404_; lean_object* v_r_2405_; 
v_res_2404_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14_spec__19___redArg(v_keys_2401_, v_i_2402_, v_k_2403_);
lean_dec_ref(v_k_2403_);
lean_dec_ref(v_keys_2401_);
v_r_2405_ = lean_box(v_res_2404_);
return v_r_2405_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14___redArg(lean_object* v_x_2406_, size_t v_x_2407_, lean_object* v_x_2408_){
_start:
{
if (lean_obj_tag(v_x_2406_) == 0)
{
lean_object* v_es_2409_; lean_object* v___x_2410_; size_t v___x_2411_; size_t v___x_2412_; size_t v___x_2413_; lean_object* v_j_2414_; lean_object* v___x_2415_; 
v_es_2409_ = lean_ctor_get(v_x_2406_, 0);
lean_inc_ref(v_es_2409_);
lean_dec_ref(v_x_2406_);
v___x_2410_ = lean_box(2);
v___x_2411_ = ((size_t)5ULL);
v___x_2412_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg___closed__1);
v___x_2413_ = lean_usize_land(v_x_2407_, v___x_2412_);
v_j_2414_ = lean_usize_to_nat(v___x_2413_);
v___x_2415_ = lean_array_get(v___x_2410_, v_es_2409_, v_j_2414_);
lean_dec(v_j_2414_);
lean_dec_ref(v_es_2409_);
switch(lean_obj_tag(v___x_2415_))
{
case 0:
{
lean_object* v_key_2416_; uint8_t v___x_2417_; 
v_key_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_key_2416_);
lean_dec_ref(v___x_2415_);
v___x_2417_ = l_Lean_instBEqExtraModUse_beq(v_x_2408_, v_key_2416_);
lean_dec(v_key_2416_);
return v___x_2417_;
}
case 1:
{
lean_object* v_node_2418_; size_t v___x_2419_; 
v_node_2418_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_node_2418_);
lean_dec_ref(v___x_2415_);
v___x_2419_ = lean_usize_shift_right(v_x_2407_, v___x_2411_);
v_x_2406_ = v_node_2418_;
v_x_2407_ = v___x_2419_;
goto _start;
}
default: 
{
uint8_t v___x_2421_; 
v___x_2421_ = 0;
return v___x_2421_;
}
}
}
else
{
lean_object* v_ks_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v_ks_2422_ = lean_ctor_get(v_x_2406_, 0);
lean_inc_ref(v_ks_2422_);
lean_dec_ref(v_x_2406_);
v___x_2423_ = lean_unsigned_to_nat(0u);
v___x_2424_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14_spec__19___redArg(v_ks_2422_, v___x_2423_, v_x_2408_);
lean_dec_ref(v_ks_2422_);
return v___x_2424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14___redArg___boxed(lean_object* v_x_2425_, lean_object* v_x_2426_, lean_object* v_x_2427_){
_start:
{
size_t v_x_21217__boxed_2428_; uint8_t v_res_2429_; lean_object* v_r_2430_; 
v_x_21217__boxed_2428_ = lean_unbox_usize(v_x_2426_);
lean_dec(v_x_2426_);
v_res_2429_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14___redArg(v_x_2425_, v_x_21217__boxed_2428_, v_x_2427_);
lean_dec_ref(v_x_2427_);
v_r_2430_ = lean_box(v_res_2429_);
return v_r_2430_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9___redArg(lean_object* v_x_2431_, lean_object* v_x_2432_){
_start:
{
uint64_t v___x_2433_; size_t v___x_2434_; uint8_t v___x_2435_; 
v___x_2433_ = l_Lean_instHashableExtraModUse_hash(v_x_2432_);
v___x_2434_ = lean_uint64_to_usize(v___x_2433_);
v___x_2435_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14___redArg(v_x_2431_, v___x_2434_, v_x_2432_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9___redArg___boxed(lean_object* v_x_2436_, lean_object* v_x_2437_){
_start:
{
uint8_t v_res_2438_; lean_object* v_r_2439_; 
v_res_2438_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9___redArg(v_x_2436_, v_x_2437_);
lean_dec_ref(v_x_2437_);
v_r_2439_ = lean_box(v_res_2438_);
return v_r_2439_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__2(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__1));
v___x_2443_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__0));
v___x_2444_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2443_, v___x_2442_);
return v___x_2444_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__3(void){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2445_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__4(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__3);
v___x_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
return v___x_2447_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__5(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__4);
v___x_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
return v___x_2449_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__6(void){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__4);
v___x_2451_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
lean_ctor_set(v___x_2451_, 2, v___x_2450_);
lean_ctor_set(v___x_2451_, 3, v___x_2450_);
lean_ctor_set(v___x_2451_, 4, v___x_2450_);
lean_ctor_set(v___x_2451_, 5, v___x_2450_);
return v___x_2451_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__10(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__9));
v___x_2457_ = l_Lean_stringToMessageData(v___x_2456_);
return v___x_2457_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__12(void){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__11));
v___x_2460_ = l_Lean_stringToMessageData(v___x_2459_);
return v___x_2460_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__13(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___closed__1));
v___x_2462_ = l_Lean_stringToMessageData(v___x_2461_);
return v___x_2462_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__15(void){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__14));
v___x_2465_ = l_Lean_stringToMessageData(v___x_2464_);
return v___x_2465_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__17(void){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__16));
v___x_2468_ = l_Lean_stringToMessageData(v___x_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6(lean_object* v_mod_2473_, uint8_t v_isMeta_2474_, lean_object* v_hint_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v___x_2485_; lean_object* v_env_2486_; uint8_t v_isExporting_2487_; lean_object* v___x_2488_; lean_object* v_env_2489_; lean_object* v___x_2490_; lean_object* v_entry_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2485_ = lean_st_ref_get(v___y_2483_);
v_env_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc_ref(v_env_2486_);
lean_dec(v___x_2485_);
v_isExporting_2487_ = lean_ctor_get_uint8(v_env_2486_, sizeof(void*)*8);
lean_dec_ref(v_env_2486_);
v___x_2488_ = lean_st_ref_get(v___y_2483_);
v_env_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc_ref(v_env_2489_);
lean_dec(v___x_2488_);
v___x_2490_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__2);
lean_inc(v_mod_2473_);
v_entry_2491_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2491_, 0, v_mod_2473_);
lean_ctor_set_uint8(v_entry_2491_, sizeof(void*)*1, v_isExporting_2487_);
lean_ctor_set_uint8(v_entry_2491_, sizeof(void*)*1 + 1, v_isMeta_2474_);
v___x_2492_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2493_ = lean_box(1);
v___x_2494_ = lean_box(0);
v___x_2537_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2490_, v___x_2492_, v_env_2489_, v___x_2493_, v___x_2494_);
v___x_2538_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9___redArg(v___x_2537_, v_entry_2491_);
if (v___x_2538_ == 0)
{
lean_object* v_cls_2539_; lean_object* v___x_2540_; lean_object* v_a_2541_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2548_; lean_object* v___y_2549_; uint8_t v___x_2561_; 
v_cls_2539_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__8));
v___x_2540_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_2539_, v___y_2482_);
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_a_2541_);
lean_dec_ref(v___x_2540_);
v___x_2561_ = lean_unbox(v_a_2541_);
lean_dec(v_a_2541_);
if (v___x_2561_ == 0)
{
lean_dec(v_hint_2475_);
lean_dec(v_mod_2473_);
v___y_2496_ = v___y_2481_;
v___y_2497_ = v___y_2483_;
goto v___jp_2495_;
}
else
{
lean_object* v___x_2562_; lean_object* v___y_2564_; 
v___x_2562_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__15);
if (v_isExporting_2487_ == 0)
{
lean_object* v___x_2571_; 
v___x_2571_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__20));
v___y_2564_ = v___x_2571_;
goto v___jp_2563_;
}
else
{
lean_object* v___x_2572_; 
v___x_2572_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__21));
v___y_2564_ = v___x_2572_;
goto v___jp_2563_;
}
v___jp_2563_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2565_ = l_Lean_stringToMessageData(v___y_2564_);
v___x_2566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2562_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__17);
v___x_2568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2566_);
lean_ctor_set(v___x_2568_, 1, v___x_2567_);
if (v_isMeta_2474_ == 0)
{
lean_object* v___x_2569_; 
v___x_2569_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__18));
v___y_2548_ = v___x_2568_;
v___y_2549_ = v___x_2569_;
goto v___jp_2547_;
}
else
{
lean_object* v___x_2570_; 
v___x_2570_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__19));
v___y_2548_ = v___x_2568_;
v___y_2549_ = v___x_2570_;
goto v___jp_2547_;
}
}
}
v___jp_2542_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___y_2543_);
lean_ctor_set(v___x_2545_, 1, v___y_2544_);
v___x_2546_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v_cls_2539_, v___x_2545_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_dec_ref(v___x_2546_);
v___y_2496_ = v___y_2481_;
v___y_2497_ = v___y_2483_;
goto v___jp_2495_;
}
else
{
lean_dec_ref(v_entry_2491_);
return v___x_2546_;
}
}
v___jp_2547_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
v___x_2550_ = l_Lean_stringToMessageData(v___y_2549_);
v___x_2551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___y_2548_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___x_2552_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__10);
v___x_2553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2551_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = l_Lean_MessageData_ofName(v_mod_2473_);
v___x_2555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2553_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
v___x_2556_ = l_Lean_Name_isAnonymous(v_hint_2475_);
if (v___x_2556_ == 0)
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2557_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__12);
v___x_2558_ = l_Lean_MessageData_ofName(v_hint_2475_);
v___x_2559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2557_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
v___y_2543_ = v___x_2555_;
v___y_2544_ = v___x_2559_;
goto v___jp_2542_;
}
else
{
lean_object* v___x_2560_; 
lean_dec(v_hint_2475_);
v___x_2560_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__13);
v___y_2543_ = v___x_2555_;
v___y_2544_ = v___x_2560_;
goto v___jp_2542_;
}
}
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
lean_dec_ref(v_entry_2491_);
lean_dec(v_hint_2475_);
lean_dec(v_mod_2473_);
v___x_2573_ = lean_box(0);
v___x_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
return v___x_2574_;
}
v___jp_2495_:
{
lean_object* v___x_2498_; lean_object* v_toEnvExtension_2499_; lean_object* v_env_2500_; lean_object* v_nextMacroScope_2501_; lean_object* v_ngen_2502_; lean_object* v_auxDeclNGen_2503_; lean_object* v_traceState_2504_; lean_object* v_messages_2505_; lean_object* v_infoState_2506_; lean_object* v_snapshotTasks_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2535_; 
v___x_2498_ = lean_st_ref_take(v___y_2497_);
v_toEnvExtension_2499_ = lean_ctor_get(v___x_2492_, 0);
lean_inc_ref(v_toEnvExtension_2499_);
v_env_2500_ = lean_ctor_get(v___x_2498_, 0);
v_nextMacroScope_2501_ = lean_ctor_get(v___x_2498_, 1);
v_ngen_2502_ = lean_ctor_get(v___x_2498_, 2);
v_auxDeclNGen_2503_ = lean_ctor_get(v___x_2498_, 3);
v_traceState_2504_ = lean_ctor_get(v___x_2498_, 4);
v_messages_2505_ = lean_ctor_get(v___x_2498_, 6);
v_infoState_2506_ = lean_ctor_get(v___x_2498_, 7);
v_snapshotTasks_2507_ = lean_ctor_get(v___x_2498_, 8);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2535_ == 0)
{
lean_object* v_unused_2536_; 
v_unused_2536_ = lean_ctor_get(v___x_2498_, 5);
lean_dec(v_unused_2536_);
v___x_2509_ = v___x_2498_;
v_isShared_2510_ = v_isSharedCheck_2535_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_snapshotTasks_2507_);
lean_inc(v_infoState_2506_);
lean_inc(v_messages_2505_);
lean_inc(v_traceState_2504_);
lean_inc(v_auxDeclNGen_2503_);
lean_inc(v_ngen_2502_);
lean_inc(v_nextMacroScope_2501_);
lean_inc(v_env_2500_);
lean_dec(v___x_2498_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2535_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v_asyncMode_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2515_; 
v_asyncMode_2511_ = lean_ctor_get(v_toEnvExtension_2499_, 2);
lean_inc(v_asyncMode_2511_);
lean_dec_ref(v_toEnvExtension_2499_);
v___x_2512_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2492_, v_env_2500_, v_entry_2491_, v_asyncMode_2511_, v___x_2494_);
lean_dec(v_asyncMode_2511_);
v___x_2513_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__5);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 5, v___x_2513_);
lean_ctor_set(v___x_2509_, 0, v___x_2512_);
v___x_2515_ = v___x_2509_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v_nextMacroScope_2501_);
lean_ctor_set(v_reuseFailAlloc_2534_, 2, v_ngen_2502_);
lean_ctor_set(v_reuseFailAlloc_2534_, 3, v_auxDeclNGen_2503_);
lean_ctor_set(v_reuseFailAlloc_2534_, 4, v_traceState_2504_);
lean_ctor_set(v_reuseFailAlloc_2534_, 5, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2534_, 6, v_messages_2505_);
lean_ctor_set(v_reuseFailAlloc_2534_, 7, v_infoState_2506_);
lean_ctor_set(v_reuseFailAlloc_2534_, 8, v_snapshotTasks_2507_);
v___x_2515_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v_mctx_2518_; lean_object* v_zetaDeltaFVarIds_2519_; lean_object* v_postponed_2520_; lean_object* v_diag_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2532_; 
v___x_2516_ = lean_st_ref_set(v___y_2497_, v___x_2515_);
v___x_2517_ = lean_st_ref_take(v___y_2496_);
v_mctx_2518_ = lean_ctor_get(v___x_2517_, 0);
v_zetaDeltaFVarIds_2519_ = lean_ctor_get(v___x_2517_, 2);
v_postponed_2520_ = lean_ctor_get(v___x_2517_, 3);
v_diag_2521_ = lean_ctor_get(v___x_2517_, 4);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; 
v_unused_2533_ = lean_ctor_get(v___x_2517_, 1);
lean_dec(v_unused_2533_);
v___x_2523_ = v___x_2517_;
v_isShared_2524_ = v_isSharedCheck_2532_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_diag_2521_);
lean_inc(v_postponed_2520_);
lean_inc(v_zetaDeltaFVarIds_2519_);
lean_inc(v_mctx_2518_);
lean_dec(v___x_2517_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2532_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; lean_object* v___x_2527_; 
v___x_2525_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___closed__6);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 1, v___x_2525_);
v___x_2527_ = v___x_2523_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_mctx_2518_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v___x_2525_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v_zetaDeltaFVarIds_2519_);
lean_ctor_set(v_reuseFailAlloc_2531_, 3, v_postponed_2520_);
lean_ctor_set(v_reuseFailAlloc_2531_, 4, v_diag_2521_);
v___x_2527_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = lean_st_ref_set(v___y_2496_, v___x_2527_);
v___x_2529_ = lean_box(0);
v___x_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
return v___x_2530_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6___boxed(lean_object* v_mod_2575_, lean_object* v_isMeta_2576_, lean_object* v_hint_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
uint8_t v_isMeta_boxed_2587_; lean_object* v_res_2588_; 
v_isMeta_boxed_2587_ = lean_unbox(v_isMeta_2576_);
v_res_2588_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6(v_mod_2575_, v_isMeta_boxed_2587_, v_hint_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__7(lean_object* v___x_2589_, lean_object* v_declName_2590_, lean_object* v_as_2591_, size_t v_sz_2592_, size_t v_i_2593_, lean_object* v_b_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
uint8_t v___x_2604_; 
v___x_2604_ = lean_usize_dec_lt(v_i_2593_, v_sz_2592_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; 
lean_dec(v_declName_2590_);
v___x_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2605_, 0, v_b_2594_);
return v___x_2605_;
}
else
{
lean_object* v___x_2606_; lean_object* v_modules_2607_; lean_object* v___x_2608_; lean_object* v_a_2609_; lean_object* v___x_2610_; lean_object* v_toImport_2611_; lean_object* v_module_2612_; uint8_t v___x_2613_; lean_object* v___x_2614_; 
v___x_2606_ = l_Lean_Environment_header(v___x_2589_);
v_modules_2607_ = lean_ctor_get(v___x_2606_, 3);
lean_inc_ref(v_modules_2607_);
lean_dec_ref(v___x_2606_);
v___x_2608_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2609_ = lean_array_uget_borrowed(v_as_2591_, v_i_2593_);
v___x_2610_ = lean_array_get(v___x_2608_, v_modules_2607_, v_a_2609_);
lean_dec_ref(v_modules_2607_);
v_toImport_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc_ref(v_toImport_2611_);
lean_dec(v___x_2610_);
v_module_2612_ = lean_ctor_get(v_toImport_2611_, 0);
lean_inc(v_module_2612_);
lean_dec_ref(v_toImport_2611_);
v___x_2613_ = 0;
lean_inc(v_declName_2590_);
v___x_2614_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6(v_module_2612_, v___x_2613_, v_declName_2590_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v___x_2615_; size_t v___x_2616_; size_t v___x_2617_; 
lean_dec_ref(v___x_2614_);
v___x_2615_ = lean_box(0);
v___x_2616_ = ((size_t)1ULL);
v___x_2617_ = lean_usize_add(v_i_2593_, v___x_2616_);
v_i_2593_ = v___x_2617_;
v_b_2594_ = v___x_2615_;
goto _start;
}
else
{
lean_dec(v_declName_2590_);
return v___x_2614_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__7___boxed(lean_object* v___x_2619_, lean_object* v_declName_2620_, lean_object* v_as_2621_, lean_object* v_sz_2622_, lean_object* v_i_2623_, lean_object* v_b_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
size_t v_sz_boxed_2634_; size_t v_i_boxed_2635_; lean_object* v_res_2636_; 
v_sz_boxed_2634_ = lean_unbox_usize(v_sz_2622_);
lean_dec(v_sz_2622_);
v_i_boxed_2635_ = lean_unbox_usize(v_i_2623_);
lean_dec(v_i_2623_);
v_res_2636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__7(v___x_2619_, v_declName_2620_, v_as_2621_, v_sz_boxed_2634_, v_i_boxed_2635_, v_b_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec_ref(v_as_2621_);
lean_dec_ref(v___x_2619_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8_spec__12___redArg(lean_object* v_a_2637_, lean_object* v_x_2638_){
_start:
{
if (lean_obj_tag(v_x_2638_) == 0)
{
lean_object* v___x_2639_; 
v___x_2639_ = lean_box(0);
return v___x_2639_;
}
else
{
lean_object* v_key_2640_; lean_object* v_value_2641_; lean_object* v_tail_2642_; uint8_t v___x_2643_; 
v_key_2640_ = lean_ctor_get(v_x_2638_, 0);
v_value_2641_ = lean_ctor_get(v_x_2638_, 1);
v_tail_2642_ = lean_ctor_get(v_x_2638_, 2);
v___x_2643_ = lean_name_eq(v_key_2640_, v_a_2637_);
if (v___x_2643_ == 0)
{
v_x_2638_ = v_tail_2642_;
goto _start;
}
else
{
lean_object* v___x_2645_; 
lean_inc(v_value_2641_);
v___x_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2645_, 0, v_value_2641_);
return v___x_2645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_a_2646_, lean_object* v_x_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8_spec__12___redArg(v_a_2646_, v_x_2647_);
lean_dec(v_x_2647_);
lean_dec(v_a_2646_);
return v_res_2648_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2649_; uint64_t v___x_2650_; 
v___x_2649_ = lean_unsigned_to_nat(1723u);
v___x_2650_ = lean_uint64_of_nat(v___x_2649_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8___redArg(lean_object* v_m_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v_buckets_2653_; lean_object* v___x_2654_; uint64_t v___y_2656_; 
v_buckets_2653_ = lean_ctor_get(v_m_2651_, 1);
v___x_2654_ = lean_array_get_size(v_buckets_2653_);
if (lean_obj_tag(v_a_2652_) == 0)
{
uint64_t v___x_2670_; 
v___x_2670_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8___redArg___closed__0);
v___y_2656_ = v___x_2670_;
goto v___jp_2655_;
}
else
{
uint64_t v_hash_2671_; 
v_hash_2671_ = lean_ctor_get_uint64(v_a_2652_, sizeof(void*)*2);
v___y_2656_ = v_hash_2671_;
goto v___jp_2655_;
}
v___jp_2655_:
{
uint64_t v___x_2657_; uint64_t v___x_2658_; uint64_t v_fold_2659_; uint64_t v___x_2660_; uint64_t v___x_2661_; uint64_t v___x_2662_; size_t v___x_2663_; size_t v___x_2664_; size_t v___x_2665_; size_t v___x_2666_; size_t v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2657_ = 32ULL;
v___x_2658_ = lean_uint64_shift_right(v___y_2656_, v___x_2657_);
v_fold_2659_ = lean_uint64_xor(v___y_2656_, v___x_2658_);
v___x_2660_ = 16ULL;
v___x_2661_ = lean_uint64_shift_right(v_fold_2659_, v___x_2660_);
v___x_2662_ = lean_uint64_xor(v_fold_2659_, v___x_2661_);
v___x_2663_ = lean_uint64_to_usize(v___x_2662_);
v___x_2664_ = lean_usize_of_nat(v___x_2654_);
v___x_2665_ = ((size_t)1ULL);
v___x_2666_ = lean_usize_sub(v___x_2664_, v___x_2665_);
v___x_2667_ = lean_usize_land(v___x_2663_, v___x_2666_);
v___x_2668_ = lean_array_uget_borrowed(v_buckets_2653_, v___x_2667_);
v___x_2669_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8_spec__12___redArg(v_a_2652_, v___x_2668_);
return v___x_2669_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_m_2672_, lean_object* v_a_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8___redArg(v_m_2672_, v_a_2673_);
lean_dec(v_a_2673_);
lean_dec_ref(v_m_2672_);
return v_res_2674_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2677_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___closed__1));
v___x_2678_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___closed__0));
v___x_2679_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2678_, v___x_2677_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(lean_object* v_declName_2682_, uint8_t v_isMeta_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v___x_2693_; lean_object* v_env_2697_; lean_object* v___y_2699_; lean_object* v___x_2712_; 
v___x_2693_ = lean_st_ref_get(v___y_2691_);
v_env_2697_ = lean_ctor_get(v___x_2693_, 0);
lean_inc_ref(v_env_2697_);
lean_dec(v___x_2693_);
v___x_2712_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2697_, v_declName_2682_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_dec_ref(v_env_2697_);
lean_dec(v_declName_2682_);
goto v___jp_2694_;
}
else
{
lean_object* v_val_2713_; lean_object* v___x_2714_; lean_object* v_modules_2715_; lean_object* v___x_2716_; uint8_t v___x_2717_; 
v_val_2713_ = lean_ctor_get(v___x_2712_, 0);
lean_inc(v_val_2713_);
lean_dec_ref(v___x_2712_);
v___x_2714_ = l_Lean_Environment_header(v_env_2697_);
v_modules_2715_ = lean_ctor_get(v___x_2714_, 3);
lean_inc_ref(v_modules_2715_);
lean_dec_ref(v___x_2714_);
v___x_2716_ = lean_array_get_size(v_modules_2715_);
v___x_2717_ = lean_nat_dec_lt(v_val_2713_, v___x_2716_);
if (v___x_2717_ == 0)
{
lean_dec_ref(v_modules_2715_);
lean_dec(v_val_2713_);
lean_dec_ref(v_env_2697_);
lean_dec(v_declName_2682_);
goto v___jp_2694_;
}
else
{
lean_object* v___x_2718_; lean_object* v_env_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; uint8_t v___y_2723_; 
v___x_2718_ = lean_st_ref_get(v___y_2691_);
v_env_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc_ref(v_env_2719_);
lean_dec(v___x_2718_);
v___x_2720_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___closed__2);
v___x_2721_ = lean_array_fget(v_modules_2715_, v_val_2713_);
lean_dec(v_val_2713_);
lean_dec_ref(v_modules_2715_);
if (v_isMeta_2683_ == 0)
{
lean_dec_ref(v_env_2719_);
v___y_2723_ = v_isMeta_2683_;
goto v___jp_2722_;
}
else
{
uint8_t v___x_2734_; 
lean_inc(v_declName_2682_);
v___x_2734_ = l_Lean_isMarkedMeta(v_env_2719_, v_declName_2682_);
if (v___x_2734_ == 0)
{
v___y_2723_ = v_isMeta_2683_;
goto v___jp_2722_;
}
else
{
uint8_t v___x_2735_; 
v___x_2735_ = 0;
v___y_2723_ = v___x_2735_;
goto v___jp_2722_;
}
}
v___jp_2722_:
{
lean_object* v_toImport_2724_; lean_object* v_module_2725_; lean_object* v___x_2726_; 
v_toImport_2724_ = lean_ctor_get(v___x_2721_, 0);
lean_inc_ref(v_toImport_2724_);
lean_dec(v___x_2721_);
v_module_2725_ = lean_ctor_get(v_toImport_2724_, 0);
lean_inc(v_module_2725_);
lean_dec_ref(v_toImport_2724_);
lean_inc(v_declName_2682_);
v___x_2726_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6(v_module_2725_, v___y_2723_, v_declName_2682_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
lean_dec_ref(v___x_2726_);
v___x_2727_ = l_Lean_indirectModUseExt;
v___x_2728_ = lean_box(1);
v___x_2729_ = lean_box(0);
lean_inc_ref(v_env_2697_);
v___x_2730_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2720_, v___x_2727_, v_env_2697_, v___x_2728_, v___x_2729_);
v___x_2731_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8___redArg(v___x_2730_, v_declName_2682_);
lean_dec(v___x_2730_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v___x_2732_; 
v___x_2732_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___closed__3));
v___y_2699_ = v___x_2732_;
goto v___jp_2698_;
}
else
{
lean_object* v_val_2733_; 
v_val_2733_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_val_2733_);
lean_dec_ref(v___x_2731_);
v___y_2699_ = v_val_2733_;
goto v___jp_2698_;
}
}
else
{
lean_dec_ref(v_env_2697_);
lean_dec(v_declName_2682_);
return v___x_2726_;
}
}
}
}
v___jp_2694_:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2695_ = lean_box(0);
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
return v___x_2696_;
}
v___jp_2698_:
{
lean_object* v___x_2700_; size_t v_sz_2701_; size_t v___x_2702_; lean_object* v___x_2703_; 
v___x_2700_ = lean_box(0);
v_sz_2701_ = lean_array_size(v___y_2699_);
v___x_2702_ = ((size_t)0ULL);
v___x_2703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__7(v_env_2697_, v_declName_2682_, v___y_2699_, v_sz_2701_, v___x_2702_, v___x_2700_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
lean_dec_ref(v___y_2699_);
lean_dec_ref(v_env_2697_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2710_ == 0)
{
lean_object* v_unused_2711_; 
v_unused_2711_ = lean_ctor_get(v___x_2703_, 0);
lean_dec(v_unused_2711_);
v___x_2705_ = v___x_2703_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_dec(v___x_2703_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 0, v___x_2700_);
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2700_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
else
{
return v___x_2703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___boxed(lean_object* v_declName_2736_, lean_object* v_isMeta_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
uint8_t v_isMeta_boxed_2747_; lean_object* v_res_2748_; 
v_isMeta_boxed_2747_ = lean_unbox(v_isMeta_2737_);
v_res_2748_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(v_declName_2736_, v_isMeta_boxed_2747_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___redArg(lean_object* v_as_x27_2749_, lean_object* v_b_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
if (lean_obj_tag(v_as_x27_2749_) == 0)
{
lean_object* v___x_2760_; 
v___x_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2760_, 0, v_b_2750_);
return v___x_2760_;
}
else
{
lean_object* v_head_2761_; lean_object* v_tail_2762_; uint8_t v___x_2763_; lean_object* v___x_2764_; 
v_head_2761_ = lean_ctor_get(v_as_x27_2749_, 0);
lean_inc(v_head_2761_);
v_tail_2762_ = lean_ctor_get(v_as_x27_2749_, 1);
lean_inc(v_tail_2762_);
lean_dec_ref(v_as_x27_2749_);
v___x_2763_ = 1;
v___x_2764_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(v_head_2761_, v___x_2763_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v___x_2765_; 
lean_dec_ref(v___x_2764_);
v___x_2765_ = lean_box(0);
v_as_x27_2749_ = v_tail_2762_;
v_b_2750_ = v___x_2765_;
goto _start;
}
else
{
lean_dec(v_tail_2762_);
return v___x_2764_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___redArg___boxed(lean_object* v_as_x27_2767_, lean_object* v_b_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___redArg(v_as_x27_2767_, v_b_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(lean_object* v_env_2779_, lean_object* v_options_2780_, lean_object* v_currNamespace_2781_, lean_object* v_openDecls_2782_, lean_object* v_n_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = l_Lean_ResolveName_resolveGlobalName(v_env_2779_, v_options_2780_, v_currNamespace_2781_, v_openDecls_2782_, v_n_2783_);
v___x_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
lean_ctor_set(v___x_2787_, 1, v___y_2785_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed(lean_object* v_env_2788_, lean_object* v_options_2789_, lean_object* v_currNamespace_2790_, lean_object* v_openDecls_2791_, lean_object* v_n_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(v_env_2788_, v_options_2789_, v_currNamespace_2790_, v_openDecls_2791_, v_n_2792_, v___y_2793_, v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec_ref(v_options_2789_);
return v_res_2795_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = l_Lean_maxRecDepthErrorMessage;
v___x_2802_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
return v___x_2802_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__3);
v___x_2804_ = l_Lean_MessageData_ofFormat(v___x_2803_);
return v___x_2804_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2805_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__4);
v___x_2806_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__2));
v___x_2807_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
lean_ctor_set(v___x_2807_, 1, v___x_2805_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg(lean_object* v_ref_2808_){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2810_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___closed__5);
v___x_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2811_, 0, v_ref_2808_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
v___x_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg___boxed(lean_object* v_ref_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg(v_ref_2813_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(lean_object* v_currNamespace_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2819_, 0, v_currNamespace_2816_);
lean_ctor_set(v___x_2819_, 1, v___y_2818_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed(lean_object* v_currNamespace_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(v_currNamespace_2820_, v___y_2821_, v___y_2822_);
lean_dec_ref(v___y_2821_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(lean_object* v_env_2824_, lean_object* v_currNamespace_2825_, lean_object* v_openDecls_2826_, lean_object* v_n_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = l_Lean_ResolveName_resolveNamespace(v_env_2824_, v_currNamespace_2825_, v_openDecls_2826_, v_n_2827_);
v___x_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
lean_ctor_set(v___x_2831_, 1, v___y_2829_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed(lean_object* v_env_2832_, lean_object* v_currNamespace_2833_, lean_object* v_openDecls_2834_, lean_object* v_n_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(v_env_2832_, v_currNamespace_2833_, v_openDecls_2834_, v_n_2835_, v___y_2836_, v___y_2837_);
lean_dec_ref(v___y_2836_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1(lean_object* v_env_2839_, lean_object* v_declName_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
uint8_t v___x_2843_; lean_object* v_env_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; uint8_t v___x_2847_; 
v___x_2843_ = 0;
v_env_2844_ = l_Lean_Environment_setExporting(v_env_2839_, v___x_2843_);
lean_inc(v_declName_2840_);
v___x_2845_ = l_Lean_mkPrivateName(v_env_2844_, v_declName_2840_);
v___x_2846_ = 1;
lean_inc_ref(v_env_2844_);
v___x_2847_ = l_Lean_Environment_contains(v_env_2844_, v___x_2845_, v___x_2846_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; uint8_t v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2848_ = l_Lean_privateToUserName(v_declName_2840_);
v___x_2849_ = l_Lean_Environment_contains(v_env_2844_, v___x_2848_, v___x_2846_);
v___x_2850_ = lean_box(v___x_2849_);
v___x_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
lean_ctor_set(v___x_2851_, 1, v___y_2842_);
return v___x_2851_;
}
else
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_dec_ref(v_env_2844_);
lean_dec(v_declName_2840_);
v___x_2852_ = lean_box(v___x_2847_);
v___x_2853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
lean_ctor_set(v___x_2853_, 1, v___y_2842_);
return v___x_2853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1___boxed(lean_object* v_env_2854_, lean_object* v_declName_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1(v_env_2854_, v_declName_2855_, v___y_2856_, v___y_2857_);
lean_dec_ref(v___y_2856_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(lean_object* v_x_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v___x_2870_; lean_object* v_env_2871_; lean_object* v_options_2872_; lean_object* v_currRecDepth_2873_; lean_object* v_maxRecDepth_2874_; lean_object* v_ref_2875_; lean_object* v_currNamespace_2876_; lean_object* v_openDecls_2877_; lean_object* v_quotContext_2878_; lean_object* v_currMacroScope_2879_; lean_object* v___x_2880_; lean_object* v_nextMacroScope_2881_; lean_object* v___f_2882_; lean_object* v___f_2883_; lean_object* v___f_2884_; lean_object* v___f_2885_; lean_object* v___f_2886_; lean_object* v_methods_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2870_ = lean_st_ref_get(v___y_2868_);
v_env_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc_ref(v_env_2871_);
lean_dec(v___x_2870_);
v_options_2872_ = lean_ctor_get(v___y_2867_, 2);
v_currRecDepth_2873_ = lean_ctor_get(v___y_2867_, 3);
v_maxRecDepth_2874_ = lean_ctor_get(v___y_2867_, 4);
v_ref_2875_ = lean_ctor_get(v___y_2867_, 5);
v_currNamespace_2876_ = lean_ctor_get(v___y_2867_, 6);
v_openDecls_2877_ = lean_ctor_get(v___y_2867_, 7);
v_quotContext_2878_ = lean_ctor_get(v___y_2867_, 10);
v_currMacroScope_2879_ = lean_ctor_get(v___y_2867_, 11);
v___x_2880_ = lean_st_ref_get(v___y_2868_);
v_nextMacroScope_2881_ = lean_ctor_get(v___x_2880_, 1);
lean_inc(v_nextMacroScope_2881_);
lean_dec(v___x_2880_);
lean_inc_ref(v_env_2871_);
v___f_2882_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2882_, 0, v_env_2871_);
lean_inc_ref(v_env_2871_);
v___f_2883_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2883_, 0, v_env_2871_);
lean_inc(v_openDecls_2877_);
lean_inc(v_currNamespace_2876_);
lean_inc_ref(v_env_2871_);
v___f_2884_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_2884_, 0, v_env_2871_);
lean_closure_set(v___f_2884_, 1, v_currNamespace_2876_);
lean_closure_set(v___f_2884_, 2, v_openDecls_2877_);
lean_inc(v_currNamespace_2876_);
v___f_2885_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2885_, 0, v_currNamespace_2876_);
lean_inc(v_openDecls_2877_);
lean_inc(v_currNamespace_2876_);
lean_inc_ref(v_options_2872_);
v___f_2886_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2886_, 0, v_env_2871_);
lean_closure_set(v___f_2886_, 1, v_options_2872_);
lean_closure_set(v___f_2886_, 2, v_currNamespace_2876_);
lean_closure_set(v___f_2886_, 3, v_openDecls_2877_);
v_methods_2887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2887_, 0, v___f_2882_);
lean_ctor_set(v_methods_2887_, 1, v___f_2885_);
lean_ctor_set(v_methods_2887_, 2, v___f_2883_);
lean_ctor_set(v_methods_2887_, 3, v___f_2884_);
lean_ctor_set(v_methods_2887_, 4, v___f_2886_);
lean_inc(v_ref_2875_);
lean_inc(v_maxRecDepth_2874_);
lean_inc(v_currRecDepth_2873_);
lean_inc(v_currMacroScope_2879_);
lean_inc(v_quotContext_2878_);
v___x_2888_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2888_, 0, v_methods_2887_);
lean_ctor_set(v___x_2888_, 1, v_quotContext_2878_);
lean_ctor_set(v___x_2888_, 2, v_currMacroScope_2879_);
lean_ctor_set(v___x_2888_, 3, v_currRecDepth_2873_);
lean_ctor_set(v___x_2888_, 4, v_maxRecDepth_2874_);
lean_ctor_set(v___x_2888_, 5, v_ref_2875_);
v___x_2889_ = lean_box(0);
v___x_2890_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2890_, 0, v_nextMacroScope_2881_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
lean_ctor_set(v___x_2890_, 2, v___x_2889_);
v___x_2891_ = lean_apply_2(v_x_2860_, v___x_2888_, v___x_2890_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v_a_2893_; lean_object* v_macroScope_2894_; lean_object* v_traceMsgs_2895_; lean_object* v_expandedMacroDecls_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 1);
lean_inc(v_a_2892_);
v_a_2893_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2893_);
lean_dec_ref(v___x_2891_);
v_macroScope_2894_ = lean_ctor_get(v_a_2892_, 0);
lean_inc(v_macroScope_2894_);
v_traceMsgs_2895_ = lean_ctor_get(v_a_2892_, 1);
lean_inc(v_traceMsgs_2895_);
v_expandedMacroDecls_2896_ = lean_ctor_get(v_a_2892_, 2);
lean_inc(v_expandedMacroDecls_2896_);
lean_dec(v_a_2892_);
v___x_2897_ = lean_box(0);
v___x_2898_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___redArg(v_expandedMacroDecls_2896_, v___x_2897_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v___x_2899_; lean_object* v_env_2900_; lean_object* v_ngen_2901_; lean_object* v_auxDeclNGen_2902_; lean_object* v_traceState_2903_; lean_object* v_cache_2904_; lean_object* v_messages_2905_; lean_object* v_infoState_2906_; lean_object* v_snapshotTasks_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2933_; 
lean_dec_ref(v___x_2898_);
v___x_2899_ = lean_st_ref_take(v___y_2868_);
v_env_2900_ = lean_ctor_get(v___x_2899_, 0);
v_ngen_2901_ = lean_ctor_get(v___x_2899_, 2);
v_auxDeclNGen_2902_ = lean_ctor_get(v___x_2899_, 3);
v_traceState_2903_ = lean_ctor_get(v___x_2899_, 4);
v_cache_2904_ = lean_ctor_get(v___x_2899_, 5);
v_messages_2905_ = lean_ctor_get(v___x_2899_, 6);
v_infoState_2906_ = lean_ctor_get(v___x_2899_, 7);
v_snapshotTasks_2907_ = lean_ctor_get(v___x_2899_, 8);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2933_ == 0)
{
lean_object* v_unused_2934_; 
v_unused_2934_ = lean_ctor_get(v___x_2899_, 1);
lean_dec(v_unused_2934_);
v___x_2909_ = v___x_2899_;
v_isShared_2910_ = v_isSharedCheck_2933_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_snapshotTasks_2907_);
lean_inc(v_infoState_2906_);
lean_inc(v_messages_2905_);
lean_inc(v_cache_2904_);
lean_inc(v_traceState_2903_);
lean_inc(v_auxDeclNGen_2902_);
lean_inc(v_ngen_2901_);
lean_inc(v_env_2900_);
lean_dec(v___x_2899_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2933_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 1, v_macroScope_2894_);
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_env_2900_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v_macroScope_2894_);
lean_ctor_set(v_reuseFailAlloc_2932_, 2, v_ngen_2901_);
lean_ctor_set(v_reuseFailAlloc_2932_, 3, v_auxDeclNGen_2902_);
lean_ctor_set(v_reuseFailAlloc_2932_, 4, v_traceState_2903_);
lean_ctor_set(v_reuseFailAlloc_2932_, 5, v_cache_2904_);
lean_ctor_set(v_reuseFailAlloc_2932_, 6, v_messages_2905_);
lean_ctor_set(v_reuseFailAlloc_2932_, 7, v_infoState_2906_);
lean_ctor_set(v_reuseFailAlloc_2932_, 8, v_snapshotTasks_2907_);
v___x_2912_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2913_ = lean_st_ref_set(v___y_2868_, v___x_2912_);
v___x_2914_ = l_List_reverse___redArg(v_traceMsgs_2895_);
v___x_2915_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(v___x_2914_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
lean_dec_ref(v___y_2867_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2922_ == 0)
{
lean_object* v_unused_2923_; 
v_unused_2923_ = lean_ctor_get(v___x_2915_, 0);
lean_dec(v_unused_2923_);
v___x_2917_ = v___x_2915_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_dec(v___x_2915_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 0, v_a_2893_);
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2893_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
lean_dec(v_a_2893_);
v_a_2924_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2915_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2915_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
}
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_dec(v_traceMsgs_2895_);
lean_dec(v_macroScope_2894_);
lean_dec(v_a_2893_);
lean_dec_ref(v___y_2867_);
v_a_2935_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2898_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2898_);
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
lean_object* v_a_2943_; 
v_a_2943_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2943_);
lean_dec_ref(v___x_2891_);
if (lean_obj_tag(v_a_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v_a_2945_; lean_object* v___x_2946_; uint8_t v___x_2947_; 
v_a_2944_ = lean_ctor_get(v_a_2943_, 0);
lean_inc(v_a_2944_);
v_a_2945_ = lean_ctor_get(v_a_2943_, 1);
lean_inc_ref(v_a_2945_);
lean_dec_ref(v_a_2943_);
v___x_2946_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0));
v___x_2947_ = lean_string_dec_eq(v_a_2945_, v___x_2946_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2948_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2948_, 0, v_a_2945_);
v___x_2949_ = l_Lean_MessageData_ofFormat(v___x_2948_);
v___x_2950_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_a_2944_, v___x_2949_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
lean_dec(v_a_2944_);
return v___x_2950_;
}
else
{
lean_object* v___x_2951_; 
lean_dec_ref(v_a_2945_);
lean_dec_ref(v___y_2867_);
v___x_2951_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg(v_a_2944_);
return v___x_2951_;
}
}
else
{
lean_object* v___x_2952_; 
lean_dec_ref(v___y_2867_);
v___x_2952_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_2952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___boxed(lean_object* v_x_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v_x_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
lean_dec(v___y_2961_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(lean_object* v_x_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v___x_2984_; uint8_t v___x_2985_; 
v___x_2984_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2));
lean_inc(v_x_2974_);
v___x_2985_ = l_Lean_Syntax_isOfKind(v_x_2974_, v___x_2984_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; 
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec(v_a_2980_);
lean_dec_ref(v_a_2979_);
lean_dec(v_a_2978_);
lean_dec_ref(v_a_2977_);
lean_dec(v_a_2976_);
lean_dec_ref(v_a_2975_);
lean_dec(v_x_2974_);
v___x_2986_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_2986_;
}
else
{
lean_object* v___x_2987_; lean_object* v_hyp_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; 
v___x_2987_ = lean_unsigned_to_nat(1u);
v_hyp_2988_ = l_Lean_Syntax_getArg(v_x_2974_, v___x_2987_);
v___x_2989_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4));
lean_inc(v_hyp_2988_);
v___x_2990_ = l_Lean_Syntax_isOfKind(v_hyp_2988_, v___x_2989_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; 
lean_dec(v_hyp_2988_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec(v_a_2980_);
lean_dec_ref(v_a_2979_);
lean_dec(v_a_2978_);
lean_dec_ref(v_a_2977_);
lean_dec(v_a_2976_);
lean_dec_ref(v_a_2975_);
lean_dec(v_x_2974_);
v___x_2991_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_2991_;
}
else
{
lean_object* v___x_2992_; lean_object* v_pat_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2992_ = lean_unsigned_to_nat(3u);
v_pat_2993_ = l_Lean_Syntax_getArg(v_x_2974_, v___x_2992_);
lean_dec(v_x_2974_);
v___x_2994_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_MCasesPat_parse), 3, 1);
lean_closure_set(v___x_2994_, 0, v_pat_2993_);
lean_inc_ref(v_a_2981_);
v___x_2995_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v___x_2994_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2997_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref(v___x_2995_);
lean_inc(v_a_2982_);
lean_inc_ref(v_a_2981_);
lean_inc(v_a_2980_);
lean_inc_ref(v_a_2979_);
v___x_2997_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_2976_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v_fst_2999_; lean_object* v_snd_3000_; lean_object* v___f_3001_; lean_object* v___x_3002_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref(v___x_2997_);
v_fst_2999_ = lean_ctor_get(v_a_2998_, 0);
lean_inc(v_fst_2999_);
v_snd_3000_ = lean_ctor_get(v_a_2998_, 1);
lean_inc(v_snd_3000_);
lean_dec(v_a_2998_);
lean_inc(v_fst_2999_);
v___f_3001_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___boxed), 13, 4);
lean_closure_set(v___f_3001_, 0, v_snd_3000_);
lean_closure_set(v___f_3001_, 1, v_hyp_2988_);
lean_closure_set(v___f_3001_, 2, v_a_2996_);
lean_closure_set(v___f_3001_, 3, v_fst_2999_);
v___x_3002_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_fst_2999_, v___f_3001_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_);
return v___x_3002_;
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec(v_a_2996_);
lean_dec(v_hyp_2988_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec(v_a_2980_);
lean_dec_ref(v_a_2979_);
lean_dec(v_a_2978_);
lean_dec_ref(v_a_2977_);
lean_dec(v_a_2976_);
lean_dec_ref(v_a_2975_);
v_a_3003_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2997_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2997_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_dec(v_hyp_2988_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec(v_a_2980_);
lean_dec_ref(v_a_2979_);
lean_dec(v_a_2978_);
lean_dec_ref(v_a_2977_);
lean_dec(v_a_2976_);
lean_dec_ref(v_a_2975_);
v_a_3011_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_2995_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_2995_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___boxed(lean_object* v_x_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(v_x_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(lean_object* v_cls_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_3030_, v___y_3037_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___boxed(lean_object* v_cls_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(v_cls_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(lean_object* v_00_u03b1_3052_, lean_object* v_x_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___redArg(v_x_3053_, v___y_3055_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3057_, lean_object* v_x_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(v_00_u03b1_3057_, v_x_3058_, v___y_3059_, v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec_ref(v_x_3058_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8(lean_object* v_00_u03b1_3062_, lean_object* v_ref_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___redArg(v_ref_3063_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8___boxed(lean_object* v_00_u03b1_3074_, lean_object* v_ref_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__8(v_00_u03b1_3074_, v_ref_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(lean_object* v_00_u03b1_3086_, lean_object* v_x_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v___x_3097_; 
v___x_3097_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v_x_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___boxed(lean_object* v_00_u03b1_3098_, lean_object* v_x_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(v_00_u03b1_3098_, v_x_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
lean_dec(v___y_3107_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(lean_object* v_mvarId_3110_, lean_object* v_val_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_mvarId_3110_, v_val_3111_, v___y_3117_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___boxed(lean_object* v_mvarId_3122_, lean_object* v_val_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(v_mvarId_3122_, v_val_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(lean_object* v_cls_3134_, lean_object* v_msg_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v_cls_3134_, v_msg_3135_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___boxed(lean_object* v_cls_3146_, lean_object* v_msg_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(v_cls_3146_, v_msg_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(lean_object* v_as_3158_, lean_object* v_as_x27_3159_, lean_object* v_b_3160_, lean_object* v_a_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v___x_3171_; 
v___x_3171_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___redArg(v_as_x27_3159_, v_b_3160_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___boxed(lean_object* v_as_3172_, lean_object* v_as_x27_3173_, lean_object* v_b_3174_, lean_object* v_a_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(v_as_3172_, v_as_x27_3173_, v_b_3174_, v_a_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v_as_3172_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(lean_object* v_00_u03b1_3186_, lean_object* v_ref_3187_, lean_object* v_msg_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v___x_3198_; 
v___x_3198_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_ref_3187_, v_msg_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3199_, lean_object* v_ref_3200_, lean_object* v_msg_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(v_00_u03b1_3199_, v_ref_3200_, v_msg_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v_ref_3200_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10(lean_object* v_00_u03b2_3212_, lean_object* v_x_3213_, lean_object* v_x_3214_, lean_object* v_x_3215_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10___redArg(v_x_3213_, v_x_3214_, v_x_3215_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_3217_, lean_object* v_m_3218_, lean_object* v_a_3219_){
_start:
{
lean_object* v___x_3220_; 
v___x_3220_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8___redArg(v_m_3218_, v_a_3219_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_3221_, lean_object* v_m_3222_, lean_object* v_a_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8(v_00_u03b2_3221_, v_m_3222_, v_a_3223_);
lean_dec(v_a_3223_);
lean_dec_ref(v_m_3222_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7_spec__12(lean_object* v_00_u03b1_3225_, lean_object* v_msg_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7_spec__12___redArg(v_msg_3226_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7_spec__12___boxed(lean_object* v_00_u03b1_3237_, lean_object* v_msg_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7_spec__12(v_00_u03b1_3237_, v_msg_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16(lean_object* v_00_u03b2_3249_, lean_object* v_x_3250_, size_t v_x_3251_, size_t v_x_3252_, lean_object* v_x_3253_, lean_object* v_x_3254_){
_start:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___redArg(v_x_3250_, v_x_3251_, v_x_3252_, v_x_3253_, v_x_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16___boxed(lean_object* v_00_u03b2_3256_, lean_object* v_x_3257_, lean_object* v_x_3258_, lean_object* v_x_3259_, lean_object* v_x_3260_, lean_object* v_x_3261_){
_start:
{
size_t v_x_22476__boxed_3262_; size_t v_x_22477__boxed_3263_; lean_object* v_res_3264_; 
v_x_22476__boxed_3262_ = lean_unbox_usize(v_x_3258_);
lean_dec(v_x_3258_);
v_x_22477__boxed_3263_ = lean_unbox_usize(v_x_3259_);
lean_dec(v_x_3259_);
v_res_3264_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16(v_00_u03b2_3256_, v_x_3257_, v_x_22476__boxed_3262_, v_x_22477__boxed_3263_, v_x_3260_, v_x_3261_);
return v_res_3264_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_3265_, lean_object* v_x_3266_, lean_object* v_x_3267_){
_start:
{
uint8_t v___x_3268_; 
v___x_3268_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9___redArg(v_x_3266_, v_x_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9___boxed(lean_object* v_00_u03b2_3269_, lean_object* v_x_3270_, lean_object* v_x_3271_){
_start:
{
uint8_t v_res_3272_; lean_object* v_r_3273_; 
v_res_3272_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9(v_00_u03b2_3269_, v_x_3270_, v_x_3271_);
lean_dec_ref(v_x_3271_);
v_r_3273_ = lean_box(v_res_3272_);
return v_r_3273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_3274_, lean_object* v_a_3275_, lean_object* v_x_3276_){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8_spec__12___redArg(v_a_3275_, v_x_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_3278_, lean_object* v_a_3279_, lean_object* v_x_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__8_spec__12(v_00_u03b2_3278_, v_a_3279_, v_x_3280_);
lean_dec(v_x_3280_);
lean_dec(v_a_3279_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__19(lean_object* v_00_u03b2_3282_, lean_object* v_n_3283_, lean_object* v_k_3284_, lean_object* v_v_3285_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__19___redArg(v_n_3283_, v_k_3284_, v_v_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__20(lean_object* v_00_u03b2_3287_, size_t v_depth_3288_, lean_object* v_keys_3289_, lean_object* v_vals_3290_, lean_object* v_heq_3291_, lean_object* v_i_3292_, lean_object* v_entries_3293_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__20___redArg(v_depth_3288_, v_keys_3289_, v_vals_3290_, v_i_3292_, v_entries_3293_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__20___boxed(lean_object* v_00_u03b2_3295_, lean_object* v_depth_3296_, lean_object* v_keys_3297_, lean_object* v_vals_3298_, lean_object* v_heq_3299_, lean_object* v_i_3300_, lean_object* v_entries_3301_){
_start:
{
size_t v_depth_boxed_3302_; lean_object* v_res_3303_; 
v_depth_boxed_3302_ = lean_unbox_usize(v_depth_3296_);
lean_dec(v_depth_3296_);
v_res_3303_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__20(v_00_u03b2_3295_, v_depth_boxed_3302_, v_keys_3297_, v_vals_3298_, v_heq_3299_, v_i_3300_, v_entries_3301_);
lean_dec_ref(v_vals_3298_);
lean_dec_ref(v_keys_3297_);
return v_res_3303_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14(lean_object* v_00_u03b2_3304_, lean_object* v_x_3305_, size_t v_x_3306_, lean_object* v_x_3307_){
_start:
{
uint8_t v___x_3308_; 
v___x_3308_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14___redArg(v_x_3305_, v_x_3306_, v_x_3307_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14___boxed(lean_object* v_00_u03b2_3309_, lean_object* v_x_3310_, lean_object* v_x_3311_, lean_object* v_x_3312_){
_start:
{
size_t v_x_22510__boxed_3313_; uint8_t v_res_3314_; lean_object* v_r_3315_; 
v_x_22510__boxed_3313_ = lean_unbox_usize(v_x_3311_);
lean_dec(v_x_3311_);
v_res_3314_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14(v_00_u03b2_3309_, v_x_3310_, v_x_22510__boxed_3313_, v_x_3312_);
lean_dec_ref(v_x_3312_);
v_r_3315_ = lean_box(v_res_3314_);
return v_r_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__19_spec__21(lean_object* v_00_u03b2_3316_, lean_object* v_x_3317_, lean_object* v_x_3318_, lean_object* v_x_3319_, lean_object* v_x_3320_){
_start:
{
lean_object* v___x_3321_; 
v___x_3321_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__10_spec__16_spec__19_spec__21___redArg(v_x_3317_, v_x_3318_, v_x_3319_, v_x_3320_);
return v___x_3321_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14_spec__19(lean_object* v_00_u03b2_3322_, lean_object* v_keys_3323_, lean_object* v_vals_3324_, lean_object* v_heq_3325_, lean_object* v_i_3326_, lean_object* v_k_3327_){
_start:
{
uint8_t v___x_3328_; 
v___x_3328_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14_spec__19___redArg(v_keys_3323_, v_i_3326_, v_k_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14_spec__19___boxed(lean_object* v_00_u03b2_3329_, lean_object* v_keys_3330_, lean_object* v_vals_3331_, lean_object* v_heq_3332_, lean_object* v_i_3333_, lean_object* v_k_3334_){
_start:
{
uint8_t v_res_3335_; lean_object* v_r_3336_; 
v_res_3335_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_spec__6_spec__9_spec__14_spec__19(v_00_u03b2_3329_, v_keys_3330_, v_vals_3331_, v_heq_3332_, v_i_3333_, v_k_3334_);
lean_dec_ref(v_k_3334_);
lean_dec_ref(v_vals_3331_);
lean_dec_ref(v_keys_3330_);
v_r_3336_ = lean_box(v_res_3335_);
return v_r_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1(){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3346_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3347_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2));
v___x_3348_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1));
v___x_3349_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___boxed), 10, 0);
v___x_3350_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3346_, v___x_3347_, v___x_3348_, v___x_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___boxed(lean_object* v_a_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1();
return v_res_3352_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(builtin);
}
#ifdef __cplusplus
}
#endif
