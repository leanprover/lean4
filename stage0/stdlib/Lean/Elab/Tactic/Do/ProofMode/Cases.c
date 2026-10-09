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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_MCasesPat_parse___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(218, 187, 99, 122, 205, 56, 35, 106)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 222, 238, 124, 44, 25, 111, 81)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(89, 242, 56, 182, 153, 42, 114, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 162, 5, 152, 35, 161, 128, 56)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Cases"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 146, 40, 210, 100, 26, 188, 244)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(157, 47, 53, 92, 44, 87, 203, 83)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 242, 250, 200, 153, 102, 94, 106)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 189, 124, 77, 205, 184, 175, 156)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 88, 5, 221, 161, 161, 158, 230)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 208, 140, 23, 157, 48, 219, 108)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(249, 80, 168, 14, 14, 136, 83, 231)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(32, 215, 139, 75, 201, 47, 183, 17)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(129, 158, 105, 169, 239, 197, 90, 65)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 128, 16, 18, 221, 168, 137, 246)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 221, 139, 80, 206, 21, 33, 202)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 233, 100, 251, 113, 139, 68, 36)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(207, 128, 35, 29, 109, 6, 117, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(157, 128, 255, 187, 121, 29, 216, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(130, 186, 110, 64, 107, 50, 144, 42)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(723085142) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 61, 101, 95, 10, 175, 53, 174)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 238, 205, 38, 187, 61, 119, 254)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 34, 142, 28, 152, 50, 197, 86)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(122, 150, 214, 160, 180, 105, 176, 72)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bientails"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(201, 51, 221, 5, 242, 131, 169, 118)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(6, 95, 37, 108, 69, 205, 235, 200)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "IsAnd"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value),LEAN_SCALAR_PTR_LITERAL(244, 83, 223, 78, 97, 64, 238, 46)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "to_and"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value),LEAN_SCALAR_PTR_LITERAL(244, 83, 223, 78, 97, 64, 238, 46)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8_value),LEAN_SCALAR_PTR_LITERAL(151, 250, 181, 158, 145, 194, 213, 0)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "add_goal"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 254, 223, 142, 199, 149, 90, 110)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 254, 223, 142, 199, 149, 90, 110)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(237, 27, 197, 114, 200, 2, 153, 253)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 254, 223, 142, 199, 149, 90, 110)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 195, 94, 67, 62, 251, 248, 42)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clear"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 254, 223, 142, 199, 149, 90, 110)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 45, 21, 8, 254, 99, 220, 141)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "and_2"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 254, 223, 142, 199, 149, 90, 110)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 129, 169, 148, 64, 164, 21, 218)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "and_3"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 254, 223, 142, 199, 149, 90, 110)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__0 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__0_value;
static const lean_ctor_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 192, 12, 149, 146, 251, 197, 23)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabMCases"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 109, 55, 23, 237, 161, 174, 103)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_95_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_96_ = 0;
v___x_97_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_98_ = l_Lean_registerTraceClass(v___x_95_, v___x_96_, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_99_;
v_res_99_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_();
stack->m_obj
 = v_res_99_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2____boxed(lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_();
return v_res_101_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(lean_object* v_u_131_, lean_object* v_00_u03c3s_132_, lean_object* v_H_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___y_140_; uint8_t v___y_141_; lean_object* v_a_146_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = l_Lean_Expr_consumeMData(v_H_133_);
v___x_150_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v___x_149_);
lean_dec_ref(v___x_149_);
if (lean_obj_tag(v___x_150_) == 1)
{
lean_object* v_val_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_190_; 
v_val_151_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_190_ == 0)
{
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_190_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_val_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_190_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v_snd_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_188_; 
v_snd_155_ = lean_ctor_get(v_val_151_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v_val_151_);
if (v_isSharedCheck_188_ == 0)
{
lean_object* v_unused_189_; 
v_unused_189_ = lean_ctor_get(v_val_151_, 0);
lean_dec(v_unused_189_);
v___x_157_ = v_val_151_;
v_isShared_158_ = v_isSharedCheck_188_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_snd_155_);
lean_dec(v_val_151_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_188_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v_snd_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_186_; 
v_snd_159_ = lean_ctor_get(v_snd_155_, 1);
v_isSharedCheck_186_ = !lean_is_exclusive(v_snd_155_);
if (v_isSharedCheck_186_ == 0)
{
lean_object* v_unused_187_; 
v_unused_187_ = lean_ctor_get(v_snd_155_, 0);
lean_dec(v_unused_187_);
v___x_161_ = v_snd_155_;
v_isShared_162_ = v_isSharedCheck_186_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_snd_159_);
lean_dec(v_snd_155_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_186_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v_fst_163_; lean_object* v_snd_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_185_; 
v_fst_163_ = lean_ctor_get(v_snd_159_, 0);
v_snd_164_ = lean_ctor_get(v_snd_159_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v_snd_159_);
if (v_isSharedCheck_185_ == 0)
{
v___x_166_ = v_snd_159_;
v_isShared_167_ = v_isSharedCheck_185_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_snd_164_);
lean_inc(v_fst_163_);
lean_dec(v_snd_159_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_185_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_168_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4));
v___x_169_ = lean_box(0);
if (v_isShared_158_ == 0)
{
lean_ctor_set_tag(v___x_157_, 1);
lean_ctor_set(v___x_157_, 1, v___x_169_);
lean_ctor_set(v___x_157_, 0, v_u_131_);
v___x_171_ = v___x_157_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_u_131_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v___x_169_);
v___x_171_ = v_reuseFailAlloc_184_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_172_ = l_Lean_mkConst(v___x_168_, v___x_171_);
v___x_173_ = l_Lean_mkAppB(v___x_172_, v_00_u03c3s_132_, v_H_133_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_173_);
lean_ctor_set(v___x_166_, 0, v_snd_164_);
v___x_175_ = v___x_166_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_snd_164_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_173_);
v___x_175_ = v_reuseFailAlloc_183_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_177_; 
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 1, v___x_175_);
lean_ctor_set(v___x_161_, 0, v_fst_163_);
v___x_177_ = v___x_161_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_fst_163_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v___x_175_);
v___x_177_ = v_reuseFailAlloc_182_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_179_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_177_);
v___x_179_ = v___x_153_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_181_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; 
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
return v___x_180_;
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
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec(v___x_150_);
v___x_191_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5));
v___x_192_ = lean_box(0);
v___x_193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_193_, 0, v_u_131_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
lean_inc_ref(v___x_193_);
v___x_194_ = l_Lean_mkConst(v___x_191_, v___x_193_);
lean_inc_ref(v_00_u03c3s_132_);
v___x_195_ = l_Lean_Expr_app___override(v___x_194_, v_00_u03c3s_132_);
v___x_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
v___x_197_ = 0;
v___x_198_ = lean_box(0);
lean_inc_ref(v___x_196_);
v___x_199_ = l_Lean_Meta_mkFreshExprMVar(v___x_196_, v___x_197_, v___x_198_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; lean_object* v___x_201_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_a_200_);
lean_dec_ref_known(v___x_199_, 1);
v___x_201_ = l_Lean_Meta_mkFreshExprMVar(v___x_196_, v___x_197_, v___x_198_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_228_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_228_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_228_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_228_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_206_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7));
lean_inc_ref(v___x_193_);
v___x_207_ = l_Lean_mkConst(v___x_206_, v___x_193_);
lean_inc(v_a_202_);
lean_inc(v_a_200_);
lean_inc_ref(v_H_133_);
lean_inc_ref(v_00_u03c3s_132_);
v___x_208_ = l_Lean_mkApp4(v___x_207_, v_00_u03c3s_132_, v_H_133_, v_a_200_, v_a_202_);
v___x_209_ = lean_box(0);
v___x_210_ = l_Lean_Meta_synthInstance(v___x_208_, v___x_209_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_226_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_226_ == 0)
{
v___x_213_ = v___x_210_;
v_isShared_214_ = v_isSharedCheck_226_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_226_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_215_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9));
v___x_216_ = l_Lean_mkConst(v___x_215_, v___x_193_);
lean_inc(v_a_202_);
lean_inc(v_a_200_);
v___x_217_ = l_Lean_mkApp5(v___x_216_, v_00_u03c3s_132_, v_H_133_, v_a_200_, v_a_202_, v_a_211_);
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v_a_202_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v_a_200_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 1);
lean_ctor_set(v___x_204_, 0, v___x_219_);
v___x_221_ = v___x_204_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_225_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_223_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_221_);
v___x_223_ = v___x_213_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
else
{
lean_object* v_a_227_; 
lean_del_object(v___x_204_);
lean_dec(v_a_202_);
lean_dec(v_a_200_);
lean_dec_ref_known(v___x_193_, 2);
lean_dec_ref(v_H_133_);
lean_dec_ref(v_00_u03c3s_132_);
v_a_227_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_227_);
lean_dec_ref_known(v___x_210_, 1);
v_a_146_ = v_a_227_;
goto v___jp_145_;
}
}
}
else
{
lean_object* v_a_229_; 
lean_dec(v_a_200_);
lean_dec_ref_known(v___x_193_, 2);
lean_dec_ref(v_H_133_);
lean_dec_ref(v_00_u03c3s_132_);
v_a_229_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_201_, 1);
v_a_146_ = v_a_229_;
goto v___jp_145_;
}
}
else
{
lean_object* v_a_230_; 
lean_dec_ref_known(v___x_196_, 1);
lean_dec_ref_known(v___x_193_, 2);
lean_dec_ref(v_H_133_);
lean_dec_ref(v_00_u03c3s_132_);
v_a_230_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v___x_199_, 1);
v_a_146_ = v_a_230_;
goto v___jp_145_;
}
}
v___jp_139_:
{
if (v___y_141_ == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec_ref(v___y_140_);
v___x_142_ = lean_box(0);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
else
{
lean_object* v___x_144_; 
v___x_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_144_, 0, v___y_140_);
return v___x_144_;
}
}
v___jp_145_:
{
uint8_t v___x_147_; 
v___x_147_ = l_Lean_Exception_isInterrupt(v_a_146_);
if (v___x_147_ == 0)
{
uint8_t v___x_148_; 
lean_inc_ref(v_a_146_);
v___x_148_ = l_Lean_Exception_isRuntime(v_a_146_);
v___y_140_ = v_a_146_;
v___y_141_ = v___x_148_;
goto v___jp_139_;
}
else
{
v___y_140_ = v_a_146_;
v___y_141_ = v___x_147_;
goto v___jp_139_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_131_ = stack[0].m_obj;
lean_object* v_00_u03c3s_132_ = stack[1].m_obj;
lean_object* v_H_133_ = stack[2].m_obj;
lean_object* v_a_134_ = stack[3].m_obj;
lean_object* v_a_135_ = stack[4].m_obj;
lean_object* v_a_136_ = stack[5].m_obj;
lean_object* v_a_137_ = stack[6].m_obj;
lean_object* v_res_231_;
v_res_231_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(v_u_131_, v_00_u03c3s_132_, v_H_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
stack->m_obj
 = v_res_231_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___boxed(lean_object* v_u_232_, lean_object* v_00_u03c3s_233_, lean_object* v_H_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(v_u_232_, v_00_u03c3s_233_, v_H_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
return v_res_240_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal(lean_object* v_u_249_, lean_object* v_goals_250_, lean_object* v_00_u03c3s_251_, lean_object* v_T_252_, lean_object* v_Q_253_, lean_object* v_H_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___x_260_; lean_object* v_fst_261_; lean_object* v_snd_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_302_; 
lean_inc_ref(v_H_254_);
lean_inc_ref(v_Q_253_);
lean_inc_ref(v_00_u03c3s_251_);
lean_inc(v_u_249_);
v___x_260_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_249_, v_00_u03c3s_251_, v_Q_253_, v_H_254_);
v_fst_261_ = lean_ctor_get(v___x_260_, 0);
v_snd_262_ = lean_ctor_get(v___x_260_, 1);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_302_ == 0)
{
v___x_264_ = v___x_260_;
v_isShared_265_ = v_isSharedCheck_302_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_snd_262_);
lean_inc(v_fst_261_);
lean_dec(v___x_260_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_302_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v_goal_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
lean_inc_ref(v_T_252_);
lean_inc(v_fst_261_);
lean_inc_ref(v_00_u03c3s_251_);
lean_inc(v_u_249_);
v_goal_266_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_goal_266_, 0, v_u_249_);
lean_ctor_set(v_goal_266_, 1, v_00_u03c3s_251_);
lean_ctor_set(v_goal_266_, 2, v_fst_261_);
lean_ctor_set(v_goal_266_, 3, v_T_252_);
v___x_267_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_266_);
v___x_268_ = lean_box(0);
v___x_269_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_267_, v___x_268_, v_a_255_, v_a_256_, v_a_257_, v_a_258_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_293_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_293_ == 0)
{
v___x_272_ = v___x_269_;
v_isShared_273_ = v_isSharedCheck_293_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_293_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_274_ = lean_st_ref_take(v_goals_250_);
v___x_275_ = l_Lean_Expr_mvarId_x21(v_a_270_);
v___x_276_ = lean_array_push(v___x_274_, v___x_275_);
v___x_277_ = lean_st_ref_put(v_goals_250_, v___x_276_);
v___x_278_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1));
v___x_279_ = lean_box(0);
lean_inc_n(v_u_249_, 2);
v___x_280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_280_, 0, v_u_249_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = l_Lean_mkConst(v___x_278_, v___x_280_);
lean_inc_ref(v_T_252_);
lean_inc_ref(v_H_254_);
lean_inc_ref(v_Q_253_);
lean_inc_ref_n(v_00_u03c3s_251_, 2);
v___x_282_ = l_Lean_mkApp7(v___x_281_, v_00_u03c3s_251_, v_fst_261_, v_Q_253_, v_H_254_, v_T_252_, v_snd_262_, v_a_270_);
v___x_283_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_249_, v_00_u03c3s_251_, v_Q_253_, v_H_254_);
v___x_284_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_284_, 0, v_u_249_);
lean_ctor_set(v___x_284_, 1, v_00_u03c3s_251_);
lean_ctor_set(v___x_284_, 2, v___x_283_);
lean_ctor_set(v___x_284_, 3, v_T_252_);
v___x_285_ = lean_box(0);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 1, v___x_282_);
lean_ctor_set(v___x_264_, 0, v___x_284_);
v___x_287_ = v___x_264_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v___x_282_);
v___x_287_ = v_reuseFailAlloc_292_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_285_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_288_);
v___x_290_ = v___x_272_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
lean_del_object(v___x_264_);
lean_dec(v_snd_262_);
lean_dec(v_fst_261_);
lean_dec_ref(v_H_254_);
lean_dec_ref(v_Q_253_);
lean_dec_ref(v_T_252_);
lean_dec_ref(v_00_u03c3s_251_);
lean_dec(v_u_249_);
v_a_294_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_269_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_269_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_249_ = stack[0].m_obj;
lean_object* v_goals_250_ = stack[1].m_obj;
lean_object* v_00_u03c3s_251_ = stack[2].m_obj;
lean_object* v_T_252_ = stack[3].m_obj;
lean_object* v_Q_253_ = stack[4].m_obj;
lean_object* v_H_254_ = stack[5].m_obj;
lean_object* v_a_255_ = stack[6].m_obj;
lean_object* v_a_256_ = stack[7].m_obj;
lean_object* v_a_257_ = stack[8].m_obj;
lean_object* v_a_258_ = stack[9].m_obj;
lean_object* v_res_303_;
v_res_303_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal(v_u_249_, v_goals_250_, v_00_u03c3s_251_, v_T_252_, v_Q_253_, v_H_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_);
stack->m_obj
 = v_res_303_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___boxed(lean_object* v_u_304_, lean_object* v_goals_305_, lean_object* v_00_u03c3s_306_, lean_object* v_T_307_, lean_object* v_Q_308_, lean_object* v_H_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal(v_u_304_, v_goals_305_, v_00_u03c3s_306_, v_T_307_, v_Q_308_, v_H_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_goals_305_);
return v_res_315_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(lean_object* v_msgData_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v___x_322_; lean_object* v_env_323_; uint8_t v___x_324_; lean_object* v_env_325_; lean_object* v___x_326_; lean_object* v_toCold_327_; lean_object* v_mctx_328_; lean_object* v_lctx_329_; lean_object* v_options_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_322_ = lean_st_ref_get(v___y_320_);
v_env_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc_ref(v_env_323_);
lean_dec(v___x_322_);
v___x_324_ = 0;
v_env_325_ = l_Lean_Environment_setRecordingDeps(v_env_323_, v___x_324_);
v___x_326_ = lean_st_ref_get(v___y_318_);
v_toCold_327_ = lean_ctor_get(v___y_319_, 0);
v_mctx_328_ = lean_ctor_get(v___x_326_, 0);
lean_inc_ref(v_mctx_328_);
lean_dec(v___x_326_);
v_lctx_329_ = lean_ctor_get(v___y_317_, 2);
v_options_330_ = lean_ctor_get(v_toCold_327_, 2);
lean_inc_ref(v_options_330_);
lean_inc_ref(v_lctx_329_);
v___x_331_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_331_, 0, v_env_325_);
lean_ctor_set(v___x_331_, 1, v_mctx_328_);
lean_ctor_set(v___x_331_, 2, v_lctx_329_);
lean_ctor_set(v___x_331_, 3, v_options_330_);
v___x_332_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v_msgData_316_);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_316_ = stack[0].m_obj;
lean_object* v___y_317_ = stack[1].m_obj;
lean_object* v___y_318_ = stack[2].m_obj;
lean_object* v___y_319_ = stack[3].m_obj;
lean_object* v___y_320_ = stack[4].m_obj;
lean_object* v_res_334_;
v_res_334_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msgData_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
stack->m_obj
 = v_res_334_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0___boxed(lean_object* v_msgData_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msgData_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
return v_res_341_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(lean_object* v_msg_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_ref_348_; lean_object* v___x_349_; lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_358_; 
v_ref_348_ = lean_ctor_get(v___y_345_, 2);
v___x_349_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_358_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_356_; 
lean_inc(v_ref_348_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v_ref_348_);
lean_ctor_set(v___x_354_, 1, v_a_350_);
if (v_isShared_353_ == 0)
{
lean_ctor_set_tag(v___x_352_, 1);
lean_ctor_set(v___x_352_, 0, v___x_354_);
v___x_356_ = v___x_352_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
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
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_342_ = stack[0].m_obj;
lean_object* v___y_343_ = stack[1].m_obj;
lean_object* v___y_344_ = stack[2].m_obj;
lean_object* v___y_345_ = stack[3].m_obj;
lean_object* v___y_346_ = stack[4].m_obj;
lean_object* v_res_359_;
v_res_359_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v_msg_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
stack->m_obj
 = v_res_359_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg___boxed(lean_object* v_msg_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v_msg_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
return v_res_366_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0));
v___x_369_ = l_Lean_stringToMessageData(v___x_368_);
return v___x_369_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(lean_object* v_goal_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_hyps_376_; lean_object* v___x_377_; 
v_hyps_376_ = lean_ctor_get(v_goal_370_, 2);
lean_inc_ref(v_hyps_376_);
lean_dec_ref(v_goal_370_);
v___x_377_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_hyps_376_);
if (lean_obj_tag(v___x_377_) == 1)
{
lean_object* v_val_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_387_; 
lean_dec_ref(v_hyps_376_);
v_val_378_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_387_ == 0)
{
v___x_380_ = v___x_377_;
v_isShared_381_ = v_isSharedCheck_387_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_val_378_);
lean_dec(v___x_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_387_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v_snd_382_; lean_object* v_snd_383_; lean_object* v___x_385_; 
v_snd_382_ = lean_ctor_get(v_val_378_, 1);
lean_inc(v_snd_382_);
lean_dec(v_val_378_);
v_snd_383_ = lean_ctor_get(v_snd_382_, 1);
lean_inc(v_snd_383_);
lean_dec(v_snd_382_);
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 0);
lean_ctor_set(v___x_380_, 0, v_snd_383_);
v___x_385_ = v___x_380_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_snd_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec(v___x_377_);
v___x_388_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1, &l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1);
v___x_389_ = l_Lean_MessageData_ofExpr(v_hyps_376_);
v___x_390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_388_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_390_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
return v___x_391_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_370_ = stack[0].m_obj;
lean_object* v_a_371_ = stack[1].m_obj;
lean_object* v_a_372_ = stack[2].m_obj;
lean_object* v_a_373_ = stack[3].m_obj;
lean_object* v_a_374_ = stack[4].m_obj;
lean_object* v_res_392_;
v_res_392_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_goal_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
stack->m_obj
 = v_res_392_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___boxed(lean_object* v_goal_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_goal_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
return v_res_399_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0(lean_object* v_00_u03b1_400_, lean_object* v_msg_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v_msg_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
return v___x_407_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_401_ = stack[1].m_obj;
lean_object* v___y_402_ = stack[2].m_obj;
lean_object* v___y_403_ = stack[3].m_obj;
lean_object* v___y_404_ = stack[4].m_obj;
lean_object* v___y_405_ = stack[5].m_obj;
lean_object* v_res_408_;
v_res_408_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0(lean_box(0), v_msg_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
stack->m_obj
 = v_res_408_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___boxed(lean_object* v_00_u03b1_409_, lean_object* v_msg_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0(v_00_u03b1_409_, v_msg_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_416_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0(lean_object* v___x_417_, lean_object* v_snd_418_, lean_object* v_k_419_, uint8_t v___x_420_, lean_object* v___x_421_, lean_object* v___x_422_, lean_object* v___x_423_, lean_object* v___x_424_, lean_object* v___x_425_, lean_object* v___x_426_, lean_object* v_H_427_, lean_object* v_x_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_lctx_434_; lean_object* v___x_435_; uint8_t v___x_436_; lean_object* v___x_437_; 
v_lctx_434_ = lean_ctor_get(v___y_429_, 2);
lean_inc_ref(v___x_417_);
v___x_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_417_);
v___x_436_ = 0;
lean_inc_ref(v_x_428_);
lean_inc_ref(v_lctx_434_);
v___x_437_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_snd_418_, v_lctx_434_, v_x_428_, v___x_435_, v___x_436_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v___x_438_; 
lean_dec_ref_known(v___x_437_, 1);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v___y_429_);
lean_inc_ref(v_x_428_);
v___x_438_ = lean_apply_6(v_k_419_, v_x_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, lean_box(0));
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v_snd_440_; lean_object* v_fst_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_526_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
v_snd_440_ = lean_ctor_get(v_a_439_, 1);
v_fst_441_ = lean_ctor_get(v_a_439_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v_a_439_);
if (v_isSharedCheck_526_ == 0)
{
v___x_443_ = v_a_439_;
v_isShared_444_ = v_isSharedCheck_526_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_snd_440_);
lean_inc(v_fst_441_);
lean_dec(v_a_439_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_526_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v_fst_445_; lean_object* v_snd_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_525_; 
v_fst_445_ = lean_ctor_get(v_snd_440_, 0);
v_snd_446_ = lean_ctor_get(v_snd_440_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v_snd_440_);
if (v_isSharedCheck_525_ == 0)
{
v___x_448_ = v_snd_440_;
v_isShared_449_ = v_isSharedCheck_525_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_snd_446_);
lean_inc(v_fst_445_);
lean_dec(v_snd_440_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_525_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; 
lean_inc(v_fst_445_);
v___x_450_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_445_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v_fst_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_515_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_a_451_);
lean_dec_ref_known(v___x_450_, 1);
v_fst_452_ = lean_ctor_get(v_a_451_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v_a_451_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; 
v_unused_516_ = lean_ctor_get(v_a_451_, 1);
lean_dec(v_unused_516_);
v___x_454_ = v_a_451_;
v_isShared_455_ = v_isSharedCheck_515_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_fst_452_);
lean_dec(v_a_451_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_515_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; 
lean_inc_ref(v___x_417_);
v___x_456_ = l_Lean_Meta_getLevel(v___x_417_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref_known(v___x_456_, 1);
v___x_458_ = lean_unsigned_to_nat(1u);
v___x_459_ = lean_mk_empty_array_with_capacity(v___x_458_);
v___x_460_ = lean_array_push(v___x_459_, v_x_428_);
v___x_461_ = 1;
v___x_462_ = l_Lean_Meta_mkLambdaFVars(v___x_460_, v_snd_446_, v___x_436_, v___x_420_, v___x_436_, v___x_420_, v___x_461_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
lean_dec_ref(v___x_460_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_498_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_498_ == 0)
{
v___x_465_ = v___x_462_;
v_isShared_466_ = v_isSharedCheck_498_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_462_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_498_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v_u_467_; lean_object* v_00_u03c3s_468_; lean_object* v_target_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_496_; 
v_u_467_ = lean_ctor_get(v_fst_445_, 0);
v_00_u03c3s_468_ = lean_ctor_get(v_fst_445_, 1);
v_target_469_ = lean_ctor_get(v_fst_445_, 3);
v_isSharedCheck_496_ = !lean_is_exclusive(v_fst_445_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; 
v_unused_497_ = lean_ctor_get(v_fst_445_, 2);
lean_dec(v_unused_497_);
v___x_471_ = v_fst_445_;
v_isShared_472_ = v_isSharedCheck_496_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_target_469_);
lean_inc(v_00_u03c3s_468_);
lean_inc(v_u_467_);
lean_dec(v_fst_445_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_496_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_473_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_474_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_475_ = l_Lean_Name_mkStr6(v___x_421_, v___x_422_, v___x_423_, v___x_473_, v___x_474_, v___x_424_);
v___x_476_ = lean_box(0);
if (v_isShared_444_ == 0)
{
lean_ctor_set_tag(v___x_443_, 1);
lean_ctor_set(v___x_443_, 1, v___x_476_);
lean_ctor_set(v___x_443_, 0, v_a_457_);
v___x_478_ = v___x_443_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_457_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_476_);
v___x_478_ = v_reuseFailAlloc_495_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
lean_inc_n(v_u_467_, 2);
v___x_479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_479_, 0, v_u_467_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v___x_480_ = l_Lean_mkConst(v___x_475_, v___x_479_);
lean_inc_ref(v_target_469_);
lean_inc(v_fst_452_);
lean_inc_ref(v___x_425_);
v___x_481_ = l_Lean_mkApp6(v___x_480_, v___x_425_, v___x_417_, v_fst_452_, v___x_426_, v_target_469_, v_a_463_);
v___x_482_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_467_, v___x_425_, v_fst_452_, v_H_427_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 2, v___x_482_);
v___x_484_ = v___x_471_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_u_467_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_00_u03c3s_468_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v___x_482_);
lean_ctor_set(v_reuseFailAlloc_494_, 3, v_target_469_);
v___x_484_ = v_reuseFailAlloc_494_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_486_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_481_);
lean_ctor_set(v___x_454_, 0, v___x_484_);
v___x_486_ = v___x_454_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v___x_481_);
v___x_486_ = v_reuseFailAlloc_493_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_488_; 
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 1, v___x_486_);
lean_ctor_set(v___x_448_, 0, v_fst_441_);
v___x_488_ = v___x_448_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_fst_441_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v___x_486_);
v___x_488_ = v_reuseFailAlloc_492_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_490_; 
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_488_);
v___x_490_ = v___x_465_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
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
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec(v_a_457_);
lean_del_object(v___x_454_);
lean_dec(v_fst_452_);
lean_del_object(v___x_448_);
lean_dec(v_fst_445_);
lean_del_object(v___x_443_);
lean_dec(v_fst_441_);
lean_dec_ref(v_H_427_);
lean_dec_ref(v___x_426_);
lean_dec_ref(v___x_425_);
lean_dec_ref(v___x_424_);
lean_dec_ref(v___x_423_);
lean_dec_ref(v___x_422_);
lean_dec_ref(v___x_421_);
lean_dec_ref(v___x_417_);
v_a_499_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_462_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_462_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_del_object(v___x_454_);
lean_dec(v_fst_452_);
lean_del_object(v___x_448_);
lean_dec(v_snd_446_);
lean_dec(v_fst_445_);
lean_del_object(v___x_443_);
lean_dec(v_fst_441_);
lean_dec_ref(v_x_428_);
lean_dec_ref(v_H_427_);
lean_dec_ref(v___x_426_);
lean_dec_ref(v___x_425_);
lean_dec_ref(v___x_424_);
lean_dec_ref(v___x_423_);
lean_dec_ref(v___x_422_);
lean_dec_ref(v___x_421_);
lean_dec_ref(v___x_417_);
v_a_507_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_456_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_456_);
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
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_del_object(v___x_448_);
lean_dec(v_snd_446_);
lean_dec(v_fst_445_);
lean_del_object(v___x_443_);
lean_dec(v_fst_441_);
lean_dec_ref(v_x_428_);
lean_dec_ref(v_H_427_);
lean_dec_ref(v___x_426_);
lean_dec_ref(v___x_425_);
lean_dec_ref(v___x_424_);
lean_dec_ref(v___x_423_);
lean_dec_ref(v___x_422_);
lean_dec_ref(v___x_421_);
lean_dec_ref(v___x_417_);
v_a_517_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_450_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_450_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
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
}
else
{
lean_dec_ref(v_x_428_);
lean_dec_ref(v_H_427_);
lean_dec_ref(v___x_426_);
lean_dec_ref(v___x_425_);
lean_dec_ref(v___x_424_);
lean_dec_ref(v___x_423_);
lean_dec_ref(v___x_422_);
lean_dec_ref(v___x_421_);
lean_dec_ref(v___x_417_);
return v___x_438_;
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec_ref(v_x_428_);
lean_dec_ref(v_H_427_);
lean_dec_ref(v___x_426_);
lean_dec_ref(v___x_425_);
lean_dec_ref(v___x_424_);
lean_dec_ref(v___x_423_);
lean_dec_ref(v___x_422_);
lean_dec_ref(v___x_421_);
lean_dec_ref(v_k_419_);
lean_dec_ref(v___x_417_);
v_a_527_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_437_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_437_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_417_ = stack[0].m_obj;
lean_object* v_snd_418_ = stack[1].m_obj;
lean_object* v_k_419_ = stack[2].m_obj;
uint8_t v___x_420_ = stack[3].m_num;
lean_object* v___x_421_ = stack[4].m_obj;
lean_object* v___x_422_ = stack[5].m_obj;
lean_object* v___x_423_ = stack[6].m_obj;
lean_object* v___x_424_ = stack[7].m_obj;
lean_object* v___x_425_ = stack[8].m_obj;
lean_object* v___x_426_ = stack[9].m_obj;
lean_object* v_H_427_ = stack[10].m_obj;
lean_object* v_x_428_ = stack[11].m_obj;
lean_object* v___y_429_ = stack[12].m_obj;
lean_object* v___y_430_ = stack[13].m_obj;
lean_object* v___y_431_ = stack[14].m_obj;
lean_object* v___y_432_ = stack[15].m_obj;
lean_object* v_res_535_;
v_res_535_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0(v___x_417_, v_snd_418_, v_k_419_, v___x_420_, v___x_421_, v___x_422_, v___x_423_, v___x_424_, v___x_425_, v___x_426_, v_H_427_, v_x_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
stack->m_obj
 = v_res_535_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_536_ = _args[0];
lean_object* v_snd_537_ = _args[1];
lean_object* v_k_538_ = _args[2];
lean_object* v___x_539_ = _args[3];
lean_object* v___x_540_ = _args[4];
lean_object* v___x_541_ = _args[5];
lean_object* v___x_542_ = _args[6];
lean_object* v___x_543_ = _args[7];
lean_object* v___x_544_ = _args[8];
lean_object* v___x_545_ = _args[9];
lean_object* v_H_546_ = _args[10];
lean_object* v_x_547_ = _args[11];
lean_object* v___y_548_ = _args[12];
lean_object* v___y_549_ = _args[13];
lean_object* v___y_550_ = _args[14];
lean_object* v___y_551_ = _args[15];
lean_object* v___y_552_ = _args[16];
_start:
{
uint8_t v___x_2258__boxed_553_; lean_object* v_res_554_; 
v___x_2258__boxed_553_ = lean_unbox(v___x_539_);
v_res_554_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0(v___x_536_, v_snd_537_, v_k_538_, v___x_2258__boxed_553_, v___x_540_, v___x_541_, v___x_542_, v___x_543_, v___x_544_, v___x_545_, v_H_546_, v_x_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
return v_res_554_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0(lean_object* v_k_555_, lean_object* v_b_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v___x_562_; 
lean_inc(v___y_560_);
lean_inc_ref(v___y_559_);
lean_inc(v___y_558_);
lean_inc_ref(v___y_557_);
v___x_562_ = lean_apply_6(v_k_555_, v_b_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, lean_box(0));
return v___x_562_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_555_ = stack[0].m_obj;
lean_object* v_b_556_ = stack[1].m_obj;
lean_object* v___y_557_ = stack[2].m_obj;
lean_object* v___y_558_ = stack[3].m_obj;
lean_object* v___y_559_ = stack[4].m_obj;
lean_object* v___y_560_ = stack[5].m_obj;
lean_object* v_res_563_;
v_res_563_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0(v_k_555_, v_b_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
stack->m_obj
 = v_res_563_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_564_, lean_object* v_b_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0(v_k_564_, v_b_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
return v_res_571_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(lean_object* v_name_572_, uint8_t v_bi_573_, lean_object* v_type_574_, lean_object* v_k_575_, uint8_t v_kind_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___f_582_; lean_object* v___x_583_; 
v___f_582_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_582_, 0, v_k_575_);
v___x_583_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_572_, v_bi_573_, v_type_574_, v___f_582_, v_kind_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
v_a_592_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_583_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_583_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_572_ = stack[0].m_obj;
uint8_t v_bi_573_ = stack[1].m_num;
lean_object* v_type_574_ = stack[2].m_obj;
lean_object* v_k_575_ = stack[3].m_obj;
uint8_t v_kind_576_ = stack[4].m_num;
lean_object* v___y_577_ = stack[5].m_obj;
lean_object* v___y_578_ = stack[6].m_obj;
lean_object* v___y_579_ = stack[7].m_obj;
lean_object* v___y_580_ = stack[8].m_obj;
lean_object* v_res_600_;
v_res_600_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_572_, v_bi_573_, v_type_574_, v_k_575_, v_kind_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
stack->m_obj
 = v_res_600_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___boxed(lean_object* v_name_601_, lean_object* v_bi_602_, lean_object* v_type_603_, lean_object* v_k_604_, lean_object* v_kind_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
uint8_t v_bi_boxed_611_; uint8_t v_kind_boxed_612_; lean_object* v_res_613_; 
v_bi_boxed_611_ = lean_unbox(v_bi_602_);
v_kind_boxed_612_ = lean_unbox(v_kind_605_);
v_res_613_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_601_, v_bi_boxed_611_, v_type_603_, v_k_604_, v_kind_boxed_612_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
return v_res_613_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(lean_object* v_name_614_, lean_object* v_type_615_, lean_object* v_k_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
uint8_t v___x_622_; uint8_t v___x_623_; lean_object* v___x_624_; 
v___x_622_ = 0;
v___x_623_ = 0;
v___x_624_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_614_, v___x_622_, v_type_615_, v_k_616_, v___x_623_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
return v___x_624_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_614_ = stack[0].m_obj;
lean_object* v_type_615_ = stack[1].m_obj;
lean_object* v_k_616_ = stack[2].m_obj;
lean_object* v___y_617_ = stack[3].m_obj;
lean_object* v___y_618_ = stack[4].m_obj;
lean_object* v___y_619_ = stack[5].m_obj;
lean_object* v___y_620_ = stack[6].m_obj;
lean_object* v_res_625_;
v_res_625_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_name_614_, v_type_615_, v_k_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
stack->m_obj
 = v_res_625_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg___boxed(lean_object* v_name_626_, lean_object* v_type_627_, lean_object* v_k_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_name_626_, v_type_627_, v_k_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
return v_res_634_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2));
v___x_643_ = l_Lean_stringToMessageData(v___x_642_);
return v___x_643_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(lean_object* v_H_644_, lean_object* v_name_645_, lean_object* v_k_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_652_ = l_Lean_Expr_consumeMData(v_H_644_);
v___x_653_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0));
v___x_654_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_655_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1));
v___x_656_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0));
v___x_657_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1));
v___x_658_ = lean_unsigned_to_nat(3u);
v___x_659_ = l_Lean_Expr_isAppOfArity(v___x_652_, v___x_657_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec_ref(v___x_652_);
lean_dec_ref(v_k_646_);
lean_dec(v_name_645_);
v___x_660_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3);
v___x_661_ = l_Lean_MessageData_ofExpr(v_H_644_);
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_662_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
return v___x_663_;
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_664_ = l_Lean_Expr_appFn_x21(v___x_652_);
v___x_665_ = l_Lean_Expr_appFn_x21(v___x_664_);
v___x_666_ = l_Lean_Expr_appArg_x21(v___x_665_);
lean_dec_ref(v___x_665_);
v___x_667_ = l_Lean_Expr_appArg_x21(v___x_664_);
lean_dec_ref(v___x_664_);
v___x_668_ = l_Lean_Expr_appArg_x21(v___x_652_);
lean_dec_ref(v___x_652_);
v___x_669_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_name_645_, v_a_649_, v_a_650_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v_fst_671_; lean_object* v_snd_672_; lean_object* v___x_673_; lean_object* v___f_674_; lean_object* v___x_675_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
v_fst_671_ = lean_ctor_get(v_a_670_, 0);
lean_inc(v_fst_671_);
v_snd_672_ = lean_ctor_get(v_a_670_, 1);
lean_inc(v_snd_672_);
lean_dec(v_a_670_);
v___x_673_ = lean_box(v___x_659_);
lean_inc_ref(v___x_666_);
v___f_674_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0___boxed), 17, 11);
lean_closure_set(v___f_674_, 0, v___x_666_);
lean_closure_set(v___f_674_, 1, v_snd_672_);
lean_closure_set(v___f_674_, 2, v_k_646_);
lean_closure_set(v___f_674_, 3, v___x_673_);
lean_closure_set(v___f_674_, 4, v___x_653_);
lean_closure_set(v___f_674_, 5, v___x_654_);
lean_closure_set(v___f_674_, 6, v___x_655_);
lean_closure_set(v___f_674_, 7, v___x_656_);
lean_closure_set(v___f_674_, 8, v___x_667_);
lean_closure_set(v___f_674_, 9, v___x_668_);
lean_closure_set(v___f_674_, 10, v_H_644_);
v___x_675_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_fst_671_, v___x_666_, v___f_674_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
return v___x_675_;
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref(v___x_668_);
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec_ref(v_k_646_);
lean_dec_ref(v_H_644_);
v_a_676_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_669_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_669_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_H_644_ = stack[0].m_obj;
lean_object* v_name_645_ = stack[1].m_obj;
lean_object* v_k_646_ = stack[2].m_obj;
lean_object* v_a_647_ = stack[3].m_obj;
lean_object* v_a_648_ = stack[4].m_obj;
lean_object* v_a_649_ = stack[5].m_obj;
lean_object* v_a_650_ = stack[6].m_obj;
lean_object* v_res_684_;
v_res_684_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(v_H_644_, v_name_645_, v_k_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
stack->m_obj
 = v_res_684_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___boxed(lean_object* v_H_685_, lean_object* v_name_686_, lean_object* v_k_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(v_H_685_, v_name_686_, v_k_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_);
lean_dec(v_a_691_);
lean_dec_ref(v_a_690_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
return v_res_693_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists(lean_object* v_00_u03b1_694_, lean_object* v_H_695_, lean_object* v_name_696_, lean_object* v_k_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(v_H_695_, v_name_696_, v_k_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
return v___x_703_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists_0interp(lean_interpreter_value* stack)
{
lean_object* v_H_695_ = stack[1].m_obj;
lean_object* v_name_696_ = stack[2].m_obj;
lean_object* v_k_697_ = stack[3].m_obj;
lean_object* v_a_698_ = stack[4].m_obj;
lean_object* v_a_699_ = stack[5].m_obj;
lean_object* v_a_700_ = stack[6].m_obj;
lean_object* v_a_701_ = stack[7].m_obj;
lean_object* v_res_704_;
v_res_704_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists(lean_box(0), v_H_695_, v_name_696_, v_k_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
stack->m_obj
 = v_res_704_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___boxed(lean_object* v_00_u03b1_705_, lean_object* v_H_706_, lean_object* v_name_707_, lean_object* v_k_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists(v_00_u03b1_705_, v_H_706_, v_name_707_, v_k_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
return v_res_714_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0(lean_object* v_00_u03b1_715_, lean_object* v_name_716_, uint8_t v_bi_717_, lean_object* v_type_718_, lean_object* v_k_719_, uint8_t v_kind_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_716_, v_bi_717_, v_type_718_, v_k_719_, v_kind_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
return v___x_726_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_716_ = stack[1].m_obj;
uint8_t v_bi_717_ = stack[2].m_num;
lean_object* v_type_718_ = stack[3].m_obj;
lean_object* v_k_719_ = stack[4].m_obj;
uint8_t v_kind_720_ = stack[5].m_num;
lean_object* v___y_721_ = stack[6].m_obj;
lean_object* v___y_722_ = stack[7].m_obj;
lean_object* v___y_723_ = stack[8].m_obj;
lean_object* v___y_724_ = stack[9].m_obj;
lean_object* v_res_727_;
v_res_727_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0(lean_box(0), v_name_716_, v_bi_717_, v_type_718_, v_k_719_, v_kind_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
stack->m_obj
 = v_res_727_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___boxed(lean_object* v_00_u03b1_728_, lean_object* v_name_729_, lean_object* v_bi_730_, lean_object* v_type_731_, lean_object* v_k_732_, lean_object* v_kind_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
uint8_t v_bi_boxed_739_; uint8_t v_kind_boxed_740_; lean_object* v_res_741_; 
v_bi_boxed_739_ = lean_unbox(v_bi_730_);
v_kind_boxed_740_ = lean_unbox(v_kind_733_);
v_res_741_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0(v_00_u03b1_728_, v_name_729_, v_bi_boxed_739_, v_type_731_, v_k_732_, v_kind_boxed_740_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_741_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0(lean_object* v_00_u03b1_742_, lean_object* v_name_743_, lean_object* v_type_744_, lean_object* v_k_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_name_743_, v_type_744_, v_k_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
return v___x_751_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_743_ = stack[1].m_obj;
lean_object* v_type_744_ = stack[2].m_obj;
lean_object* v_k_745_ = stack[3].m_obj;
lean_object* v___y_746_ = stack[4].m_obj;
lean_object* v___y_747_ = stack[5].m_obj;
lean_object* v___y_748_ = stack[6].m_obj;
lean_object* v___y_749_ = stack[7].m_obj;
lean_object* v_res_752_;
v_res_752_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0(lean_box(0), v_name_743_, v_type_744_, v_k_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
stack->m_obj
 = v_res_752_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___boxed(lean_object* v_00_u03b1_753_, lean_object* v_name_754_, lean_object* v_type_755_, lean_object* v_k_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0(v_00_u03b1_753_, v_name_754_, v_type_755_, v_k_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
return v_res_762_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_box(0);
v___x_764_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_763_);
return v___x_765_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg(){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0);
v___x_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_769_;
v_res_769_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
stack->m_obj
 = v_res_769_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___boxed(lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
return v_res_771_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0(lean_object* v_00_u03b1_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
return v___x_778_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_773_ = stack[1].m_obj;
lean_object* v___y_774_ = stack[2].m_obj;
lean_object* v___y_775_ = stack[3].m_obj;
lean_object* v___y_776_ = stack[4].m_obj;
lean_object* v_res_779_;
v_res_779_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0(lean_box(0), v___y_773_, v___y_774_, v___y_775_, v___y_776_);
stack->m_obj
 = v_res_779_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___boxed(lean_object* v_00_u03b1_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0(v_00_u03b1_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
return v_res_786_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(lean_object* v___y_787_){
_start:
{
lean_object* v___x_789_; lean_object* v_ngen_790_; lean_object* v_namePrefix_791_; lean_object* v_idx_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_822_; 
v___x_789_ = lean_st_ref_get(v___y_787_);
v_ngen_790_ = lean_ctor_get(v___x_789_, 2);
lean_inc_ref(v_ngen_790_);
lean_dec(v___x_789_);
v_namePrefix_791_ = lean_ctor_get(v_ngen_790_, 0);
v_idx_792_ = lean_ctor_get(v_ngen_790_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v_ngen_790_);
if (v_isSharedCheck_822_ == 0)
{
v___x_794_ = v_ngen_790_;
v_isShared_795_ = v_isSharedCheck_822_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_idx_792_);
lean_inc(v_namePrefix_791_);
lean_dec(v_ngen_790_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_822_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v_r_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
lean_inc(v_idx_792_);
lean_inc(v_namePrefix_791_);
v_r_796_ = l_Lean_Name_num___override(v_namePrefix_791_, v_idx_792_);
v___x_797_ = lean_unsigned_to_nat(1u);
v___x_798_ = lean_nat_add(v_idx_792_, v___x_797_);
lean_dec(v_idx_792_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v___x_798_);
v___x_800_ = v___x_794_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_namePrefix_791_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___x_798_);
v___x_800_ = v_reuseFailAlloc_821_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; lean_object* v_env_802_; lean_object* v_nextMacroScope_803_; lean_object* v_auxDeclNGen_804_; lean_object* v_traceState_805_; lean_object* v_cache_806_; lean_object* v_recordedDeps_807_; lean_object* v_messages_808_; lean_object* v_infoState_809_; lean_object* v_snapshotTasks_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_819_; 
v___x_801_ = lean_st_ref_take(v___y_787_);
v_env_802_ = lean_ctor_get(v___x_801_, 0);
v_nextMacroScope_803_ = lean_ctor_get(v___x_801_, 1);
v_auxDeclNGen_804_ = lean_ctor_get(v___x_801_, 3);
v_traceState_805_ = lean_ctor_get(v___x_801_, 4);
v_cache_806_ = lean_ctor_get(v___x_801_, 5);
v_recordedDeps_807_ = lean_ctor_get(v___x_801_, 6);
v_messages_808_ = lean_ctor_get(v___x_801_, 7);
v_infoState_809_ = lean_ctor_get(v___x_801_, 8);
v_snapshotTasks_810_ = lean_ctor_get(v___x_801_, 9);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v___x_801_, 2);
lean_dec(v_unused_820_);
v___x_812_ = v___x_801_;
v_isShared_813_ = v_isSharedCheck_819_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_snapshotTasks_810_);
lean_inc(v_infoState_809_);
lean_inc(v_messages_808_);
lean_inc(v_recordedDeps_807_);
lean_inc(v_cache_806_);
lean_inc(v_traceState_805_);
lean_inc(v_auxDeclNGen_804_);
lean_inc(v_nextMacroScope_803_);
lean_inc(v_env_802_);
lean_dec(v___x_801_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_819_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 2, v___x_800_);
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_env_802_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_nextMacroScope_803_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v_auxDeclNGen_804_);
lean_ctor_set(v_reuseFailAlloc_818_, 4, v_traceState_805_);
lean_ctor_set(v_reuseFailAlloc_818_, 5, v_cache_806_);
lean_ctor_set(v_reuseFailAlloc_818_, 6, v_recordedDeps_807_);
lean_ctor_set(v_reuseFailAlloc_818_, 7, v_messages_808_);
lean_ctor_set(v_reuseFailAlloc_818_, 8, v_infoState_809_);
lean_ctor_set(v_reuseFailAlloc_818_, 9, v_snapshotTasks_810_);
v___x_815_ = v_reuseFailAlloc_818_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_st_ref_put(v___y_787_, v___x_815_);
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v_r_796_);
return v___x_817_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_787_ = stack[0].m_obj;
lean_object* v_res_823_;
v_res_823_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v___y_787_);
stack->m_obj
 = v_res_823_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg___boxed(lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v___y_824_);
lean_dec(v___y_824_);
return v_res_826_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v___y_830_);
return v___x_832_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_827_ = stack[0].m_obj;
lean_object* v___y_828_ = stack[1].m_obj;
lean_object* v___y_829_ = stack[2].m_obj;
lean_object* v___y_830_ = stack[3].m_obj;
lean_object* v_res_833_;
v_res_833_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(v___y_827_, v___y_828_, v___y_829_, v___y_830_);
stack->m_obj
 = v_res_833_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___boxed(lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
return v_res_839_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0(lean_object* v_u_848_, lean_object* v_00_u03c3s_849_, lean_object* v_H_u2081_x27_850_, lean_object* v_k_851_, lean_object* v_H_u2082_x27_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; lean_object* v_fst_859_; lean_object* v_snd_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_938_; 
lean_inc_ref(v_H_u2082_x27_852_);
lean_inc_ref(v_H_u2081_x27_850_);
lean_inc_ref(v_00_u03c3s_849_);
lean_inc(v_u_848_);
v___x_858_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_848_, v_00_u03c3s_849_, v_H_u2081_x27_850_, v_H_u2082_x27_852_);
v_fst_859_ = lean_ctor_get(v___x_858_, 0);
v_snd_860_ = lean_ctor_get(v___x_858_, 1);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_938_ == 0)
{
v___x_862_ = v___x_858_;
v_isShared_863_ = v_isSharedCheck_938_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_snd_860_);
lean_inc(v_fst_859_);
lean_dec(v___x_858_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_938_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; 
lean_inc(v___y_856_);
lean_inc_ref(v___y_855_);
lean_inc(v___y_854_);
lean_inc_ref(v___y_853_);
lean_inc(v_fst_859_);
v___x_864_ = lean_apply_6(v_k_851_, v_fst_859_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, lean_box(0));
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v_snd_866_; lean_object* v_fst_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_929_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_864_, 1);
v_snd_866_ = lean_ctor_get(v_a_865_, 1);
v_fst_867_ = lean_ctor_get(v_a_865_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v_a_865_);
if (v_isSharedCheck_929_ == 0)
{
v___x_869_ = v_a_865_;
v_isShared_870_ = v_isSharedCheck_929_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_snd_866_);
lean_inc(v_fst_867_);
lean_dec(v_a_865_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_929_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v_fst_871_; lean_object* v_snd_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_928_; 
v_fst_871_ = lean_ctor_get(v_snd_866_, 0);
v_snd_872_ = lean_ctor_get(v_snd_866_, 1);
v_isSharedCheck_928_ = !lean_is_exclusive(v_snd_866_);
if (v_isSharedCheck_928_ == 0)
{
v___x_874_ = v_snd_866_;
v_isShared_875_ = v_isSharedCheck_928_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_snd_872_);
lean_inc(v_fst_871_);
lean_dec(v_snd_866_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_928_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; 
lean_inc(v_fst_871_);
v___x_876_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_871_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_919_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_919_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_919_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_919_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v_fst_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_917_; 
v_fst_881_ = lean_ctor_get(v_a_877_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v_a_877_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; 
v_unused_918_ = lean_ctor_get(v_a_877_, 1);
lean_dec(v_unused_918_);
v___x_883_ = v_a_877_;
v_isShared_884_ = v_isSharedCheck_917_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_fst_881_);
lean_dec(v_a_877_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_917_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v_u_885_; lean_object* v_00_u03c3s_886_; lean_object* v_target_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_915_; 
v_u_885_ = lean_ctor_get(v_fst_871_, 0);
v_00_u03c3s_886_ = lean_ctor_get(v_fst_871_, 1);
v_target_887_ = lean_ctor_get(v_fst_871_, 3);
v_isSharedCheck_915_ = !lean_is_exclusive(v_fst_871_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; 
v_unused_916_ = lean_ctor_get(v_fst_871_, 2);
lean_dec(v_unused_916_);
v___x_889_ = v_fst_871_;
v_isShared_890_ = v_isSharedCheck_915_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_target_887_);
lean_inc(v_00_u03c3s_886_);
lean_inc(v_u_885_);
lean_dec(v_fst_871_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_915_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_891_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1));
v___x_892_ = lean_box(0);
lean_inc(v_u_848_);
if (v_isShared_863_ == 0)
{
lean_ctor_set_tag(v___x_862_, 1);
lean_ctor_set(v___x_862_, 1, v___x_892_);
lean_ctor_set(v___x_862_, 0, v_u_848_);
v___x_894_ = v___x_862_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_u_848_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v___x_892_);
v___x_894_ = v_reuseFailAlloc_914_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_895_ = l_Lean_mkConst(v___x_891_, v___x_894_);
lean_inc_ref(v_target_887_);
lean_inc_ref(v_H_u2082_x27_852_);
lean_inc_ref(v_H_u2081_x27_850_);
lean_inc_n(v_fst_881_, 2);
lean_inc_ref_n(v_00_u03c3s_849_, 2);
v___x_896_ = l_Lean_mkApp8(v___x_895_, v_00_u03c3s_849_, v_fst_881_, v_H_u2081_x27_850_, v_H_u2082_x27_852_, v_fst_859_, v_target_887_, v_snd_860_, v_snd_872_);
lean_inc(v_u_848_);
v___x_897_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_848_, v_00_u03c3s_849_, v_fst_881_, v_H_u2081_x27_850_);
v___x_898_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_848_, v_00_u03c3s_849_, v___x_897_, v_H_u2082_x27_852_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 2, v___x_898_);
v___x_900_ = v___x_889_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_u_885_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_00_u03c3s_886_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_target_887_);
v___x_900_ = v_reuseFailAlloc_913_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_902_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 1, v_fst_881_);
lean_ctor_set(v___x_883_, 0, v_fst_867_);
v___x_902_ = v___x_883_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_fst_867_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_fst_881_);
v___x_902_ = v_reuseFailAlloc_912_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_904_; 
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 1, v___x_896_);
lean_ctor_set(v___x_874_, 0, v___x_900_);
v___x_904_ = v___x_874_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v___x_896_);
v___x_904_ = v_reuseFailAlloc_911_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_906_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 1, v___x_904_);
lean_ctor_set(v___x_869_, 0, v___x_902_);
v___x_906_ = v___x_869_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v___x_904_);
v___x_906_ = v_reuseFailAlloc_910_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_908_; 
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_906_);
v___x_908_ = v___x_879_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
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
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_del_object(v___x_874_);
lean_dec(v_snd_872_);
lean_dec(v_fst_871_);
lean_del_object(v___x_869_);
lean_dec(v_fst_867_);
lean_del_object(v___x_862_);
lean_dec(v_snd_860_);
lean_dec(v_fst_859_);
lean_dec_ref(v_H_u2082_x27_852_);
lean_dec_ref(v_H_u2081_x27_850_);
lean_dec_ref(v_00_u03c3s_849_);
lean_dec(v_u_848_);
v_a_920_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_876_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_876_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_del_object(v___x_862_);
lean_dec(v_snd_860_);
lean_dec(v_fst_859_);
lean_dec_ref(v_H_u2082_x27_852_);
lean_dec_ref(v_H_u2081_x27_850_);
lean_dec_ref(v_00_u03c3s_849_);
lean_dec(v_u_848_);
v_a_930_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_864_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_864_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_848_ = stack[0].m_obj;
lean_object* v_00_u03c3s_849_ = stack[1].m_obj;
lean_object* v_H_u2081_x27_850_ = stack[2].m_obj;
lean_object* v_k_851_ = stack[3].m_obj;
lean_object* v_H_u2082_x27_852_ = stack[4].m_obj;
lean_object* v___y_853_ = stack[5].m_obj;
lean_object* v___y_854_ = stack[6].m_obj;
lean_object* v___y_855_ = stack[7].m_obj;
lean_object* v___y_856_ = stack[8].m_obj;
lean_object* v_res_939_;
v_res_939_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0(v_u_848_, v_00_u03c3s_849_, v_H_u2081_x27_850_, v_k_851_, v_H_u2082_x27_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
stack->m_obj
 = v_res_939_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___boxed(lean_object* v_u_940_, lean_object* v_00_u03c3s_941_, lean_object* v_H_u2081_x27_942_, lean_object* v_k_943_, lean_object* v_H_u2082_x27_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0(v_u_940_, v_00_u03c3s_941_, v_H_u2081_x27_942_, v_k_943_, v_H_u2082_x27_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
return v_res_950_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(lean_object* v_a_953_, lean_object* v_snd_954_, lean_object* v_k_955_, lean_object* v___x_956_, lean_object* v___x_957_, lean_object* v___x_958_, lean_object* v___x_959_, lean_object* v___x_960_, lean_object* v_00_u03c3s_961_, lean_object* v_hyp_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_h_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_lctx_971_; lean_object* v___x_972_; uint8_t v___x_973_; lean_object* v___x_974_; 
v_lctx_971_ = lean_ctor_get(v___y_966_, 2);
lean_inc_ref(v_a_953_);
v___x_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_972_, 0, v_a_953_);
v___x_973_ = 0;
lean_inc_ref(v_h_965_);
lean_inc_ref(v_lctx_971_);
v___x_974_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_snd_954_, v_lctx_971_, v_h_965_, v___x_972_, v___x_973_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v___x_975_; 
lean_dec_ref_known(v___x_974_, 1);
lean_inc(v___y_969_);
lean_inc_ref(v___y_968_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
lean_inc_ref(v_h_965_);
lean_inc_ref(v_a_953_);
v___x_975_ = lean_apply_7(v_k_955_, v_a_953_, v_h_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, lean_box(0));
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v_snd_977_; lean_object* v_fst_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1033_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v_snd_977_ = lean_ctor_get(v_a_976_, 1);
v_fst_978_ = lean_ctor_get(v_a_976_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_a_976_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_980_ = v_a_976_;
v_isShared_981_ = v_isSharedCheck_1033_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_snd_977_);
lean_inc(v_fst_978_);
lean_dec(v_a_976_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1033_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v_fst_982_; lean_object* v_snd_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1032_; 
v_fst_982_ = lean_ctor_get(v_snd_977_, 0);
v_snd_983_ = lean_ctor_get(v_snd_977_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_snd_977_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_985_ = v_snd_977_;
v_isShared_986_ = v_isSharedCheck_1032_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_snd_983_);
lean_inc(v_fst_982_);
lean_dec(v_snd_977_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1032_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; uint8_t v___x_991_; lean_object* v___x_992_; 
v___x_987_ = lean_unsigned_to_nat(1u);
v___x_988_ = lean_mk_empty_array_with_capacity(v___x_987_);
v___x_989_ = lean_array_push(v___x_988_, v_h_965_);
v___x_990_ = 1;
v___x_991_ = 1;
v___x_992_ = l_Lean_Meta_mkLambdaFVars(v___x_989_, v_snd_983_, v___x_973_, v___x_990_, v___x_973_, v___x_990_, v___x_991_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec_ref(v___x_989_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1023_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1023_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1023_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v_u_997_; lean_object* v_00_u03c3s_998_; lean_object* v_hyps_999_; lean_object* v_target_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1022_; 
v_u_997_ = lean_ctor_get(v_fst_982_, 0);
v_00_u03c3s_998_ = lean_ctor_get(v_fst_982_, 1);
v_hyps_999_ = lean_ctor_get(v_fst_982_, 2);
v_target_1000_ = lean_ctor_get(v_fst_982_, 3);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_fst_982_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1002_ = v_fst_982_;
v_isShared_1003_ = v_isSharedCheck_1022_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_target_1000_);
lean_inc(v_hyps_999_);
lean_inc(v_00_u03c3s_998_);
lean_inc(v_u_997_);
lean_dec(v_fst_982_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1022_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v_prf_1008_; lean_object* v___x_1009_; lean_object* v_goal_1011_; 
v___x_1004_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0));
v___x_1005_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1));
v___x_1006_ = l_Lean_Name_mkStr6(v___x_956_, v___x_957_, v___x_958_, v___x_959_, v___x_1004_, v___x_1005_);
v___x_1007_ = l_Lean_mkConst(v___x_1006_, v___x_960_);
lean_inc_ref(v_target_1000_);
lean_inc_ref(v_hyp_962_);
lean_inc_ref(v_hyps_999_);
lean_inc_ref(v_00_u03c3s_961_);
v_prf_1008_ = l_Lean_mkApp7(v___x_1007_, v_00_u03c3s_961_, v_hyps_999_, v_hyp_962_, v_target_1000_, v_a_953_, v_a_963_, v_a_993_);
v___x_1009_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_a_964_, v_00_u03c3s_961_, v_hyps_999_, v_hyp_962_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 2, v___x_1009_);
v_goal_1011_ = v___x_1002_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_u_997_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_00_u03c3s_998_);
lean_ctor_set(v_reuseFailAlloc_1021_, 2, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1021_, 3, v_target_1000_);
v_goal_1011_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1013_; 
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 1, v_prf_1008_);
lean_ctor_set(v___x_985_, 0, v_goal_1011_);
v___x_1013_ = v___x_985_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_goal_1011_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_prf_1008_);
v___x_1013_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1015_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v___x_1013_);
v___x_1015_ = v___x_980_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_fst_978_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1017_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1015_);
v___x_1017_ = v___x_995_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_del_object(v___x_985_);
lean_dec(v_fst_982_);
lean_del_object(v___x_980_);
lean_dec(v_fst_978_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec_ref(v_hyp_962_);
lean_dec_ref(v_00_u03c3s_961_);
lean_dec(v___x_960_);
lean_dec_ref(v___x_959_);
lean_dec_ref(v___x_958_);
lean_dec_ref(v___x_957_);
lean_dec_ref(v___x_956_);
lean_dec_ref(v_a_953_);
v_a_1024_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_992_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_992_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec_ref(v_hyp_962_);
lean_dec_ref(v_00_u03c3s_961_);
lean_dec(v___x_960_);
lean_dec_ref(v___x_959_);
lean_dec_ref(v___x_958_);
lean_dec_ref(v___x_957_);
lean_dec_ref(v___x_956_);
lean_dec_ref(v_a_953_);
return v___x_975_;
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec_ref(v_h_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec_ref(v_hyp_962_);
lean_dec_ref(v_00_u03c3s_961_);
lean_dec(v___x_960_);
lean_dec_ref(v___x_959_);
lean_dec_ref(v___x_958_);
lean_dec_ref(v___x_957_);
lean_dec_ref(v___x_956_);
lean_dec_ref(v_k_955_);
lean_dec_ref(v_a_953_);
v_a_1034_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_974_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_974_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
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
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_953_ = stack[0].m_obj;
lean_object* v_snd_954_ = stack[1].m_obj;
lean_object* v_k_955_ = stack[2].m_obj;
lean_object* v___x_956_ = stack[3].m_obj;
lean_object* v___x_957_ = stack[4].m_obj;
lean_object* v___x_958_ = stack[5].m_obj;
lean_object* v___x_959_ = stack[6].m_obj;
lean_object* v___x_960_ = stack[7].m_obj;
lean_object* v_00_u03c3s_961_ = stack[8].m_obj;
lean_object* v_hyp_962_ = stack[9].m_obj;
lean_object* v_a_963_ = stack[10].m_obj;
lean_object* v_a_964_ = stack[11].m_obj;
lean_object* v_h_965_ = stack[12].m_obj;
lean_object* v___y_966_ = stack[13].m_obj;
lean_object* v___y_967_ = stack[14].m_obj;
lean_object* v___y_968_ = stack[15].m_obj;
lean_object* v___y_969_ = stack[16].m_obj;
lean_object* v_res_1042_;
v_res_1042_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(v_a_953_, v_snd_954_, v_k_955_, v___x_956_, v___x_957_, v___x_958_, v___x_959_, v___x_960_, v_00_u03c3s_961_, v_hyp_962_, v_a_963_, v_a_964_, v_h_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
stack->m_obj
 = v_res_1042_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_a_1043_ = _args[0];
lean_object* v_snd_1044_ = _args[1];
lean_object* v_k_1045_ = _args[2];
lean_object* v___x_1046_ = _args[3];
lean_object* v___x_1047_ = _args[4];
lean_object* v___x_1048_ = _args[5];
lean_object* v___x_1049_ = _args[6];
lean_object* v___x_1050_ = _args[7];
lean_object* v_00_u03c3s_1051_ = _args[8];
lean_object* v_hyp_1052_ = _args[9];
lean_object* v_a_1053_ = _args[10];
lean_object* v_a_1054_ = _args[11];
lean_object* v_h_1055_ = _args[12];
lean_object* v___y_1056_ = _args[13];
lean_object* v___y_1057_ = _args[14];
lean_object* v___y_1058_ = _args[15];
lean_object* v___y_1059_ = _args[16];
lean_object* v___y_1060_ = _args[17];
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(v_a_1043_, v_snd_1044_, v_k_1045_, v___x_1046_, v___x_1047_, v___x_1048_, v___x_1049_, v___x_1050_, v_00_u03c3s_1051_, v_hyp_1052_, v_a_1053_, v_a_1054_, v_h_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
return v_res_1061_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_box(0);
v___x_1063_ = l_Lean_mkSort(v___x_1062_);
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0);
v___x_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
return v___x_1065_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(lean_object* v_00_u03c3s_1073_, lean_object* v_hyp_1074_, lean_object* v_name_1075_, lean_object* v_k_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v___x_1082_, 1);
v___x_1084_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1);
v___x_1085_ = 0;
v___x_1086_ = lean_box(0);
v___x_1087_ = l_Lean_Meta_mkFreshExprMVar(v___x_1084_, v___x_1085_, v___x_1086_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc_n(v_a_1088_, 2);
lean_dec_ref_known(v___x_1087_, 1);
v___x_1089_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0));
v___x_1090_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_1091_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1));
v___x_1092_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_1093_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3));
v___x_1094_ = lean_box(0);
lean_inc(v_a_1083_);
v___x_1095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1095_, 0, v_a_1083_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
lean_inc_ref(v___x_1095_);
v___x_1096_ = l_Lean_mkConst(v___x_1093_, v___x_1095_);
lean_inc_ref(v_hyp_1074_);
lean_inc_ref(v_00_u03c3s_1073_);
v___x_1097_ = l_Lean_mkApp3(v___x_1096_, v_00_u03c3s_1073_, v_hyp_1074_, v_a_1088_);
v___x_1098_ = lean_box(0);
v___x_1099_ = l_Lean_Meta_synthInstance(v___x_1097_, v___x_1098_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1101_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1099_, 1);
v___x_1101_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_name_1075_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v_fst_1103_; lean_object* v_snd_1104_; lean_object* v___f_1105_; lean_object* v___x_1106_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v___x_1101_, 1);
v_fst_1103_ = lean_ctor_get(v_a_1102_, 0);
lean_inc(v_fst_1103_);
v_snd_1104_ = lean_ctor_get(v_a_1102_, 1);
lean_inc(v_snd_1104_);
lean_dec(v_a_1102_);
lean_inc(v_a_1088_);
v___f_1105_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1105_, 0, v_a_1088_);
lean_closure_set(v___f_1105_, 1, v_snd_1104_);
lean_closure_set(v___f_1105_, 2, v_k_1076_);
lean_closure_set(v___f_1105_, 3, v___x_1089_);
lean_closure_set(v___f_1105_, 4, v___x_1090_);
lean_closure_set(v___f_1105_, 5, v___x_1091_);
lean_closure_set(v___f_1105_, 6, v___x_1092_);
lean_closure_set(v___f_1105_, 7, v___x_1095_);
lean_closure_set(v___f_1105_, 8, v_00_u03c3s_1073_);
lean_closure_set(v___f_1105_, 9, v_hyp_1074_);
lean_closure_set(v___f_1105_, 10, v_a_1100_);
lean_closure_set(v___f_1105_, 11, v_a_1083_);
v___x_1106_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_fst_1103_, v_a_1088_, v___f_1105_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1106_;
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec(v_a_1100_);
lean_dec_ref_known(v___x_1095_, 2);
lean_dec(v_a_1088_);
lean_dec(v_a_1083_);
lean_dec_ref(v_k_1076_);
lean_dec_ref(v_hyp_1074_);
lean_dec_ref(v_00_u03c3s_1073_);
v_a_1107_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1101_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1101_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec_ref_known(v___x_1095_, 2);
lean_dec(v_a_1088_);
lean_dec(v_a_1083_);
lean_dec_ref(v_k_1076_);
lean_dec(v_name_1075_);
lean_dec_ref(v_hyp_1074_);
lean_dec_ref(v_00_u03c3s_1073_);
v_a_1115_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1099_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1099_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec(v_a_1083_);
lean_dec_ref(v_k_1076_);
lean_dec(v_name_1075_);
lean_dec_ref(v_hyp_1074_);
lean_dec_ref(v_00_u03c3s_1073_);
v_a_1123_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1087_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1087_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec_ref(v_k_1076_);
lean_dec(v_name_1075_);
lean_dec_ref(v_hyp_1074_);
lean_dec_ref(v_00_u03c3s_1073_);
v_a_1131_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1082_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1082_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03c3s_1073_ = stack[0].m_obj;
lean_object* v_hyp_1074_ = stack[1].m_obj;
lean_object* v_name_1075_ = stack[2].m_obj;
lean_object* v_k_1076_ = stack[3].m_obj;
lean_object* v___y_1077_ = stack[4].m_obj;
lean_object* v___y_1078_ = stack[5].m_obj;
lean_object* v___y_1079_ = stack[6].m_obj;
lean_object* v___y_1080_ = stack[7].m_obj;
lean_object* v_res_1139_;
v_res_1139_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1073_, v_hyp_1074_, v_name_1075_, v_k_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
stack->m_obj
 = v_res_1139_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___boxed(lean_object* v_00_u03c3s_1140_, lean_object* v_hyp_1141_, lean_object* v_name_1142_, lean_object* v_k_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1140_, v_hyp_1141_, v_name_1142_, v_k_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
return v_res_1149_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(lean_object* v_u_1158_, lean_object* v_00_u03c3s_1159_, lean_object* v_k_1160_, lean_object* v_x_1161_, lean_object* v___h_u03c6_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_H_x27_1168_; lean_object* v___x_1169_; 
lean_inc_ref(v_00_u03c3s_1159_);
lean_inc(v_u_1158_);
v_H_x27_1168_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_1158_, v_00_u03c3s_1159_);
lean_inc(v___y_1166_);
lean_inc_ref(v___y_1165_);
lean_inc(v___y_1164_);
lean_inc_ref(v___y_1163_);
v___x_1169_ = lean_apply_6(v_k_1160_, v_H_x27_1168_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, lean_box(0));
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v_snd_1171_; lean_object* v_fst_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1229_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 1);
v_snd_1171_ = lean_ctor_get(v_a_1170_, 1);
v_fst_1172_ = lean_ctor_get(v_a_1170_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_a_1170_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1174_ = v_a_1170_;
v_isShared_1175_ = v_isSharedCheck_1229_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_snd_1171_);
lean_inc(v_fst_1172_);
lean_dec(v_a_1170_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1229_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_fst_1176_; lean_object* v_snd_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1228_; 
v_fst_1176_ = lean_ctor_get(v_snd_1171_, 0);
v_snd_1177_ = lean_ctor_get(v_snd_1171_, 1);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_snd_1171_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1179_ = v_snd_1171_;
v_isShared_1180_ = v_isSharedCheck_1228_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_snd_1177_);
lean_inc(v_fst_1176_);
lean_dec(v_snd_1171_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1228_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; 
lean_inc(v_fst_1176_);
v___x_1181_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_1176_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1219_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1219_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1219_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v_fst_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1217_; 
v_fst_1186_ = lean_ctor_get(v_a_1182_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_a_1182_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; 
v_unused_1218_ = lean_ctor_get(v_a_1182_, 1);
lean_dec(v_unused_1218_);
v___x_1188_ = v_a_1182_;
v_isShared_1189_ = v_isSharedCheck_1217_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_fst_1186_);
lean_dec(v_a_1182_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1217_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_u_1190_; lean_object* v_00_u03c3s_1191_; lean_object* v_target_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1215_; 
v_u_1190_ = lean_ctor_get(v_fst_1176_, 0);
v_00_u03c3s_1191_ = lean_ctor_get(v_fst_1176_, 1);
v_target_1192_ = lean_ctor_get(v_fst_1176_, 3);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_fst_1176_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v_fst_1176_, 2);
lean_dec(v_unused_1216_);
v___x_1194_ = v_fst_1176_;
v_isShared_1195_ = v_isSharedCheck_1215_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_target_1192_);
lean_inc(v_00_u03c3s_1191_);
lean_inc(v_u_1190_);
lean_dec(v_fst_1176_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1215_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1196_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1));
v___x_1197_ = lean_box(0);
if (v_isShared_1175_ == 0)
{
lean_ctor_set_tag(v___x_1174_, 1);
lean_ctor_set(v___x_1174_, 1, v___x_1197_);
lean_ctor_set(v___x_1174_, 0, v_u_1158_);
v___x_1199_ = v___x_1174_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_u_1158_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1200_ = l_Lean_mkConst(v___x_1196_, v___x_1199_);
lean_inc_ref(v_target_1192_);
lean_inc(v_fst_1186_);
v___x_1201_ = l_Lean_mkApp4(v___x_1200_, v_00_u03c3s_1159_, v_fst_1186_, v_target_1192_, v_snd_1177_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 2, v_fst_1186_);
v___x_1203_ = v___x_1194_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_u_1190_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_00_u03c3s_1191_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v_fst_1186_);
lean_ctor_set(v_reuseFailAlloc_1213_, 3, v_target_1192_);
v___x_1203_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1205_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 1, v___x_1201_);
lean_ctor_set(v___x_1188_, 0, v___x_1203_);
v___x_1205_ = v___x_1188_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___x_1201_);
v___x_1205_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1207_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 1, v___x_1205_);
lean_ctor_set(v___x_1179_, 0, v_fst_1172_);
v___x_1207_ = v___x_1179_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_fst_1172_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1209_; 
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1207_);
v___x_1209_ = v___x_1184_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
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
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_del_object(v___x_1179_);
lean_dec(v_snd_1177_);
lean_dec(v_fst_1176_);
lean_del_object(v___x_1174_);
lean_dec(v_fst_1172_);
lean_dec_ref(v_00_u03c3s_1159_);
lean_dec(v_u_1158_);
v_a_1220_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1181_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1181_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_00_u03c3s_1159_);
lean_dec(v_u_1158_);
return v___x_1169_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1158_ = stack[0].m_obj;
lean_object* v_00_u03c3s_1159_ = stack[1].m_obj;
lean_object* v_k_1160_ = stack[2].m_obj;
lean_object* v_x_1161_ = stack[3].m_obj;
lean_object* v___h_u03c6_1162_ = stack[4].m_obj;
lean_object* v___y_1163_ = stack[5].m_obj;
lean_object* v___y_1164_ = stack[6].m_obj;
lean_object* v___y_1165_ = stack[7].m_obj;
lean_object* v___y_1166_ = stack[8].m_obj;
lean_object* v_res_1230_;
v_res_1230_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(v_u_1158_, v_00_u03c3s_1159_, v_k_1160_, v_x_1161_, v___h_u03c6_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
stack->m_obj
 = v_res_1230_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___boxed(lean_object* v_u_1231_, lean_object* v_00_u03c3s_1232_, lean_object* v_k_1233_, lean_object* v_x_1234_, lean_object* v___h_u03c6_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(v_u_1231_, v_00_u03c3s_1232_, v_k_1233_, v_x_1234_, v___h_u03c6_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec_ref(v___h_u03c6_1235_);
lean_dec_ref(v_x_1234_);
return v_res_1241_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(lean_object* v_u_1258_, lean_object* v_00_u03c3s_1259_, lean_object* v_k_1260_, lean_object* v_tail_1261_, lean_object* v_fst_1262_, lean_object* v_H_u2081_x27_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___f_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_inc_ref(v_H_u2081_x27_1263_);
lean_inc_ref_n(v_00_u03c3s_1259_, 2);
lean_inc_n(v_u_1258_, 2);
v___f_1269_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1269_, 0, v_u_1258_);
lean_closure_set(v___f_1269_, 1, v_00_u03c3s_1259_);
lean_closure_set(v___f_1269_, 2, v_H_u2081_x27_1263_);
lean_closure_set(v___f_1269_, 3, v_k_1260_);
v___x_1270_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1270_, 0, v_tail_1261_);
lean_inc_ref(v_fst_1262_);
v___x_1271_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1258_, v_00_u03c3s_1259_, v_fst_1262_, v___x_1270_, v___f_1269_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1317_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1317_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1317_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v_fst_1276_; lean_object* v_snd_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1316_; 
v_fst_1276_ = lean_ctor_get(v_a_1272_, 0);
v_snd_1277_ = lean_ctor_get(v_a_1272_, 1);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_a_1272_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1279_ = v_a_1272_;
v_isShared_1280_ = v_isSharedCheck_1316_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_snd_1277_);
lean_inc(v_fst_1276_);
lean_dec(v_a_1272_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1316_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v_fst_1281_; lean_object* v_snd_1282_; lean_object* v_snd_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1314_; 
v_fst_1281_ = lean_ctor_get(v_snd_1277_, 0);
lean_inc(v_fst_1281_);
v_snd_1282_ = lean_ctor_get(v_fst_1276_, 1);
v_snd_1283_ = lean_ctor_get(v_snd_1277_, 1);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_snd_1277_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; 
v_unused_1315_ = lean_ctor_get(v_snd_1277_, 0);
lean_dec(v_unused_1315_);
v___x_1285_ = v_snd_1277_;
v_isShared_1286_ = v_isSharedCheck_1314_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_snd_1283_);
lean_dec(v_snd_1277_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1314_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_u_1287_; lean_object* v_00_u03c3s_1288_; lean_object* v_target_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1312_; 
v_u_1287_ = lean_ctor_get(v_fst_1281_, 0);
v_00_u03c3s_1288_ = lean_ctor_get(v_fst_1281_, 1);
v_target_1289_ = lean_ctor_get(v_fst_1281_, 3);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_fst_1281_);
if (v_isSharedCheck_1312_ == 0)
{
lean_object* v_unused_1313_; 
v_unused_1313_ = lean_ctor_get(v_fst_1281_, 2);
lean_dec(v_unused_1313_);
v___x_1291_ = v_fst_1281_;
v_isShared_1292_ = v_isSharedCheck_1312_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_target_1289_);
lean_inc(v_00_u03c3s_1288_);
lean_inc(v_u_1287_);
lean_dec(v_fst_1281_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1312_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1293_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1));
v___x_1294_ = lean_box(0);
lean_inc_n(v_u_1258_, 2);
v___x_1295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1295_, 0, v_u_1258_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
v___x_1296_ = l_Lean_mkConst(v___x_1293_, v___x_1295_);
lean_inc_ref(v_target_1289_);
lean_inc_ref(v_fst_1262_);
lean_inc_ref(v_H_u2081_x27_1263_);
lean_inc_n(v_snd_1282_, 2);
lean_inc_ref_n(v_00_u03c3s_1259_, 2);
v___x_1297_ = l_Lean_mkApp6(v___x_1296_, v_00_u03c3s_1259_, v_snd_1282_, v_H_u2081_x27_1263_, v_fst_1262_, v_target_1289_, v_snd_1283_);
v___x_1298_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1258_, v_00_u03c3s_1259_, v_snd_1282_, v_fst_1262_);
v___x_1299_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1258_, v_00_u03c3s_1259_, v___x_1298_, v_H_u2081_x27_1263_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 2, v___x_1299_);
v___x_1301_ = v___x_1291_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_u_1287_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_00_u03c3s_1288_);
lean_ctor_set(v_reuseFailAlloc_1311_, 2, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1311_, 3, v_target_1289_);
v___x_1301_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1303_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1297_);
lean_ctor_set(v___x_1285_, 0, v___x_1301_);
v___x_1303_ = v___x_1285_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v___x_1297_);
v___x_1303_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1305_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 1, v___x_1303_);
v___x_1305_ = v___x_1279_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_fst_1276_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1307_; 
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1305_);
v___x_1307_ = v___x_1274_;
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
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_H_u2081_x27_1263_);
lean_dec_ref(v_fst_1262_);
lean_dec_ref(v_00_u03c3s_1259_);
lean_dec(v_u_1258_);
return v___x_1271_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1258_ = stack[0].m_obj;
lean_object* v_00_u03c3s_1259_ = stack[1].m_obj;
lean_object* v_k_1260_ = stack[2].m_obj;
lean_object* v_tail_1261_ = stack[3].m_obj;
lean_object* v_fst_1262_ = stack[4].m_obj;
lean_object* v_H_u2081_x27_1263_ = stack[5].m_obj;
lean_object* v___y_1264_ = stack[6].m_obj;
lean_object* v___y_1265_ = stack[7].m_obj;
lean_object* v___y_1266_ = stack[8].m_obj;
lean_object* v___y_1267_ = stack[9].m_obj;
lean_object* v_res_1318_;
v_res_1318_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(v_u_1258_, v_00_u03c3s_1259_, v_k_1260_, v_tail_1261_, v_fst_1262_, v_H_u2081_x27_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
stack->m_obj
 = v_res_1318_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___boxed(lean_object* v_u_1319_, lean_object* v_00_u03c3s_1320_, lean_object* v_k_1321_, lean_object* v_tail_1322_, lean_object* v_fst_1323_, lean_object* v_H_u2081_x27_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(v_u_1319_, v_00_u03c3s_1320_, v_k_1321_, v_tail_1322_, v_fst_1323_, v_H_u2081_x27_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
return v_res_1330_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4));
v___x_1341_ = l_Lean_stringToMessageData(v___x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2___boxed(lean_object* v___x_1342_, lean_object* v_tail_1343_, lean_object* v_u_1344_, lean_object* v___x_1345_, lean_object* v_k_1346_, lean_object* v_x_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2(v___x_1342_, v_tail_1343_, v_u_1344_, v___x_1345_, v_k_1346_, v_x_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
return v_res_1353_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6));
v___x_1356_ = l_Lean_stringToMessageData(v___x_1355_);
return v___x_1356_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10));
v___x_1365_ = l_Lean_stringToMessageData(v___x_1364_);
return v___x_1365_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(lean_object* v_u_1372_, lean_object* v_00_u03c3s_1373_, lean_object* v_H_1374_, lean_object* v_pat_1375_, lean_object* v_k_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
switch(lean_obj_tag(v_pat_1375_))
{
case 0:
{
lean_object* v_name_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1429_; 
v_name_1382_ = lean_ctor_get(v_pat_1375_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_pat_1375_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1384_ = v_pat_1375_;
v_isShared_1385_ = v_isSharedCheck_1429_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_name_1382_);
lean_dec(v_pat_1375_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1429_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___y_1387_; uint8_t v___y_1388_; lean_object* v___y_1394_; lean_object* v_a_1395_; lean_object* v___x_1398_; uint8_t v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1398_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1);
v___x_1399_ = 0;
v___x_1400_ = lean_box(0);
v___x_1401_ = l_Lean_Meta_mkFreshExprMVar(v___x_1398_, v___x_1399_, v___x_1400_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref_known(v___x_1401_, 1);
v___x_1403_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3));
v___x_1404_ = lean_box(0);
lean_inc(v_u_1372_);
v___x_1405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1405_, 0, v_u_1372_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
v___x_1406_ = l_Lean_mkConst(v___x_1403_, v___x_1405_);
lean_inc_ref(v_H_1374_);
lean_inc_ref(v_00_u03c3s_1373_);
v___x_1407_ = l_Lean_mkApp3(v___x_1406_, v_00_u03c3s_1373_, v_H_1374_, v_a_1402_);
v___x_1408_ = lean_box(0);
v___x_1409_ = l_Lean_Meta_synthInstance(v___x_1407_, v___x_1408_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
lean_dec_ref_known(v___x_1409_, 1);
lean_inc(v_name_1382_);
v___x_1410_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1410_, 0, v_name_1382_);
lean_inc_ref(v_k_1376_);
lean_inc_ref(v_H_1374_);
lean_inc_ref(v_00_u03c3s_1373_);
lean_inc(v_u_1372_);
v___x_1411_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1372_, v_00_u03c3s_1373_, v_H_1374_, v___x_1410_, v_k_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_del_object(v___x_1384_);
lean_dec(v_name_1382_);
lean_dec_ref(v_k_1376_);
lean_dec_ref(v_H_1374_);
lean_dec_ref(v_00_u03c3s_1373_);
lean_dec(v_u_1372_);
return v___x_1411_;
}
else
{
lean_object* v_a_1412_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
v___y_1394_ = v___x_1411_;
v_a_1395_ = v_a_1412_;
goto v___jp_1393_;
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
v_a_1413_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1409_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1409_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
lean_inc(v_a_1413_);
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
v___y_1394_ = v___x_1418_;
v_a_1395_ = v_a_1413_;
goto v___jp_1393_;
}
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
v_a_1421_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1401_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1401_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
lean_inc(v_a_1421_);
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
v___y_1394_ = v___x_1426_;
v_a_1395_ = v_a_1421_;
goto v___jp_1393_;
}
}
}
v___jp_1386_:
{
if (v___y_1388_ == 0)
{
lean_object* v___x_1390_; 
lean_dec_ref(v___y_1387_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set_tag(v___x_1384_, 5);
v___x_1390_ = v___x_1384_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_name_1382_);
v___x_1390_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
v_pat_1375_ = v___x_1390_;
goto _start;
}
}
else
{
lean_del_object(v___x_1384_);
lean_dec(v_name_1382_);
lean_dec_ref(v_k_1376_);
lean_dec_ref(v_H_1374_);
lean_dec_ref(v_00_u03c3s_1373_);
lean_dec(v_u_1372_);
return v___y_1387_;
}
}
v___jp_1393_:
{
uint8_t v___x_1396_; 
v___x_1396_ = l_Lean_Exception_isInterrupt(v_a_1395_);
if (v___x_1396_ == 0)
{
uint8_t v___x_1397_; 
v___x_1397_ = l_Lean_Exception_isRuntime(v_a_1395_);
v___y_1387_ = v___y_1394_;
v___y_1388_ = v___x_1397_;
goto v___jp_1386_;
}
else
{
lean_dec_ref(v_a_1395_);
v___y_1387_ = v___y_1394_;
v___y_1388_ = v___x_1396_;
goto v___jp_1386_;
}
}
}
}
case 1:
{
lean_object* v_H_x27_1430_; lean_object* v___x_1431_; 
lean_inc_ref(v_00_u03c3s_1373_);
lean_inc(v_u_1372_);
v_H_x27_1430_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_1372_, v_00_u03c3s_1373_);
lean_inc(v_a_1380_);
lean_inc_ref(v_a_1379_);
lean_inc(v_a_1378_);
lean_inc_ref(v_a_1377_);
v___x_1431_ = lean_apply_6(v_k_1376_, v_H_x27_1430_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, lean_box(0));
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v_snd_1433_; lean_object* v_fst_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1492_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v_snd_1433_ = lean_ctor_get(v_a_1432_, 1);
v_fst_1434_ = lean_ctor_get(v_a_1432_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_a_1432_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1436_ = v_a_1432_;
v_isShared_1437_ = v_isSharedCheck_1492_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_snd_1433_);
lean_inc(v_fst_1434_);
lean_dec(v_a_1432_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1492_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v_fst_1438_; lean_object* v_snd_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1491_; 
v_fst_1438_ = lean_ctor_get(v_snd_1433_, 0);
v_snd_1439_ = lean_ctor_get(v_snd_1433_, 1);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_snd_1433_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1441_ = v_snd_1433_;
v_isShared_1442_ = v_isSharedCheck_1491_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_snd_1439_);
lean_inc(v_fst_1438_);
lean_dec(v_snd_1433_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1491_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; 
lean_inc(v_fst_1438_);
v___x_1443_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_1438_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1482_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1446_ = v___x_1443_;
v_isShared_1447_ = v_isSharedCheck_1482_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1443_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1482_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v_fst_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1480_; 
v_fst_1448_ = lean_ctor_get(v_a_1444_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_a_1444_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; 
v_unused_1481_ = lean_ctor_get(v_a_1444_, 1);
lean_dec(v_unused_1481_);
v___x_1450_ = v_a_1444_;
v_isShared_1451_ = v_isSharedCheck_1480_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_fst_1448_);
lean_dec(v_a_1444_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1480_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v_u_1452_; lean_object* v_00_u03c3s_1453_; lean_object* v_target_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1478_; 
v_u_1452_ = lean_ctor_get(v_fst_1438_, 0);
v_00_u03c3s_1453_ = lean_ctor_get(v_fst_1438_, 1);
v_target_1454_ = lean_ctor_get(v_fst_1438_, 3);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_fst_1438_);
if (v_isSharedCheck_1478_ == 0)
{
lean_object* v_unused_1479_; 
v_unused_1479_ = lean_ctor_get(v_fst_1438_, 2);
lean_dec(v_unused_1479_);
v___x_1456_ = v_fst_1438_;
v_isShared_1457_ = v_isSharedCheck_1478_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_target_1454_);
lean_inc(v_00_u03c3s_1453_);
lean_inc(v_u_1452_);
lean_dec(v_fst_1438_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1478_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1458_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1));
v___x_1459_ = lean_box(0);
lean_inc(v_u_1372_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set_tag(v___x_1436_, 1);
lean_ctor_set(v___x_1436_, 1, v___x_1459_);
lean_ctor_set(v___x_1436_, 0, v_u_1372_);
v___x_1461_ = v___x_1436_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_u_1372_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1462_ = l_Lean_mkConst(v___x_1458_, v___x_1461_);
lean_inc_ref(v_target_1454_);
lean_inc_ref(v_H_1374_);
lean_inc(v_fst_1448_);
lean_inc_ref(v_00_u03c3s_1373_);
v___x_1463_ = l_Lean_mkApp5(v___x_1462_, v_00_u03c3s_1373_, v_fst_1448_, v_H_1374_, v_target_1454_, v_snd_1439_);
v___x_1464_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1372_, v_00_u03c3s_1373_, v_fst_1448_, v_H_1374_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 2, v___x_1464_);
v___x_1466_ = v___x_1456_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_u_1452_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_00_u03c3s_1453_);
lean_ctor_set(v_reuseFailAlloc_1476_, 2, v___x_1464_);
lean_ctor_set(v_reuseFailAlloc_1476_, 3, v_target_1454_);
v___x_1466_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1468_; 
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 1, v___x_1463_);
lean_ctor_set(v___x_1450_, 0, v___x_1466_);
v___x_1468_ = v___x_1450_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v___x_1463_);
v___x_1468_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1470_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 1, v___x_1468_);
lean_ctor_set(v___x_1441_, 0, v_fst_1434_);
v___x_1470_ = v___x_1441_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_fst_1434_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1472_; 
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v___x_1470_);
v___x_1472_ = v___x_1446_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
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
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_del_object(v___x_1441_);
lean_dec(v_snd_1439_);
lean_dec(v_fst_1438_);
lean_del_object(v___x_1436_);
lean_dec(v_fst_1434_);
lean_dec_ref(v_H_1374_);
lean_dec_ref(v_00_u03c3s_1373_);
lean_dec(v_u_1372_);
v_a_1483_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1443_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1443_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_H_1374_);
lean_dec_ref(v_00_u03c3s_1373_);
lean_dec(v_u_1372_);
return v___x_1431_;
}
}
case 2:
{
lean_object* v_args_1493_; 
v_args_1493_ = lean_ctor_get(v_pat_1375_, 0);
lean_inc(v_args_1493_);
lean_dec_ref_known(v_pat_1375_, 1);
if (lean_obj_tag(v_args_1493_) == 0)
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_box(1);
v_pat_1375_ = v___x_1494_;
goto _start;
}
else
{
lean_object* v_tail_1496_; 
v_tail_1496_ = lean_ctor_get(v_args_1493_, 1);
if (lean_obj_tag(v_tail_1496_) == 0)
{
lean_object* v_head_1497_; 
v_head_1497_ = lean_ctor_get(v_args_1493_, 0);
lean_inc(v_head_1497_);
lean_dec_ref_known(v_args_1493_, 2);
v_pat_1375_ = v_head_1497_;
goto _start;
}
else
{
lean_object* v_head_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1592_; 
lean_inc(v_tail_1496_);
v_head_1499_ = lean_ctor_get(v_args_1493_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_args_1493_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; 
v_unused_1593_ = lean_ctor_get(v_args_1493_, 1);
lean_dec(v_unused_1593_);
v___x_1501_ = v_args_1493_;
v_isShared_1502_ = v_isSharedCheck_1592_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_head_1499_);
lean_dec(v_args_1493_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1592_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; 
lean_inc_ref(v_H_1374_);
lean_inc_ref(v_00_u03c3s_1373_);
lean_inc(v_u_1372_);
v___x_1503_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(v_u_1372_, v_00_u03c3s_1373_, v_H_1374_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1503_, 1);
if (lean_obj_tag(v_a_1504_) == 1)
{
lean_object* v_val_1505_; lean_object* v_snd_1506_; lean_object* v_fst_1507_; lean_object* v_fst_1508_; lean_object* v_snd_1509_; lean_object* v___f_1510_; lean_object* v___x_1511_; 
v_val_1505_ = lean_ctor_get(v_a_1504_, 0);
lean_inc(v_val_1505_);
lean_dec_ref_known(v_a_1504_, 1);
v_snd_1506_ = lean_ctor_get(v_val_1505_, 1);
lean_inc(v_snd_1506_);
v_fst_1507_ = lean_ctor_get(v_val_1505_, 0);
lean_inc_n(v_fst_1507_, 2);
lean_dec(v_val_1505_);
v_fst_1508_ = lean_ctor_get(v_snd_1506_, 0);
lean_inc_n(v_fst_1508_, 2);
v_snd_1509_ = lean_ctor_get(v_snd_1506_, 1);
lean_inc(v_snd_1509_);
lean_dec(v_snd_1506_);
lean_inc_ref_n(v_00_u03c3s_1373_, 2);
lean_inc_n(v_u_1372_, 2);
v___f_1510_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___boxed), 11, 5);
lean_closure_set(v___f_1510_, 0, v_u_1372_);
lean_closure_set(v___f_1510_, 1, v_00_u03c3s_1373_);
lean_closure_set(v___f_1510_, 2, v_k_1376_);
lean_closure_set(v___f_1510_, 3, v_tail_1496_);
lean_closure_set(v___f_1510_, 4, v_fst_1508_);
v___x_1511_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1372_, v_00_u03c3s_1373_, v_fst_1507_, v_head_1499_, v___f_1510_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1559_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1514_ = v___x_1511_;
v_isShared_1515_ = v_isSharedCheck_1559_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1559_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v_fst_1516_; lean_object* v_snd_1517_; lean_object* v_fst_1518_; lean_object* v_fst_1519_; lean_object* v_snd_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1558_; 
v_fst_1516_ = lean_ctor_get(v_a_1512_, 0);
lean_inc(v_fst_1516_);
v_snd_1517_ = lean_ctor_get(v_a_1512_, 1);
lean_inc(v_snd_1517_);
lean_dec(v_a_1512_);
v_fst_1518_ = lean_ctor_get(v_snd_1517_, 0);
lean_inc(v_fst_1518_);
v_fst_1519_ = lean_ctor_get(v_fst_1516_, 0);
v_snd_1520_ = lean_ctor_get(v_fst_1516_, 1);
v_isSharedCheck_1558_ = !lean_is_exclusive(v_fst_1516_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1522_ = v_fst_1516_;
v_isShared_1523_ = v_isSharedCheck_1558_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_snd_1520_);
lean_inc(v_fst_1519_);
lean_dec(v_fst_1516_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1558_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v_snd_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1556_; 
v_snd_1524_ = lean_ctor_get(v_snd_1517_, 1);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_snd_1517_);
if (v_isSharedCheck_1556_ == 0)
{
lean_object* v_unused_1557_; 
v_unused_1557_ = lean_ctor_get(v_snd_1517_, 0);
lean_dec(v_unused_1557_);
v___x_1526_ = v_snd_1517_;
v_isShared_1527_ = v_isSharedCheck_1556_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_snd_1524_);
lean_dec(v_snd_1517_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1556_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v_u_1528_; lean_object* v_00_u03c3s_1529_; lean_object* v_target_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1554_; 
v_u_1528_ = lean_ctor_get(v_fst_1518_, 0);
v_00_u03c3s_1529_ = lean_ctor_get(v_fst_1518_, 1);
v_target_1530_ = lean_ctor_get(v_fst_1518_, 3);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_fst_1518_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; 
v_unused_1555_ = lean_ctor_get(v_fst_1518_, 2);
lean_dec(v_unused_1555_);
v___x_1532_ = v_fst_1518_;
v_isShared_1533_ = v_isSharedCheck_1554_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_target_1530_);
lean_inc(v_00_u03c3s_1529_);
lean_inc(v_u_1528_);
lean_dec(v_fst_1518_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1554_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1537_; 
v___x_1534_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3));
v___x_1535_ = lean_box(0);
lean_inc(v_u_1372_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 1, v___x_1535_);
lean_ctor_set(v___x_1501_, 0, v_u_1372_);
v___x_1537_ = v___x_1501_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_u_1372_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1538_ = l_Lean_mkConst(v___x_1534_, v___x_1537_);
lean_inc_ref(v_target_1530_);
lean_inc_ref(v_H_1374_);
lean_inc(v_snd_1520_);
lean_inc_ref(v_00_u03c3s_1373_);
v___x_1539_ = l_Lean_mkApp8(v___x_1538_, v_00_u03c3s_1373_, v_snd_1520_, v_fst_1507_, v_fst_1508_, v_H_1374_, v_target_1530_, v_snd_1509_, v_snd_1524_);
v___x_1540_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1372_, v_00_u03c3s_1373_, v_snd_1520_, v_H_1374_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 2, v___x_1540_);
v___x_1542_ = v___x_1532_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_u_1528_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_00_u03c3s_1529_);
lean_ctor_set(v_reuseFailAlloc_1552_, 2, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1552_, 3, v_target_1530_);
v___x_1542_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1544_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 1, v___x_1539_);
lean_ctor_set(v___x_1526_, 0, v___x_1542_);
v___x_1544_ = v___x_1526_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v___x_1539_);
v___x_1544_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1546_; 
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 1, v___x_1544_);
v___x_1546_ = v___x_1522_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_fst_1519_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1548_; 
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v___x_1546_);
v___x_1548_ = v___x_1514_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
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
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec(v_snd_1509_);
lean_dec(v_fst_1508_);
lean_dec(v_fst_1507_);
lean_del_object(v___x_1501_);
lean_dec_ref(v_H_1374_);
lean_dec_ref(v_00_u03c3s_1373_);
lean_dec(v_u_1372_);
v_a_1560_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1511_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1511_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
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
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
lean_dec(v_a_1504_);
lean_del_object(v___x_1501_);
lean_dec_ref(v_00_u03c3s_1373_);
v___x_1568_ = l_Lean_Expr_consumeMData(v_H_1374_);
v___x_1569_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1));
v___x_1570_ = lean_unsigned_to_nat(3u);
v___x_1571_ = l_Lean_Expr_isAppOfArity(v___x_1568_, v___x_1569_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_dec_ref(v___x_1568_);
lean_dec(v_head_1499_);
lean_dec(v_tail_1496_);
lean_dec_ref(v_k_1376_);
lean_dec(v_u_1372_);
v___x_1572_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5);
v___x_1573_ = l_Lean_MessageData_ofExpr(v_H_1374_);
v___x_1574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1572_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_1574_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
return v___x_1575_;
}
else
{
if (lean_obj_tag(v_head_1499_) == 0)
{
lean_object* v_name_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___f_1580_; lean_object* v___x_1581_; 
v_name_1576_ = lean_ctor_get(v_head_1499_, 0);
lean_inc(v_name_1576_);
lean_dec_ref_known(v_head_1499_, 1);
v___x_1577_ = l_Lean_Expr_appFn_x21(v___x_1568_);
v___x_1578_ = l_Lean_Expr_appArg_x21(v___x_1577_);
lean_dec_ref(v___x_1577_);
v___x_1579_ = l_Lean_Expr_appArg_x21(v___x_1568_);
lean_dec_ref(v___x_1568_);
v___f_1580_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2___boxed), 11, 5);
lean_closure_set(v___f_1580_, 0, v___x_1579_);
lean_closure_set(v___f_1580_, 1, v_tail_1496_);
lean_closure_set(v___f_1580_, 2, v_u_1372_);
lean_closure_set(v___f_1580_, 3, v___x_1578_);
lean_closure_set(v___f_1580_, 4, v_k_1376_);
v___x_1581_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(v_H_1374_, v_name_1576_, v___f_1580_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
return v___x_1581_;
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec_ref(v___x_1568_);
lean_dec(v_head_1499_);
lean_dec(v_tail_1496_);
lean_dec_ref(v_k_1376_);
lean_dec_ref(v_H_1374_);
lean_dec(v_u_1372_);
v___x_1582_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7);
v___x_1583_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_1582_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
return v___x_1583_;
}
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_del_object(v___x_1501_);
lean_dec(v_head_1499_);
lean_dec(v_tail_1496_);
lean_dec_ref(v_k_1376_);
lean_dec_ref(v_H_1374_);
lean_dec_ref(v_00_u03c3s_1373_);
lean_dec(v_u_1372_);
v_a_1584_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1503_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1503_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
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
}
}
}
case 3:
{
lean_object* v_args_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1689_; 
v_args_1594_ = lean_ctor_get(v_pat_1375_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_pat_1375_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1596_ = v_pat_1375_;
v_isShared_1597_ = v_isSharedCheck_1689_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_args_1594_);
lean_dec(v_pat_1375_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1689_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
if (lean_obj_tag(v_args_1594_) == 0)
{
lean_object* v___x_1598_; 
lean_del_object(v___x_1596_);
lean_dec_ref(v_k_1376_);
lean_dec_ref(v_H_1374_);
lean_dec_ref(v_00_u03c3s_1373_);
lean_dec(v_u_1372_);
v___x_1598_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
return v___x_1598_;
}
else
{
lean_object* v_tail_1599_; 
v_tail_1599_ = lean_ctor_get(v_args_1594_, 1);
if (lean_obj_tag(v_tail_1599_) == 0)
{
lean_object* v_head_1600_; 
lean_del_object(v___x_1596_);
v_head_1600_ = lean_ctor_get(v_args_1594_, 0);
lean_inc(v_head_1600_);
lean_dec_ref_known(v_args_1594_, 2);
v_pat_1375_ = v_head_1600_;
goto _start;
}
else
{
lean_object* v_head_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1687_; 
lean_inc(v_tail_1599_);
lean_dec_ref(v_00_u03c3s_1373_);
v_head_1602_ = lean_ctor_get(v_args_1594_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_args_1594_);
if (v_isSharedCheck_1687_ == 0)
{
lean_object* v_unused_1688_; 
v_unused_1688_ = lean_ctor_get(v_args_1594_, 1);
lean_dec(v_unused_1688_);
v___x_1604_ = v_args_1594_;
v_isShared_1605_ = v_isSharedCheck_1687_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_head_1602_);
lean_dec(v_args_1594_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1687_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1606_ = l_Lean_Expr_consumeMData(v_H_1374_);
v___x_1607_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9));
v___x_1608_ = lean_unsigned_to_nat(3u);
v___x_1609_ = l_Lean_Expr_isAppOfArity(v___x_1606_, v___x_1607_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_dec_ref(v___x_1606_);
lean_del_object(v___x_1604_);
lean_dec(v_head_1602_);
lean_dec(v_tail_1599_);
lean_del_object(v___x_1596_);
lean_dec_ref(v_k_1376_);
lean_dec(v_u_1372_);
v___x_1610_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11);
v___x_1611_ = l_Lean_MessageData_ofExpr(v_H_1374_);
v___x_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_1612_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
return v___x_1613_;
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_dec_ref(v_H_1374_);
v___x_1614_ = l_Lean_Expr_appFn_x21(v___x_1606_);
v___x_1615_ = l_Lean_Expr_appFn_x21(v___x_1614_);
v___x_1616_ = l_Lean_Expr_appArg_x21(v___x_1615_);
lean_dec_ref(v___x_1615_);
v___x_1617_ = l_Lean_Expr_appArg_x21(v___x_1614_);
lean_dec_ref(v___x_1614_);
v___x_1618_ = l_Lean_Expr_appArg_x21(v___x_1606_);
lean_dec_ref(v___x_1606_);
lean_inc_ref(v_k_1376_);
lean_inc_ref(v___x_1617_);
lean_inc_ref(v___x_1616_);
lean_inc(v_u_1372_);
v___x_1619_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1372_, v___x_1616_, v___x_1617_, v_head_1602_, v_k_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v_snd_1621_; lean_object* v_fst_1622_; lean_object* v_snd_1623_; lean_object* v___x_1625_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
v_snd_1621_ = lean_ctor_get(v_a_1620_, 1);
lean_inc(v_snd_1621_);
lean_dec(v_a_1620_);
v_fst_1622_ = lean_ctor_get(v_snd_1621_, 0);
lean_inc(v_fst_1622_);
v_snd_1623_ = lean_ctor_get(v_snd_1621_, 1);
lean_inc(v_snd_1623_);
lean_dec(v_snd_1621_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v_tail_1599_);
v___x_1625_ = v___x_1596_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_tail_1599_);
v___x_1625_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1626_; 
lean_inc_ref(v___x_1618_);
lean_inc_ref(v___x_1616_);
lean_inc(v_u_1372_);
v___x_1626_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1372_, v___x_1616_, v___x_1618_, v___x_1625_, v_k_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v_snd_1628_; lean_object* v_fst_1629_; lean_object* v_snd_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1684_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v_snd_1628_ = lean_ctor_get(v_a_1627_, 1);
lean_inc(v_snd_1628_);
v_fst_1629_ = lean_ctor_get(v_a_1627_, 0);
lean_inc(v_fst_1629_);
lean_dec(v_a_1627_);
v_snd_1630_ = lean_ctor_get(v_snd_1628_, 1);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_snd_1628_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; 
v_unused_1685_ = lean_ctor_get(v_snd_1628_, 0);
lean_dec(v_unused_1685_);
v___x_1632_ = v_snd_1628_;
v_isShared_1633_ = v_isSharedCheck_1684_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_snd_1630_);
lean_dec(v_snd_1628_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1684_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; 
lean_inc(v_fst_1622_);
v___x_1634_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_1622_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1675_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1675_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1675_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v_fst_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1673_; 
v_fst_1639_ = lean_ctor_get(v_a_1635_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_a_1635_);
if (v_isSharedCheck_1673_ == 0)
{
lean_object* v_unused_1674_; 
v_unused_1674_ = lean_ctor_get(v_a_1635_, 1);
lean_dec(v_unused_1674_);
v___x_1641_ = v_a_1635_;
v_isShared_1642_ = v_isSharedCheck_1673_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_fst_1639_);
lean_dec(v_a_1635_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1673_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v_u_1643_; lean_object* v_00_u03c3s_1644_; lean_object* v_target_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1671_; 
v_u_1643_ = lean_ctor_get(v_fst_1622_, 0);
v_00_u03c3s_1644_ = lean_ctor_get(v_fst_1622_, 1);
v_target_1645_ = lean_ctor_get(v_fst_1622_, 3);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_fst_1622_);
if (v_isSharedCheck_1671_ == 0)
{
lean_object* v_unused_1672_; 
v_unused_1672_ = lean_ctor_get(v_fst_1622_, 2);
lean_dec(v_unused_1672_);
v___x_1647_ = v_fst_1622_;
v_isShared_1648_ = v_isSharedCheck_1671_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_target_1645_);
lean_inc(v_00_u03c3s_1644_);
lean_inc(v_u_1643_);
lean_dec(v_fst_1622_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1671_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1649_ = lean_box(0);
lean_inc(v_u_1372_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 1, v___x_1649_);
lean_ctor_set(v___x_1604_, 0, v_u_1372_);
v___x_1651_ = v___x_1604_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_u_1372_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1656_; 
lean_inc_ref(v___x_1651_);
v___x_1652_ = l_Lean_mkConst(v___x_1607_, v___x_1651_);
lean_inc_ref(v___x_1618_);
lean_inc_ref(v___x_1617_);
lean_inc_ref_n(v___x_1616_, 2);
v___x_1653_ = l_Lean_mkApp3(v___x_1652_, v___x_1616_, v___x_1617_, v___x_1618_);
lean_inc(v_fst_1639_);
v___x_1654_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1372_, v___x_1616_, v_fst_1639_, v___x_1653_);
lean_inc_ref(v_target_1645_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 2, v___x_1654_);
v___x_1656_ = v___x_1647_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_u_1643_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_00_u03c3s_1644_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1669_, 3, v_target_1645_);
v___x_1656_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1657_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13));
v___x_1658_ = l_Lean_mkConst(v___x_1657_, v___x_1651_);
v___x_1659_ = l_Lean_mkApp7(v___x_1658_, v___x_1616_, v_fst_1639_, v___x_1617_, v___x_1618_, v_target_1645_, v_snd_1623_, v_snd_1630_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 1, v___x_1659_);
lean_ctor_set(v___x_1641_, 0, v___x_1656_);
v___x_1661_ = v___x_1641_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1656_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1663_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 1, v___x_1661_);
lean_ctor_set(v___x_1632_, 0, v_fst_1629_);
v___x_1663_ = v___x_1632_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_fst_1629_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1665_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1663_);
v___x_1665_ = v___x_1637_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
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
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_del_object(v___x_1632_);
lean_dec(v_snd_1630_);
lean_dec(v_fst_1629_);
lean_dec(v_snd_1623_);
lean_dec(v_fst_1622_);
lean_dec_ref(v___x_1618_);
lean_dec_ref(v___x_1617_);
lean_dec_ref(v___x_1616_);
lean_del_object(v___x_1604_);
lean_dec(v_u_1372_);
v_a_1676_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1634_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1634_);
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
}
else
{
lean_dec(v_snd_1623_);
lean_dec(v_fst_1622_);
lean_dec_ref(v___x_1618_);
lean_dec_ref(v___x_1617_);
lean_dec_ref(v___x_1616_);
lean_del_object(v___x_1604_);
lean_dec(v_u_1372_);
return v___x_1626_;
}
}
}
else
{
lean_dec_ref(v___x_1618_);
lean_dec_ref(v___x_1617_);
lean_dec_ref(v___x_1616_);
lean_del_object(v___x_1604_);
lean_dec(v_tail_1599_);
lean_del_object(v___x_1596_);
lean_dec_ref(v_k_1376_);
lean_dec(v_u_1372_);
return v___x_1619_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_h_1690_; lean_object* v___f_1691_; lean_object* v___x_1692_; 
v_h_1690_ = lean_ctor_get(v_pat_1375_, 0);
lean_inc(v_h_1690_);
lean_dec_ref_known(v_pat_1375_, 1);
lean_inc_ref(v_00_u03c3s_1373_);
v___f_1691_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___boxed), 10, 3);
lean_closure_set(v___f_1691_, 0, v_u_1372_);
lean_closure_set(v___f_1691_, 1, v_00_u03c3s_1373_);
lean_closure_set(v___f_1691_, 2, v_k_1376_);
v___x_1692_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1373_, v_H_1374_, v_h_1690_, v___f_1691_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
return v___x_1692_;
}
default: 
{
lean_object* v_h_1693_; lean_object* v___x_1694_; 
lean_dec(v_u_1372_);
v_h_1693_ = lean_ctor_get(v_pat_1375_, 0);
lean_inc(v_h_1693_);
lean_dec_ref_known(v_pat_1375_, 1);
v___x_1694_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_h_1693_, v_a_1379_, v_a_1380_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v_fst_1696_; lean_object* v_snd_1697_; lean_object* v___x_1698_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1694_, 1);
v_fst_1696_ = lean_ctor_get(v_a_1695_, 0);
lean_inc(v_fst_1696_);
v_snd_1697_ = lean_ctor_get(v_a_1695_, 1);
lean_inc(v_snd_1697_);
lean_dec(v_a_1695_);
v___x_1698_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v_a_1380_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; lean_object* v___x_1703_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1698_, 1);
v___x_1700_ = l_Lean_Expr_consumeMData(v_H_1374_);
lean_dec_ref(v_H_1374_);
v___x_1701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1701_, 0, v_fst_1696_);
lean_ctor_set(v___x_1701_, 1, v_a_1699_);
lean_ctor_set(v___x_1701_, 2, v___x_1700_);
v___x_1702_ = 1;
lean_inc_ref(v___x_1701_);
v___x_1703_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_snd_1697_, v_00_u03c3s_1373_, v___x_1701_, v___x_1702_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec_ref_known(v___x_1703_, 1);
v___x_1704_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1701_);
lean_inc(v_a_1380_);
lean_inc_ref(v_a_1379_);
lean_inc(v_a_1378_);
lean_inc_ref(v_a_1377_);
v___x_1705_ = lean_apply_6(v_k_1376_, v___x_1704_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, lean_box(0));
return v___x_1705_;
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec_ref_known(v___x_1701_, 3);
lean_dec_ref(v_k_1376_);
v_a_1706_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1703_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1703_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec(v_snd_1697_);
lean_dec(v_fst_1696_);
lean_dec_ref(v_k_1376_);
lean_dec_ref(v_H_1374_);
lean_dec_ref(v_00_u03c3s_1373_);
v_a_1714_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1698_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1698_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_dec_ref(v_k_1376_);
lean_dec_ref(v_H_1374_);
lean_dec_ref(v_00_u03c3s_1373_);
v_a_1722_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1694_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1694_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1372_ = stack[0].m_obj;
lean_object* v_00_u03c3s_1373_ = stack[1].m_obj;
lean_object* v_H_1374_ = stack[2].m_obj;
lean_object* v_pat_1375_ = stack[3].m_obj;
lean_object* v_k_1376_ = stack[4].m_obj;
lean_object* v_a_1377_ = stack[5].m_obj;
lean_object* v_a_1378_ = stack[6].m_obj;
lean_object* v_a_1379_ = stack[7].m_obj;
lean_object* v_a_1380_ = stack[8].m_obj;
lean_object* v_res_1730_;
v_res_1730_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1372_, v_00_u03c3s_1373_, v_H_1374_, v_pat_1375_, v_k_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
stack->m_obj
 = v_res_1730_;
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2(lean_object* v___x_1731_, lean_object* v_tail_1732_, lean_object* v_u_1733_, lean_object* v___x_1734_, lean_object* v_k_1735_, lean_object* v_x_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1742_ = lean_unsigned_to_nat(1u);
v___x_1743_ = lean_mk_empty_array_with_capacity(v___x_1742_);
v___x_1744_ = lean_array_push(v___x_1743_, v_x_1736_);
v___x_1745_ = 0;
v___x_1746_ = l_Lean_Expr_betaRev(v___x_1731_, v___x_1744_, v___x_1745_, v___x_1745_);
lean_dec_ref(v___x_1744_);
v___x_1747_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1747_, 0, v_tail_1732_);
v___x_1748_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1733_, v___x_1734_, v___x_1746_, v___x_1747_, v_k_1735_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
return v___x_1748_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1731_ = stack[0].m_obj;
lean_object* v_tail_1732_ = stack[1].m_obj;
lean_object* v_u_1733_ = stack[2].m_obj;
lean_object* v___x_1734_ = stack[3].m_obj;
lean_object* v_k_1735_ = stack[4].m_obj;
lean_object* v_x_1736_ = stack[5].m_obj;
lean_object* v___y_1737_ = stack[6].m_obj;
lean_object* v___y_1738_ = stack[7].m_obj;
lean_object* v___y_1739_ = stack[8].m_obj;
lean_object* v___y_1740_ = stack[9].m_obj;
lean_object* v_res_1749_;
v_res_1749_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2(v___x_1731_, v_tail_1732_, v_u_1733_, v___x_1734_, v_k_1735_, v_x_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
stack->m_obj
 = v_res_1749_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___boxed(lean_object* v_u_1750_, lean_object* v_00_u03c3s_1751_, lean_object* v_H_1752_, lean_object* v_pat_1753_, lean_object* v_k_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1750_, v_00_u03c3s_1751_, v_H_1752_, v_pat_1753_, v_k_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
lean_dec(v_a_1758_);
lean_dec_ref(v_a_1757_);
lean_dec(v_a_1756_);
lean_dec_ref(v_a_1755_);
return v_res_1760_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore(lean_object* v_00_u03b1_1761_, lean_object* v_u_1762_, lean_object* v_00_u03c3s_1763_, lean_object* v_H_1764_, lean_object* v_pat_1765_, lean_object* v_k_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1762_, v_00_u03c3s_1763_, v_H_1764_, v_pat_1765_, v_k_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
return v___x_1772_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1762_ = stack[1].m_obj;
lean_object* v_00_u03c3s_1763_ = stack[2].m_obj;
lean_object* v_H_1764_ = stack[3].m_obj;
lean_object* v_pat_1765_ = stack[4].m_obj;
lean_object* v_k_1766_ = stack[5].m_obj;
lean_object* v_a_1767_ = stack[6].m_obj;
lean_object* v_a_1768_ = stack[7].m_obj;
lean_object* v_a_1769_ = stack[8].m_obj;
lean_object* v_a_1770_ = stack[9].m_obj;
lean_object* v_res_1773_;
v_res_1773_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore(lean_box(0), v_u_1762_, v_00_u03c3s_1763_, v_H_1764_, v_pat_1765_, v_k_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
stack->m_obj
 = v_res_1773_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___boxed(lean_object* v_00_u03b1_1774_, lean_object* v_u_1775_, lean_object* v_00_u03c3s_1776_, lean_object* v_H_1777_, lean_object* v_pat_1778_, lean_object* v_k_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore(v_00_u03b1_1774_, v_u_1775_, v_00_u03c3s_1776_, v_H_1777_, v_pat_1778_, v_k_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
return v_res_1785_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(lean_object* v_00_u03b1_1786_, lean_object* v_00_u03c3s_1787_, lean_object* v_hyp_1788_, lean_object* v_name_1789_, lean_object* v_k_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1787_, v_hyp_1788_, v_name_1789_, v_k_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
return v___x_1796_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03c3s_1787_ = stack[1].m_obj;
lean_object* v_hyp_1788_ = stack[2].m_obj;
lean_object* v_name_1789_ = stack[3].m_obj;
lean_object* v_k_1790_ = stack[4].m_obj;
lean_object* v___y_1791_ = stack[5].m_obj;
lean_object* v___y_1792_ = stack[6].m_obj;
lean_object* v___y_1793_ = stack[7].m_obj;
lean_object* v___y_1794_ = stack[8].m_obj;
lean_object* v_res_1797_;
v_res_1797_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(lean_box(0), v_00_u03c3s_1787_, v_hyp_1788_, v_name_1789_, v_k_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
stack->m_obj
 = v_res_1797_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___boxed(lean_object* v_00_u03b1_1798_, lean_object* v_00_u03c3s_1799_, lean_object* v_hyp_1800_, lean_object* v_name_1801_, lean_object* v_k_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(v_00_u03b1_1798_, v_00_u03c3s_1799_, v_hyp_1800_, v_name_1801_, v_k_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
return v_res_1808_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg(){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0);
v___x_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1812_;
v_res_1812_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
stack->m_obj
 = v_res_1812_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg___boxed(lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v_res_1814_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(lean_object* v_00_u03b1_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_1825_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1816_ = stack[1].m_obj;
lean_object* v___y_1817_ = stack[2].m_obj;
lean_object* v___y_1818_ = stack[3].m_obj;
lean_object* v___y_1819_ = stack[4].m_obj;
lean_object* v___y_1820_ = stack[5].m_obj;
lean_object* v___y_1821_ = stack[6].m_obj;
lean_object* v___y_1822_ = stack[7].m_obj;
lean_object* v___y_1823_ = stack[8].m_obj;
lean_object* v_res_1826_;
v_res_1826_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(lean_box(0), v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
stack->m_obj
 = v_res_1826_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___boxed(lean_object* v_00_u03b1_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(v_00_u03b1_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
return v_res_1837_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(lean_object* v_x_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___x_1848_; 
lean_inc(v___y_1842_);
lean_inc_ref(v___y_1841_);
lean_inc(v___y_1840_);
lean_inc_ref(v___y_1839_);
v___x_1848_ = lean_apply_9(v_x_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, lean_box(0));
return v___x_1848_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1838_ = stack[0].m_obj;
lean_object* v___y_1839_ = stack[1].m_obj;
lean_object* v___y_1840_ = stack[2].m_obj;
lean_object* v___y_1841_ = stack[3].m_obj;
lean_object* v___y_1842_ = stack[4].m_obj;
lean_object* v___y_1843_ = stack[5].m_obj;
lean_object* v___y_1844_ = stack[6].m_obj;
lean_object* v___y_1845_ = stack[7].m_obj;
lean_object* v___y_1846_ = stack[8].m_obj;
lean_object* v_res_1849_;
v_res_1849_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(v_x_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
stack->m_obj
 = v_res_1849_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0___boxed(lean_object* v_x_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(v_x_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
return v_res_1860_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(lean_object* v_mvarId_1861_, lean_object* v_x_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v___f_1872_; lean_object* v___x_1873_; 
lean_inc(v___y_1866_);
lean_inc_ref(v___y_1865_);
lean_inc(v___y_1864_);
lean_inc_ref(v___y_1863_);
v___f_1872_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1872_, 0, v_x_1862_);
lean_closure_set(v___f_1872_, 1, v___y_1863_);
lean_closure_set(v___f_1872_, 2, v___y_1864_);
lean_closure_set(v___f_1872_, 3, v___y_1865_);
lean_closure_set(v___f_1872_, 4, v___y_1866_);
v___x_1873_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1861_, v___f_1872_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1873_) == 0)
{
return v___x_1873_;
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
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
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1861_ = stack[0].m_obj;
lean_object* v_x_1862_ = stack[1].m_obj;
lean_object* v___y_1863_ = stack[2].m_obj;
lean_object* v___y_1864_ = stack[3].m_obj;
lean_object* v___y_1865_ = stack[4].m_obj;
lean_object* v___y_1866_ = stack[5].m_obj;
lean_object* v___y_1867_ = stack[6].m_obj;
lean_object* v___y_1868_ = stack[7].m_obj;
lean_object* v___y_1869_ = stack[8].m_obj;
lean_object* v___y_1870_ = stack[9].m_obj;
lean_object* v_res_1882_;
v_res_1882_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_mvarId_1861_, v_x_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
stack->m_obj
 = v_res_1882_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___boxed(lean_object* v_mvarId_1883_, lean_object* v_x_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_mvarId_1883_, v_x_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
return v_res_1894_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3(lean_object* v_00_u03b1_1895_, lean_object* v_mvarId_1896_, lean_object* v_x_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_mvarId_1896_, v_x_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
return v___x_1907_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1896_ = stack[1].m_obj;
lean_object* v_x_1897_ = stack[2].m_obj;
lean_object* v___y_1898_ = stack[3].m_obj;
lean_object* v___y_1899_ = stack[4].m_obj;
lean_object* v___y_1900_ = stack[5].m_obj;
lean_object* v___y_1901_ = stack[6].m_obj;
lean_object* v___y_1902_ = stack[7].m_obj;
lean_object* v___y_1903_ = stack[8].m_obj;
lean_object* v___y_1904_ = stack[9].m_obj;
lean_object* v___y_1905_ = stack[10].m_obj;
lean_object* v_res_1908_;
v_res_1908_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3(lean_box(0), v_mvarId_1896_, v_x_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
stack->m_obj
 = v_res_1908_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___boxed(lean_object* v_00_u03b1_1909_, lean_object* v_mvarId_1910_, lean_object* v_x_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3(v_00_u03b1_1909_, v_mvarId_1910_, v_x_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(lean_object* v_x_1922_, lean_object* v_x_1923_, lean_object* v_x_1924_, lean_object* v_x_1925_){
_start:
{
lean_object* v_ks_1926_; lean_object* v_vs_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1951_; 
v_ks_1926_ = lean_ctor_get(v_x_1922_, 0);
v_vs_1927_ = lean_ctor_get(v_x_1922_, 1);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_x_1922_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1929_ = v_x_1922_;
v_isShared_1930_ = v_isSharedCheck_1951_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_vs_1927_);
lean_inc(v_ks_1926_);
lean_dec(v_x_1922_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1951_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; uint8_t v___x_1932_; 
v___x_1931_ = lean_array_get_size(v_ks_1926_);
v___x_1932_ = lean_nat_dec_lt(v_x_1923_, v___x_1931_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1936_; 
lean_dec(v_x_1923_);
v___x_1933_ = lean_array_push(v_ks_1926_, v_x_1924_);
v___x_1934_ = lean_array_push(v_vs_1927_, v_x_1925_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 1, v___x_1934_);
lean_ctor_set(v___x_1929_, 0, v___x_1933_);
v___x_1936_ = v___x_1929_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
else
{
lean_object* v_k_x27_1938_; uint8_t v___x_1939_; 
v_k_x27_1938_ = lean_array_fget_borrowed(v_ks_1926_, v_x_1923_);
v___x_1939_ = l_Lean_instBEqMVarId_beq(v_x_1924_, v_k_x27_1938_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1941_; 
if (v_isShared_1930_ == 0)
{
v___x_1941_ = v___x_1929_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_ks_1926_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_vs_1927_);
v___x_1941_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = lean_unsigned_to_nat(1u);
v___x_1943_ = lean_nat_add(v_x_1923_, v___x_1942_);
lean_dec(v_x_1923_);
v_x_1922_ = v___x_1941_;
v_x_1923_ = v___x_1943_;
goto _start;
}
}
else
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___x_1946_ = lean_array_fset(v_ks_1926_, v_x_1923_, v_x_1924_);
v___x_1947_ = lean_array_fset(v_vs_1927_, v_x_1923_, v_x_1925_);
lean_dec(v_x_1923_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 1, v___x_1947_);
lean_ctor_set(v___x_1929_, 0, v___x_1946_);
v___x_1949_ = v___x_1929_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1946_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(lean_object* v_n_1952_, lean_object* v_k_1953_, lean_object* v_v_1954_){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_unsigned_to_nat(0u);
v___x_1956_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(v_n_1952_, v___x_1955_, v_k_1953_, v_v_1954_);
return v___x_1956_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1957_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(lean_object* v_x_1958_, size_t v_x_1959_, size_t v_x_1960_, lean_object* v_x_1961_, lean_object* v_x_1962_){
_start:
{
if (lean_obj_tag(v_x_1958_) == 0)
{
lean_object* v_es_1963_; size_t v___x_1964_; size_t v___x_1965_; lean_object* v_j_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v_es_1963_ = lean_ctor_get(v_x_1958_, 0);
v___x_1964_ = ((size_t)31ULL);
v___x_1965_ = lean_usize_land(v_x_1959_, v___x_1964_);
v_j_1966_ = lean_usize_to_nat(v___x_1965_);
v___x_1967_ = lean_array_get_size(v_es_1963_);
v___x_1968_ = lean_nat_dec_lt(v_j_1966_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_dec(v_j_1966_);
lean_dec(v_x_1962_);
lean_dec(v_x_1961_);
return v_x_1958_;
}
else
{
lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_2007_; 
lean_inc_ref(v_es_1963_);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_x_1958_);
if (v_isSharedCheck_2007_ == 0)
{
lean_object* v_unused_2008_; 
v_unused_2008_ = lean_ctor_get(v_x_1958_, 0);
lean_dec(v_unused_2008_);
v___x_1970_ = v_x_1958_;
v_isShared_1971_ = v_isSharedCheck_2007_;
goto v_resetjp_1969_;
}
else
{
lean_dec(v_x_1958_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_2007_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v_v_1972_; lean_object* v___x_1973_; lean_object* v_xs_x27_1974_; lean_object* v___y_1976_; 
v_v_1972_ = lean_array_fget(v_es_1963_, v_j_1966_);
v___x_1973_ = lean_box(0);
v_xs_x27_1974_ = lean_array_fset(v_es_1963_, v_j_1966_, v___x_1973_);
switch(lean_obj_tag(v_v_1972_))
{
case 0:
{
lean_object* v_key_1981_; lean_object* v_val_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1992_; 
v_key_1981_ = lean_ctor_get(v_v_1972_, 0);
v_val_1982_ = lean_ctor_get(v_v_1972_, 1);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_v_1972_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1984_ = v_v_1972_;
v_isShared_1985_ = v_isSharedCheck_1992_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_val_1982_);
lean_inc(v_key_1981_);
lean_dec(v_v_1972_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1992_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
uint8_t v___x_1986_; 
v___x_1986_ = l_Lean_instBEqMVarId_beq(v_x_1961_, v_key_1981_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
lean_del_object(v___x_1984_);
v___x_1987_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1981_, v_val_1982_, v_x_1961_, v_x_1962_);
v___x_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
v___y_1976_ = v___x_1988_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_1990_; 
lean_dec(v_val_1982_);
lean_dec(v_key_1981_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 1, v_x_1962_);
lean_ctor_set(v___x_1984_, 0, v_x_1961_);
v___x_1990_ = v___x_1984_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_x_1961_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_x_1962_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
v___y_1976_ = v___x_1990_;
goto v___jp_1975_;
}
}
}
}
case 1:
{
lean_object* v_node_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2005_; 
v_node_1993_ = lean_ctor_get(v_v_1972_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_v_1972_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1995_ = v_v_1972_;
v_isShared_1996_ = v_isSharedCheck_2005_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_node_1993_);
lean_dec(v_v_1972_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2005_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
size_t v___x_1997_; size_t v___x_1998_; size_t v___x_1999_; size_t v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2003_; 
v___x_1997_ = ((size_t)5ULL);
v___x_1998_ = lean_usize_shift_right(v_x_1959_, v___x_1997_);
v___x_1999_ = ((size_t)1ULL);
v___x_2000_ = lean_usize_add(v_x_1960_, v___x_1999_);
v___x_2001_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_node_1993_, v___x_1998_, v___x_2000_, v_x_1961_, v_x_1962_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_2001_);
v___x_2003_ = v___x_1995_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
v___y_1976_ = v___x_2003_;
goto v___jp_1975_;
}
}
}
default: 
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2006_, 0, v_x_1961_);
lean_ctor_set(v___x_2006_, 1, v_x_1962_);
v___y_1976_ = v___x_2006_;
goto v___jp_1975_;
}
}
v___jp_1975_:
{
lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1977_ = lean_array_fset(v_xs_x27_1974_, v_j_1966_, v___y_1976_);
lean_dec(v_j_1966_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1977_);
v___x_1979_ = v___x_1970_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
else
{
lean_object* v_ks_2009_; lean_object* v_vs_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2028_; 
v_ks_2009_ = lean_ctor_get(v_x_1958_, 0);
v_vs_2010_ = lean_ctor_get(v_x_1958_, 1);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_x_1958_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2012_ = v_x_1958_;
v_isShared_2013_ = v_isSharedCheck_2028_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_vs_2010_);
lean_inc(v_ks_2009_);
lean_dec(v_x_1958_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2028_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_ks_2009_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_vs_2010_);
v___x_2015_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v_newNode_2016_; size_t v___x_2017_; uint8_t v___x_2018_; 
v_newNode_2016_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(v___x_2015_, v_x_1961_, v_x_1962_);
v___x_2017_ = ((size_t)7ULL);
v___x_2018_ = lean_usize_dec_le(v___x_2017_, v_x_1960_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2019_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2016_);
v___x_2020_ = lean_unsigned_to_nat(4u);
v___x_2021_ = lean_nat_dec_lt(v___x_2019_, v___x_2020_);
lean_dec(v___x_2019_);
if (v___x_2021_ == 0)
{
lean_object* v_ks_2022_; lean_object* v_vs_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v_ks_2022_ = lean_ctor_get(v_newNode_2016_, 0);
lean_inc_ref(v_ks_2022_);
v_vs_2023_ = lean_ctor_get(v_newNode_2016_, 1);
lean_inc_ref(v_vs_2023_);
lean_dec_ref(v_newNode_2016_);
v___x_2024_ = lean_unsigned_to_nat(0u);
v___x_2025_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0);
v___x_2026_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_x_1960_, v_ks_2022_, v_vs_2023_, v___x_2024_, v___x_2025_);
lean_dec_ref(v_vs_2023_);
lean_dec_ref(v_ks_2022_);
return v___x_2026_;
}
else
{
return v_newNode_2016_;
}
}
else
{
return v_newNode_2016_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1958_ = stack[0].m_obj;
size_t v_x_1959_ = stack[1].m_num;
size_t v_x_1960_ = stack[2].m_num;
lean_object* v_x_1961_ = stack[3].m_obj;
lean_object* v_x_1962_ = stack[4].m_obj;
lean_object* v_res_2029_;
v_res_2029_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_1958_, v_x_1959_, v_x_1960_, v_x_1961_, v_x_1962_);
stack->m_obj
 = v_res_2029_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(size_t v_depth_2030_, lean_object* v_keys_2031_, lean_object* v_vals_2032_, lean_object* v_i_2033_, lean_object* v_entries_2034_){
_start:
{
lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2035_ = lean_array_get_size(v_keys_2031_);
v___x_2036_ = lean_nat_dec_lt(v_i_2033_, v___x_2035_);
if (v___x_2036_ == 0)
{
lean_dec(v_i_2033_);
return v_entries_2034_;
}
else
{
lean_object* v_k_2037_; lean_object* v_v_2038_; uint64_t v___x_2039_; size_t v_h_2040_; size_t v___x_2041_; lean_object* v___x_2042_; size_t v___x_2043_; size_t v___x_2044_; size_t v___x_2045_; size_t v_h_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v_k_2037_ = lean_array_fget_borrowed(v_keys_2031_, v_i_2033_);
v_v_2038_ = lean_array_fget_borrowed(v_vals_2032_, v_i_2033_);
v___x_2039_ = l_Lean_instHashableMVarId_hash(v_k_2037_);
v_h_2040_ = lean_uint64_to_usize(v___x_2039_);
v___x_2041_ = ((size_t)5ULL);
v___x_2042_ = lean_unsigned_to_nat(1u);
v___x_2043_ = ((size_t)1ULL);
v___x_2044_ = lean_usize_sub(v_depth_2030_, v___x_2043_);
v___x_2045_ = lean_usize_mul(v___x_2041_, v___x_2044_);
v_h_2046_ = lean_usize_shift_right(v_h_2040_, v___x_2045_);
v___x_2047_ = lean_nat_add(v_i_2033_, v___x_2042_);
lean_dec(v_i_2033_);
lean_inc(v_v_2038_);
lean_inc(v_k_2037_);
v___x_2048_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_entries_2034_, v_h_2046_, v_depth_2030_, v_k_2037_, v_v_2038_);
v_i_2033_ = v___x_2047_;
v_entries_2034_ = v___x_2048_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2030_ = stack[0].m_num;
lean_object* v_keys_2031_ = stack[1].m_obj;
lean_object* v_vals_2032_ = stack[2].m_obj;
lean_object* v_i_2033_ = stack[3].m_obj;
lean_object* v_entries_2034_ = stack[4].m_obj;
lean_object* v_res_2050_;
v_res_2050_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_depth_2030_, v_keys_2031_, v_vals_2032_, v_i_2033_, v_entries_2034_);
stack->m_obj
 = v_res_2050_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg___boxed(lean_object* v_depth_2051_, lean_object* v_keys_2052_, lean_object* v_vals_2053_, lean_object* v_i_2054_, lean_object* v_entries_2055_){
_start:
{
size_t v_depth_boxed_2056_; lean_object* v_res_2057_; 
v_depth_boxed_2056_ = lean_unbox_usize(v_depth_2051_);
lean_dec(v_depth_2051_);
v_res_2057_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_depth_boxed_2056_, v_keys_2052_, v_vals_2053_, v_i_2054_, v_entries_2055_);
lean_dec_ref(v_vals_2053_);
lean_dec_ref(v_keys_2052_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___boxed(lean_object* v_x_2058_, lean_object* v_x_2059_, lean_object* v_x_2060_, lean_object* v_x_2061_, lean_object* v_x_2062_){
_start:
{
size_t v_x_19859__boxed_2063_; size_t v_x_19860__boxed_2064_; lean_object* v_res_2065_; 
v_x_19859__boxed_2063_ = lean_unbox_usize(v_x_2059_);
lean_dec(v_x_2059_);
v_x_19860__boxed_2064_ = lean_unbox_usize(v_x_2060_);
lean_dec(v_x_2060_);
v_res_2065_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_2058_, v_x_19859__boxed_2063_, v_x_19860__boxed_2064_, v_x_2061_, v_x_2062_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(lean_object* v_x_2066_, lean_object* v_x_2067_, lean_object* v_x_2068_){
_start:
{
uint64_t v___x_2069_; size_t v___x_2070_; size_t v___x_2071_; lean_object* v___x_2072_; 
v___x_2069_ = l_Lean_instHashableMVarId_hash(v_x_2067_);
v___x_2070_ = lean_uint64_to_usize(v___x_2069_);
v___x_2071_ = ((size_t)1ULL);
v___x_2072_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_2066_, v___x_2070_, v___x_2071_, v_x_2067_, v_x_2068_);
return v___x_2072_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(lean_object* v_mvarId_2073_, lean_object* v_val_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2077_; lean_object* v_mctx_2078_; lean_object* v_cache_2079_; lean_object* v_zetaDeltaFVarIds_2080_; lean_object* v_postponed_2081_; lean_object* v_diag_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2112_; 
v___x_2077_ = lean_st_ref_take(v___y_2075_);
v_mctx_2078_ = lean_ctor_get(v___x_2077_, 0);
v_cache_2079_ = lean_ctor_get(v___x_2077_, 1);
v_zetaDeltaFVarIds_2080_ = lean_ctor_get(v___x_2077_, 2);
v_postponed_2081_ = lean_ctor_get(v___x_2077_, 3);
v_diag_2082_ = lean_ctor_get(v___x_2077_, 4);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2084_ = v___x_2077_;
v_isShared_2085_ = v_isSharedCheck_2112_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_diag_2082_);
lean_inc(v_postponed_2081_);
lean_inc(v_zetaDeltaFVarIds_2080_);
lean_inc(v_cache_2079_);
lean_inc(v_mctx_2078_);
lean_dec(v___x_2077_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2112_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v_depth_2086_; lean_object* v_levelAssignDepth_2087_; lean_object* v_lmvarCounter_2088_; lean_object* v_mvarCounter_2089_; lean_object* v_lDecls_2090_; lean_object* v_decls_2091_; lean_object* v_userNames_2092_; lean_object* v_lAssignment_2093_; lean_object* v_eAssignment_2094_; lean_object* v_dAssignment_2095_; lean_object* v_instanceTypedMVars_2096_; lean_object* v_synthNormMemo_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2111_; 
v_depth_2086_ = lean_ctor_get(v_mctx_2078_, 0);
v_levelAssignDepth_2087_ = lean_ctor_get(v_mctx_2078_, 1);
v_lmvarCounter_2088_ = lean_ctor_get(v_mctx_2078_, 2);
v_mvarCounter_2089_ = lean_ctor_get(v_mctx_2078_, 3);
v_lDecls_2090_ = lean_ctor_get(v_mctx_2078_, 4);
v_decls_2091_ = lean_ctor_get(v_mctx_2078_, 5);
v_userNames_2092_ = lean_ctor_get(v_mctx_2078_, 6);
v_lAssignment_2093_ = lean_ctor_get(v_mctx_2078_, 7);
v_eAssignment_2094_ = lean_ctor_get(v_mctx_2078_, 8);
v_dAssignment_2095_ = lean_ctor_get(v_mctx_2078_, 9);
v_instanceTypedMVars_2096_ = lean_ctor_get(v_mctx_2078_, 10);
v_synthNormMemo_2097_ = lean_ctor_get(v_mctx_2078_, 11);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_mctx_2078_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2099_ = v_mctx_2078_;
v_isShared_2100_ = v_isSharedCheck_2111_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_synthNormMemo_2097_);
lean_inc(v_instanceTypedMVars_2096_);
lean_inc(v_dAssignment_2095_);
lean_inc(v_eAssignment_2094_);
lean_inc(v_lAssignment_2093_);
lean_inc(v_userNames_2092_);
lean_inc(v_decls_2091_);
lean_inc(v_lDecls_2090_);
lean_inc(v_mvarCounter_2089_);
lean_inc(v_lmvarCounter_2088_);
lean_inc(v_levelAssignDepth_2087_);
lean_inc(v_depth_2086_);
lean_dec(v_mctx_2078_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2111_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2104_; 
v___x_2101_ = lean_box(0);
v___x_2102_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(v_eAssignment_2094_, v_mvarId_2073_, v_val_2074_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 8, v___x_2102_);
v___x_2104_ = v___x_2099_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_depth_2086_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_levelAssignDepth_2087_);
lean_ctor_set(v_reuseFailAlloc_2110_, 2, v_lmvarCounter_2088_);
lean_ctor_set(v_reuseFailAlloc_2110_, 3, v_mvarCounter_2089_);
lean_ctor_set(v_reuseFailAlloc_2110_, 4, v_lDecls_2090_);
lean_ctor_set(v_reuseFailAlloc_2110_, 5, v_decls_2091_);
lean_ctor_set(v_reuseFailAlloc_2110_, 6, v_userNames_2092_);
lean_ctor_set(v_reuseFailAlloc_2110_, 7, v_lAssignment_2093_);
lean_ctor_set(v_reuseFailAlloc_2110_, 8, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2110_, 9, v_dAssignment_2095_);
lean_ctor_set(v_reuseFailAlloc_2110_, 10, v_instanceTypedMVars_2096_);
lean_ctor_set(v_reuseFailAlloc_2110_, 11, v_synthNormMemo_2097_);
v___x_2104_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2106_; 
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2104_);
v___x_2106_ = v___x_2084_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_cache_2079_);
lean_ctor_set(v_reuseFailAlloc_2109_, 2, v_zetaDeltaFVarIds_2080_);
lean_ctor_set(v_reuseFailAlloc_2109_, 3, v_postponed_2081_);
lean_ctor_set(v_reuseFailAlloc_2109_, 4, v_diag_2082_);
v___x_2106_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = lean_st_ref_put(v___y_2075_, v___x_2106_);
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2101_);
return v___x_2108_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2073_ = stack[0].m_obj;
lean_object* v_val_2074_ = stack[1].m_obj;
lean_object* v___y_2075_ = stack[2].m_obj;
lean_object* v_res_2113_;
v_res_2113_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_mvarId_2073_, v_val_2074_, v___y_2075_);
stack->m_obj
 = v_res_2113_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg___boxed(lean_object* v_mvarId_2114_, lean_object* v_val_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_mvarId_2114_, v_val_2115_, v___y_2116_);
lean_dec(v___y_2116_);
return v_res_2118_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(lean_object* v_snd_2121_, lean_object* v_hyp_2122_, lean_object* v_a_2123_, lean_object* v_fst_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___x_2134_; 
lean_inc_ref(v_snd_2121_);
v___x_2134_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_snd_2121_, v_hyp_2122_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v_focusHyp_2136_; lean_object* v_restHyps_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v_u_2140_; lean_object* v_00_u03c3s_2141_; lean_object* v_target_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v_focusHyp_2136_ = lean_ctor_get(v_a_2135_, 0);
v_restHyps_2137_ = lean_ctor_get(v_a_2135_, 1);
v___x_2138_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0));
v___x_2139_ = lean_st_mk_ref(v___x_2138_);
v_u_2140_ = lean_ctor_get(v_snd_2121_, 0);
v_00_u03c3s_2141_ = lean_ctor_get(v_snd_2121_, 1);
v_target_2142_ = lean_ctor_get(v_snd_2121_, 3);
lean_inc_ref(v_restHyps_2137_);
lean_inc_ref(v_target_2142_);
lean_inc_ref_n(v_00_u03c3s_2141_, 2);
lean_inc(v___x_2139_);
lean_inc_n(v_u_2140_, 2);
v___x_2143_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___boxed), 11, 5);
lean_closure_set(v___x_2143_, 0, v_u_2140_);
lean_closure_set(v___x_2143_, 1, v___x_2139_);
lean_closure_set(v___x_2143_, 2, v_00_u03c3s_2141_);
lean_closure_set(v___x_2143_, 3, v_target_2142_);
lean_closure_set(v___x_2143_, 4, v_restHyps_2137_);
lean_inc_ref(v_focusHyp_2136_);
v___x_2144_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_2140_, v_00_u03c3s_2141_, v_focusHyp_2136_, v_a_2123_, v___x_2143_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v_snd_2146_; lean_object* v_snd_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v_snd_2146_ = lean_ctor_get(v_a_2145_, 1);
lean_inc(v_snd_2146_);
lean_dec(v_a_2145_);
v_snd_2147_ = lean_ctor_get(v_snd_2146_, 1);
lean_inc(v_snd_2147_);
lean_dec(v_snd_2146_);
v___x_2148_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps(v_a_2135_, v_snd_2121_, v_snd_2147_);
v___x_2149_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_fst_2124_, v___x_2148_, v___y_2130_);
lean_dec_ref(v___x_2149_);
v___x_2150_ = lean_st_ref_get(v___x_2139_);
lean_dec(v___x_2139_);
v___x_2151_ = lean_array_to_list(v___x_2150_);
v___x_2152_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2151_, v___y_2126_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
return v___x_2152_;
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec(v___x_2139_);
lean_dec(v_a_2135_);
lean_dec(v_fst_2124_);
lean_dec_ref(v_snd_2121_);
v_a_2153_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2144_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2144_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_dec(v_fst_2124_);
lean_dec(v_a_2123_);
lean_dec_ref(v_snd_2121_);
v_a_2161_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2134_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2134_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_2121_ = stack[0].m_obj;
lean_object* v_hyp_2122_ = stack[1].m_obj;
lean_object* v_a_2123_ = stack[2].m_obj;
lean_object* v_fst_2124_ = stack[3].m_obj;
lean_object* v___y_2125_ = stack[4].m_obj;
lean_object* v___y_2126_ = stack[5].m_obj;
lean_object* v___y_2127_ = stack[6].m_obj;
lean_object* v___y_2128_ = stack[7].m_obj;
lean_object* v___y_2129_ = stack[8].m_obj;
lean_object* v___y_2130_ = stack[9].m_obj;
lean_object* v___y_2131_ = stack[10].m_obj;
lean_object* v___y_2132_ = stack[11].m_obj;
lean_object* v_res_2169_;
v_res_2169_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(v_snd_2121_, v_hyp_2122_, v_a_2123_, v_fst_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
stack->m_obj
 = v_res_2169_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___boxed(lean_object* v_snd_2170_, lean_object* v_hyp_2171_, lean_object* v_a_2172_, lean_object* v_fst_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(v_snd_2170_, v_hyp_2171_, v_a_2172_, v_fst_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
return v_res_2183_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2184_; double v___x_2185_; 
v___x_2184_ = lean_unsigned_to_nat(0u);
v___x_2185_ = lean_float_of_nat(v___x_2184_);
return v___x_2185_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(lean_object* v_cls_2189_, lean_object* v_msg_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_ref_2196_; lean_object* v___x_2197_; lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2243_; 
v_ref_2196_ = lean_ctor_get(v___y_2193_, 2);
v___x_2197_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2200_ = v___x_2197_;
v_isShared_2201_ = v_isSharedCheck_2243_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2197_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2243_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; lean_object* v_traceState_2203_; lean_object* v_env_2204_; lean_object* v_nextMacroScope_2205_; lean_object* v_ngen_2206_; lean_object* v_auxDeclNGen_2207_; lean_object* v_cache_2208_; lean_object* v_recordedDeps_2209_; lean_object* v_messages_2210_; lean_object* v_infoState_2211_; lean_object* v_snapshotTasks_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2242_; 
v___x_2202_ = lean_st_ref_take(v___y_2194_);
v_traceState_2203_ = lean_ctor_get(v___x_2202_, 4);
v_env_2204_ = lean_ctor_get(v___x_2202_, 0);
v_nextMacroScope_2205_ = lean_ctor_get(v___x_2202_, 1);
v_ngen_2206_ = lean_ctor_get(v___x_2202_, 2);
v_auxDeclNGen_2207_ = lean_ctor_get(v___x_2202_, 3);
v_cache_2208_ = lean_ctor_get(v___x_2202_, 5);
v_recordedDeps_2209_ = lean_ctor_get(v___x_2202_, 6);
v_messages_2210_ = lean_ctor_get(v___x_2202_, 7);
v_infoState_2211_ = lean_ctor_get(v___x_2202_, 8);
v_snapshotTasks_2212_ = lean_ctor_get(v___x_2202_, 9);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2214_ = v___x_2202_;
v_isShared_2215_ = v_isSharedCheck_2242_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_snapshotTasks_2212_);
lean_inc(v_infoState_2211_);
lean_inc(v_messages_2210_);
lean_inc(v_recordedDeps_2209_);
lean_inc(v_cache_2208_);
lean_inc(v_traceState_2203_);
lean_inc(v_auxDeclNGen_2207_);
lean_inc(v_ngen_2206_);
lean_inc(v_nextMacroScope_2205_);
lean_inc(v_env_2204_);
lean_dec(v___x_2202_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2242_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
uint64_t v_tid_2216_; lean_object* v_traces_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2241_; 
v_tid_2216_ = lean_ctor_get_uint64(v_traceState_2203_, sizeof(void*)*1);
v_traces_2217_ = lean_ctor_get(v_traceState_2203_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_traceState_2203_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2219_ = v_traceState_2203_;
v_isShared_2220_ = v_isSharedCheck_2241_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_traces_2217_);
lean_dec(v_traceState_2203_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2241_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; double v___x_2223_; uint8_t v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2221_ = lean_box(0);
v___x_2222_ = lean_box(0);
v___x_2223_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0);
v___x_2224_ = 0;
v___x_2225_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1));
v___x_2226_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2226_, 0, v_cls_2189_);
lean_ctor_set(v___x_2226_, 1, v___x_2222_);
lean_ctor_set(v___x_2226_, 2, v___x_2225_);
lean_ctor_set_float(v___x_2226_, sizeof(void*)*3, v___x_2223_);
lean_ctor_set_float(v___x_2226_, sizeof(void*)*3 + 8, v___x_2223_);
lean_ctor_set_uint8(v___x_2226_, sizeof(void*)*3 + 16, v___x_2224_);
v___x_2227_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2));
v___x_2228_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2226_);
lean_ctor_set(v___x_2228_, 1, v_a_2198_);
lean_ctor_set(v___x_2228_, 2, v___x_2227_);
lean_inc(v_ref_2196_);
v___x_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2229_, 0, v_ref_2196_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
v___x_2230_ = l_Lean_PersistentArray_push___redArg(v_traces_2217_, v___x_2229_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 0, v___x_2230_);
v___x_2232_ = v___x_2219_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2230_);
lean_ctor_set_uint64(v_reuseFailAlloc_2240_, sizeof(void*)*1, v_tid_2216_);
v___x_2232_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2234_; 
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 4, v___x_2232_);
v___x_2234_ = v___x_2214_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_env_2204_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_nextMacroScope_2205_);
lean_ctor_set(v_reuseFailAlloc_2239_, 2, v_ngen_2206_);
lean_ctor_set(v_reuseFailAlloc_2239_, 3, v_auxDeclNGen_2207_);
lean_ctor_set(v_reuseFailAlloc_2239_, 4, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2239_, 5, v_cache_2208_);
lean_ctor_set(v_reuseFailAlloc_2239_, 6, v_recordedDeps_2209_);
lean_ctor_set(v_reuseFailAlloc_2239_, 7, v_messages_2210_);
lean_ctor_set(v_reuseFailAlloc_2239_, 8, v_infoState_2211_);
lean_ctor_set(v_reuseFailAlloc_2239_, 9, v_snapshotTasks_2212_);
v___x_2234_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2235_; lean_object* v___x_2237_; 
v___x_2235_ = lean_st_ref_put(v___y_2194_, v___x_2234_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2221_);
v___x_2237_ = v___x_2200_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2221_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2189_ = stack[0].m_obj;
lean_object* v_msg_2190_ = stack[1].m_obj;
lean_object* v___y_2191_ = stack[2].m_obj;
lean_object* v___y_2192_ = stack[3].m_obj;
lean_object* v___y_2193_ = stack[4].m_obj;
lean_object* v___y_2194_ = stack[5].m_obj;
lean_object* v_res_2244_;
v_res_2244_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_2189_, v_msg_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
stack->m_obj
 = v_res_2244_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___boxed(lean_object* v_cls_2245_, lean_object* v_msg_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_2245_, v_msg_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
return v_res_2252_;
}
}
lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(lean_object* v_as_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
if (lean_obj_tag(v_as_2256_) == 0)
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = lean_box(0);
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
return v___x_2267_;
}
else
{
lean_object* v_toCold_2268_; lean_object* v_options_2269_; uint8_t v_hasTrace_2270_; 
v_toCold_2268_ = lean_ctor_get(v___y_2263_, 0);
v_options_2269_ = lean_ctor_get(v_toCold_2268_, 2);
v_hasTrace_2270_ = lean_ctor_get_uint8(v_options_2269_, sizeof(void*)*1);
if (v_hasTrace_2270_ == 0)
{
lean_object* v_tail_2271_; 
v_tail_2271_ = lean_ctor_get(v_as_2256_, 1);
lean_inc(v_tail_2271_);
lean_dec_ref_known(v_as_2256_, 2);
v_as_2256_ = v_tail_2271_;
goto _start;
}
else
{
lean_object* v_head_2273_; lean_object* v_tail_2274_; lean_object* v_fst_2275_; lean_object* v_snd_2276_; lean_object* v_inheritedTraceOptions_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; 
v_head_2273_ = lean_ctor_get(v_as_2256_, 0);
lean_inc(v_head_2273_);
v_tail_2274_ = lean_ctor_get(v_as_2256_, 1);
lean_inc(v_tail_2274_);
lean_dec_ref_known(v_as_2256_, 2);
v_fst_2275_ = lean_ctor_get(v_head_2273_, 0);
lean_inc_n(v_fst_2275_, 2);
v_snd_2276_ = lean_ctor_get(v_head_2273_, 1);
lean_inc(v_snd_2276_);
lean_dec(v_head_2273_);
v_inheritedTraceOptions_2277_ = lean_ctor_get(v_toCold_2268_, 11);
v___x_2278_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1));
v___x_2279_ = l_Lean_Name_append(v___x_2278_, v_fst_2275_);
v___x_2280_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2277_, v_options_2269_, v___x_2279_);
lean_dec(v___x_2279_);
if (v___x_2280_ == 0)
{
lean_dec(v_snd_2276_);
lean_dec(v_fst_2275_);
v_as_2256_ = v_tail_2274_;
goto _start;
}
else
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2282_, 0, v_snd_2276_);
v___x_2283_ = l_Lean_MessageData_ofFormat(v___x_2282_);
v___x_2284_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_fst_2275_, v___x_2283_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_dec_ref_known(v___x_2284_, 1);
v_as_2256_ = v_tail_2274_;
goto _start;
}
else
{
lean_dec(v_tail_2274_);
return v___x_2284_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2256_ = stack[0].m_obj;
lean_object* v___y_2257_ = stack[1].m_obj;
lean_object* v___y_2258_ = stack[2].m_obj;
lean_object* v___y_2259_ = stack[3].m_obj;
lean_object* v___y_2260_ = stack[4].m_obj;
lean_object* v___y_2261_ = stack[5].m_obj;
lean_object* v___y_2262_ = stack[6].m_obj;
lean_object* v___y_2263_ = stack[7].m_obj;
lean_object* v___y_2264_ = stack[8].m_obj;
lean_object* v_res_2286_;
v_res_2286_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(v_as_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
stack->m_obj
 = v_res_2286_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___boxed(lean_object* v_as_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(v_as_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(lean_object* v_env_2298_, lean_object* v_declName_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
uint8_t v___x_2302_; lean_object* v_env_2303_; lean_object* v___x_2304_; uint8_t v___x_2305_; uint8_t v___x_2306_; 
v___x_2302_ = 0;
v_env_2303_ = l_Lean_Environment_setExporting(v_env_2298_, v___x_2302_);
lean_inc(v_declName_2299_);
v___x_2304_ = l_Lean_mkPrivateName(v_env_2303_, v_declName_2299_);
v___x_2305_ = 1;
lean_inc_ref(v_env_2303_);
v___x_2306_ = l_Lean_Environment_contains(v_env_2303_, v___x_2304_, v___x_2305_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2307_; uint8_t v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2307_ = l_Lean_privateToUserName(v_declName_2299_);
v___x_2308_ = l_Lean_Environment_contains(v_env_2303_, v___x_2307_, v___x_2305_);
v___x_2309_ = lean_box(v___x_2308_);
v___x_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
lean_ctor_set(v___x_2310_, 1, v___y_2301_);
return v___x_2310_;
}
else
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
lean_dec_ref(v_env_2303_);
lean_dec(v_declName_2299_);
v___x_2311_ = lean_box(v___x_2306_);
v___x_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
lean_ctor_set(v___x_2312_, 1, v___y_2301_);
return v___x_2312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed(lean_object* v_env_2313_, lean_object* v_declName_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(v_env_2313_, v_declName_2314_, v___y_2315_, v___y_2316_);
lean_dec_ref(v___y_2315_);
return v_res_2317_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(lean_object* v_msg_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v_ref_2324_; lean_object* v___x_2325_; lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2334_; 
v_ref_2324_ = lean_ctor_get(v___y_2321_, 2);
v___x_2325_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2332_; 
lean_inc(v_ref_2324_);
v___x_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2330_, 0, v_ref_2324_);
lean_ctor_set(v___x_2330_, 1, v_a_2326_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set_tag(v___x_2328_, 1);
lean_ctor_set(v___x_2328_, 0, v___x_2330_);
v___x_2332_ = v___x_2328_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2318_ = stack[0].m_obj;
lean_object* v___y_2319_ = stack[1].m_obj;
lean_object* v___y_2320_ = stack[2].m_obj;
lean_object* v___y_2321_ = stack[3].m_obj;
lean_object* v___y_2322_ = stack[4].m_obj;
lean_object* v_res_2335_;
v_res_2335_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
stack->m_obj
 = v_res_2335_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg___boxed(lean_object* v_msg_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
return v_res_2342_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(lean_object* v_ref_2343_, lean_object* v_msg_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_toCold_2354_; lean_object* v_currRecDepth_2355_; lean_object* v_ref_2356_; uint16_t v_optionFlags_2357_; uint8_t v_suppressElabErrors_2358_; uint8_t v_isRecordingDeps_2359_; lean_object* v_ref_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v_toCold_2354_ = lean_ctor_get(v___y_2351_, 0);
v_currRecDepth_2355_ = lean_ctor_get(v___y_2351_, 1);
v_ref_2356_ = lean_ctor_get(v___y_2351_, 2);
v_optionFlags_2357_ = lean_ctor_get_uint16(v___y_2351_, sizeof(void*)*3);
v_suppressElabErrors_2358_ = lean_ctor_get_uint8(v___y_2351_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2359_ = lean_ctor_get_uint8(v___y_2351_, sizeof(void*)*3 + 3);
v_ref_2360_ = l_Lean_replaceRef(v_ref_2343_, v_ref_2356_);
lean_inc(v_currRecDepth_2355_);
lean_inc_ref(v_toCold_2354_);
v___x_2361_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2361_, 0, v_toCold_2354_);
lean_ctor_set(v___x_2361_, 1, v_currRecDepth_2355_);
lean_ctor_set(v___x_2361_, 2, v_ref_2360_);
lean_ctor_set_uint16(v___x_2361_, sizeof(void*)*3, v_optionFlags_2357_);
lean_ctor_set_uint8(v___x_2361_, sizeof(void*)*3 + 2, v_suppressElabErrors_2358_);
lean_ctor_set_uint8(v___x_2361_, sizeof(void*)*3 + 3, v_isRecordingDeps_2359_);
v___x_2362_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_2344_, v___y_2349_, v___y_2350_, v___x_2361_, v___y_2352_);
lean_dec_ref_known(v___x_2361_, 3);
return v___x_2362_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2343_ = stack[0].m_obj;
lean_object* v_msg_2344_ = stack[1].m_obj;
lean_object* v___y_2345_ = stack[2].m_obj;
lean_object* v___y_2346_ = stack[3].m_obj;
lean_object* v___y_2347_ = stack[4].m_obj;
lean_object* v___y_2348_ = stack[5].m_obj;
lean_object* v___y_2349_ = stack[6].m_obj;
lean_object* v___y_2350_ = stack[7].m_obj;
lean_object* v___y_2351_ = stack[8].m_obj;
lean_object* v___y_2352_ = stack[9].m_obj;
lean_object* v_res_2363_;
v_res_2363_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_ref_2343_, v_msg_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
stack->m_obj
 = v_res_2363_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2364_, lean_object* v_msg_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_ref_2364_, v_msg_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v_ref_2364_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(lean_object* v_env_2376_, lean_object* v_currNamespace_2377_, lean_object* v_openDecls_2378_, lean_object* v_n_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = l_Lean_ResolveName_resolveNamespace(v_env_2376_, v_currNamespace_2377_, v_openDecls_2378_, v_n_2379_);
v___x_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
lean_ctor_set(v___x_2383_, 1, v___y_2381_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed(lean_object* v_env_2384_, lean_object* v_currNamespace_2385_, lean_object* v_openDecls_2386_, lean_object* v_n_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(v_env_2384_, v_currNamespace_2385_, v_openDecls_2386_, v_n_2387_, v___y_2388_, v___y_2389_);
lean_dec_ref(v___y_2388_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(lean_object* v_env_2391_, lean_object* v___x_2392_, lean_object* v_currNamespace_2393_, lean_object* v_openDecls_2394_, lean_object* v_n_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = l_Lean_ResolveName_resolveGlobalName(v_env_2391_, v___x_2392_, v_currNamespace_2393_, v_openDecls_2394_, v_n_2395_);
v___x_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
lean_ctor_set(v___x_2399_, 1, v___y_2397_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed(lean_object* v_env_2400_, lean_object* v___x_2401_, lean_object* v_currNamespace_2402_, lean_object* v_openDecls_2403_, lean_object* v_n_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(v_env_2400_, v___x_2401_, v_currNamespace_2402_, v_openDecls_2403_, v_n_2404_, v___y_2405_, v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec_ref(v___x_2401_);
return v_res_2407_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = l_Lean_maxRecDepthErrorMessage;
v___x_2414_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
return v___x_2414_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3);
v___x_2416_ = l_Lean_MessageData_ofFormat(v___x_2415_);
return v___x_2416_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2417_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4);
v___x_2418_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2));
v___x_2419_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
lean_ctor_set(v___x_2419_, 1, v___x_2417_);
return v___x_2419_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(lean_object* v_ref_2420_){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2422_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5);
v___x_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2423_, 0, v_ref_2420_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2420_ = stack[0].m_obj;
lean_object* v_res_2425_;
v_res_2425_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_ref_2420_);
stack->m_obj
 = v_res_2425_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_ref_2426_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(lean_object* v_currNamespace_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2432_, 0, v_currNamespace_2429_);
lean_ctor_set(v___x_2432_, 1, v___y_2431_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed(lean_object* v_currNamespace_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(v_currNamespace_2433_, v___y_2434_, v___y_2435_);
lean_dec_ref(v___y_2434_);
return v_res_2436_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(lean_object* v_keys_2437_, lean_object* v_i_2438_, lean_object* v_k_2439_){
_start:
{
lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___x_2440_ = lean_array_get_size(v_keys_2437_);
v___x_2441_ = lean_nat_dec_lt(v_i_2438_, v___x_2440_);
if (v___x_2441_ == 0)
{
lean_dec(v_i_2438_);
return v___x_2441_;
}
else
{
lean_object* v_k_x27_2442_; uint8_t v___x_2443_; 
v_k_x27_2442_ = lean_array_fget_borrowed(v_keys_2437_, v_i_2438_);
v___x_2443_ = l_Lean_instBEqExtraModUse_beq(v_k_2439_, v_k_x27_2442_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = lean_unsigned_to_nat(1u);
v___x_2445_ = lean_nat_add(v_i_2438_, v___x_2444_);
lean_dec(v_i_2438_);
v_i_2438_ = v___x_2445_;
goto _start;
}
else
{
lean_dec(v_i_2438_);
return v___x_2441_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2437_ = stack[0].m_obj;
lean_object* v_i_2438_ = stack[1].m_obj;
lean_object* v_k_2439_ = stack[2].m_obj;
uint8_t v_res_2447_;
v_res_2447_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_keys_2437_, v_i_2438_, v_k_2439_);
stack->m_num = v_res_2447_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg___boxed(lean_object* v_keys_2448_, lean_object* v_i_2449_, lean_object* v_k_2450_){
_start:
{
uint8_t v_res_2451_; lean_object* v_r_2452_; 
v_res_2451_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_keys_2448_, v_i_2449_, v_k_2450_);
lean_dec_ref(v_k_2450_);
lean_dec_ref(v_keys_2448_);
v_r_2452_ = lean_box(v_res_2451_);
return v_r_2452_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(lean_object* v_x_2453_, size_t v_x_2454_, lean_object* v_x_2455_){
_start:
{
if (lean_obj_tag(v_x_2453_) == 0)
{
lean_object* v_es_2456_; lean_object* v___x_2457_; size_t v___x_2458_; size_t v___x_2459_; lean_object* v_j_2460_; lean_object* v___x_2461_; 
v_es_2456_ = lean_ctor_get(v_x_2453_, 0);
v___x_2457_ = lean_box(2);
v___x_2458_ = ((size_t)31ULL);
v___x_2459_ = lean_usize_land(v_x_2454_, v___x_2458_);
v_j_2460_ = lean_usize_to_nat(v___x_2459_);
v___x_2461_ = lean_array_get_borrowed(v___x_2457_, v_es_2456_, v_j_2460_);
lean_dec(v_j_2460_);
switch(lean_obj_tag(v___x_2461_))
{
case 0:
{
lean_object* v_key_2462_; uint8_t v___x_2463_; 
v_key_2462_ = lean_ctor_get(v___x_2461_, 0);
v___x_2463_ = l_Lean_instBEqExtraModUse_beq(v_x_2455_, v_key_2462_);
return v___x_2463_;
}
case 1:
{
lean_object* v_node_2464_; size_t v___x_2465_; size_t v___x_2466_; 
v_node_2464_ = lean_ctor_get(v___x_2461_, 0);
v___x_2465_ = ((size_t)5ULL);
v___x_2466_ = lean_usize_shift_right(v_x_2454_, v___x_2465_);
v_x_2453_ = v_node_2464_;
v_x_2454_ = v___x_2466_;
goto _start;
}
default: 
{
uint8_t v___x_2468_; 
v___x_2468_ = 0;
return v___x_2468_;
}
}
}
else
{
lean_object* v_ks_2469_; lean_object* v___x_2470_; uint8_t v___x_2471_; 
v_ks_2469_ = lean_ctor_get(v_x_2453_, 0);
v___x_2470_ = lean_unsigned_to_nat(0u);
v___x_2471_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_ks_2469_, v___x_2470_, v_x_2455_);
return v___x_2471_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2453_ = stack[0].m_obj;
size_t v_x_2454_ = stack[1].m_num;
lean_object* v_x_2455_ = stack[2].m_obj;
uint8_t v_res_2472_;
v_res_2472_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_2453_, v_x_2454_, v_x_2455_);
stack->m_num = v_res_2472_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_x_2473_, lean_object* v_x_2474_, lean_object* v_x_2475_){
_start:
{
size_t v_x_20879__boxed_2476_; uint8_t v_res_2477_; lean_object* v_r_2478_; 
v_x_20879__boxed_2476_ = lean_unbox_usize(v_x_2474_);
lean_dec(v_x_2474_);
v_res_2477_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_2473_, v_x_20879__boxed_2476_, v_x_2475_);
lean_dec_ref(v_x_2475_);
lean_dec_ref(v_x_2473_);
v_r_2478_ = lean_box(v_res_2477_);
return v_r_2478_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(lean_object* v_x_2479_, lean_object* v_x_2480_){
_start:
{
uint64_t v___x_2481_; size_t v___x_2482_; uint8_t v___x_2483_; 
v___x_2481_ = l_Lean_instHashableExtraModUse_hash(v_x_2480_);
v___x_2482_ = lean_uint64_to_usize(v___x_2481_);
v___x_2483_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_2479_, v___x_2482_, v_x_2480_);
return v___x_2483_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2479_ = stack[0].m_obj;
lean_object* v_x_2480_ = stack[1].m_obj;
uint8_t v_res_2484_;
v_res_2484_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v_x_2479_, v_x_2480_);
stack->m_num = v_res_2484_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_x_2485_, lean_object* v_x_2486_){
_start:
{
uint8_t v_res_2487_; lean_object* v_r_2488_; 
v_res_2487_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v_x_2485_, v_x_2486_);
lean_dec_ref(v_x_2486_);
lean_dec_ref(v_x_2485_);
v_r_2488_ = lean_box(v_res_2487_);
return v_r_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___lam__0(lean_object* v___x_2489_, lean_object* v_entry_2490_, lean_object* v_s_2491_){
_start:
{
lean_object* v_addEntryFn_2492_; lean_object* v_importedEntries_2493_; lean_object* v_state_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2502_; 
v_addEntryFn_2492_ = lean_ctor_get(v___x_2489_, 3);
lean_inc(v_addEntryFn_2492_);
lean_dec_ref(v___x_2489_);
v_importedEntries_2493_ = lean_ctor_get(v_s_2491_, 0);
v_state_2494_ = lean_ctor_get(v_s_2491_, 1);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_s_2491_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2496_ = v_s_2491_;
v_isShared_2497_ = v_isSharedCheck_2502_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_state_2494_);
lean_inc(v_importedEntries_2493_);
lean_dec(v_s_2491_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2502_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v_state_2498_; lean_object* v___x_2500_; 
v_state_2498_ = lean_apply_2(v_addEntryFn_2492_, v_state_2494_, v_entry_2490_);
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 1, v_state_2498_);
v___x_2500_ = v___x_2496_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_importedEntries_2493_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v_state_2498_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2503_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0);
v___x_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
return v___x_2505_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1);
v___x_2507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
return v___x_2507_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1);
v___x_2509_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
lean_ctor_set(v___x_2509_, 2, v___x_2508_);
lean_ctor_set(v___x_2509_, 3, v___x_2508_);
lean_ctor_set(v___x_2509_, 4, v___x_2508_);
lean_ctor_set(v___x_2509_, 5, v___x_2508_);
return v___x_2509_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4(void){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2510_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7));
v___x_2516_ = l_Lean_stringToMessageData(v___x_2515_);
return v___x_2516_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9));
v___x_2519_ = l_Lean_stringToMessageData(v___x_2518_);
return v___x_2519_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1));
v___x_2521_ = l_Lean_stringToMessageData(v___x_2520_);
return v___x_2521_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v_cls_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v_cls_2522_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6));
v___x_2523_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1));
v___x_2524_ = l_Lean_Name_append(v___x_2523_, v_cls_2522_);
return v___x_2524_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13));
v___x_2527_ = l_Lean_stringToMessageData(v___x_2526_);
return v___x_2527_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15));
v___x_2530_ = l_Lean_stringToMessageData(v___x_2529_);
return v___x_2530_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(lean_object* v_mod_2535_, uint8_t v_isMeta_2536_, lean_object* v_hint_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v_env_2581_; uint8_t v_isExporting_2582_; lean_object* v_entry_2583_; lean_object* v___x_2584_; lean_object* v_env_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2579_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4);
v___x_2580_ = lean_st_ref_get(v___y_2545_);
v_env_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc_ref(v_env_2581_);
lean_dec(v___x_2580_);
v_isExporting_2582_ = lean_ctor_get_uint8(v_env_2581_, sizeof(void*)*13);
lean_dec_ref(v_env_2581_);
lean_inc(v_mod_2535_);
v_entry_2583_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2583_, 0, v_mod_2535_);
lean_ctor_set_uint8(v_entry_2583_, sizeof(void*)*1, v_isExporting_2582_);
lean_ctor_set_uint8(v_entry_2583_, sizeof(void*)*1 + 1, v_isMeta_2536_);
v___x_2584_ = lean_st_ref_get(v___y_2545_);
v_env_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc_ref(v_env_2585_);
lean_dec(v___x_2584_);
v___x_2586_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2587_ = lean_box(1);
v___x_2588_ = lean_box(0);
v___x_2589_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2579_, v___x_2586_, v_env_2585_, v___x_2587_, v___x_2588_);
v___x_2590_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v___x_2589_, v_entry_2583_);
lean_dec(v___x_2589_);
if (v___x_2590_ == 0)
{
lean_object* v_toCold_2591_; lean_object* v_options_2592_; lean_object* v_inheritedTraceOptions_2593_; uint8_t v_hasTrace_2594_; lean_object* v___f_2595_; uint8_t v___x_2596_; lean_object* v___y_2598_; lean_object* v___y_2599_; 
v_toCold_2591_ = lean_ctor_get(v___y_2544_, 0);
v_options_2592_ = lean_ctor_get(v_toCold_2591_, 2);
v_inheritedTraceOptions_2593_ = lean_ctor_get(v_toCold_2591_, 11);
v_hasTrace_2594_ = lean_ctor_get_uint8(v_options_2592_, sizeof(void*)*1);
v___f_2595_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___lam__0), 3, 2);
lean_closure_set(v___f_2595_, 0, v___x_2586_);
lean_closure_set(v___f_2595_, 1, v_entry_2583_);
v___x_2596_ = 1;
if (v_hasTrace_2594_ == 0)
{
lean_dec(v_hint_2537_);
lean_dec(v_mod_2535_);
v___y_2598_ = v___y_2543_;
v___y_2599_ = v___y_2545_;
goto v___jp_2597_;
}
else
{
lean_object* v_cls_2626_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___x_2646_; uint8_t v___x_2647_; 
v_cls_2626_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6));
v___x_2646_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12);
v___x_2647_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2593_, v_options_2592_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_dec(v_hint_2537_);
lean_dec(v_mod_2535_);
v___y_2598_ = v___y_2543_;
v___y_2599_ = v___y_2545_;
goto v___jp_2597_;
}
else
{
lean_object* v___x_2648_; lean_object* v___y_2650_; 
v___x_2648_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14);
if (v_isExporting_2582_ == 0)
{
lean_object* v___x_2657_; 
v___x_2657_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19));
v___y_2650_ = v___x_2657_;
goto v___jp_2649_;
}
else
{
lean_object* v___x_2658_; 
v___x_2658_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20));
v___y_2650_ = v___x_2658_;
goto v___jp_2649_;
}
v___jp_2649_:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_inc_ref(v___y_2650_);
v___x_2651_ = l_Lean_stringToMessageData(v___y_2650_);
v___x_2652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2648_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16);
v___x_2654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2652_);
lean_ctor_set(v___x_2654_, 1, v___x_2653_);
if (v_isMeta_2536_ == 0)
{
lean_object* v___x_2655_; 
v___x_2655_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17));
v___y_2633_ = v___x_2654_;
v___y_2634_ = v___x_2655_;
goto v___jp_2632_;
}
else
{
lean_object* v___x_2656_; 
v___x_2656_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18));
v___y_2633_ = v___x_2654_;
v___y_2634_ = v___x_2656_;
goto v___jp_2632_;
}
}
}
v___jp_2627_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___y_2628_);
lean_ctor_set(v___x_2630_, 1, v___y_2629_);
v___x_2631_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_2626_, v___x_2630_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_dec_ref_known(v___x_2631_, 1);
v___y_2598_ = v___y_2543_;
v___y_2599_ = v___y_2545_;
goto v___jp_2597_;
}
else
{
lean_dec_ref(v___f_2595_);
return v___x_2631_;
}
}
v___jp_2632_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; uint8_t v___x_2641_; 
lean_inc_ref(v___y_2634_);
v___x_2635_ = l_Lean_stringToMessageData(v___y_2634_);
v___x_2636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___y_2633_);
lean_ctor_set(v___x_2636_, 1, v___x_2635_);
v___x_2637_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8);
v___x_2638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2636_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
v___x_2639_ = l_Lean_MessageData_ofName(v_mod_2535_);
v___x_2640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2638_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
v___x_2641_ = l_Lean_Name_isAnonymous(v_hint_2537_);
if (v___x_2641_ == 0)
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2642_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10);
v___x_2643_ = l_Lean_MessageData_ofName(v_hint_2537_);
v___x_2644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2642_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
v___y_2628_ = v___x_2640_;
v___y_2629_ = v___x_2644_;
goto v___jp_2627_;
}
else
{
lean_object* v___x_2645_; 
lean_dec(v_hint_2537_);
v___x_2645_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11);
v___y_2628_ = v___x_2640_;
v___y_2629_ = v___x_2645_;
goto v___jp_2627_;
}
}
}
v___jp_2597_:
{
lean_object* v___x_2600_; lean_object* v_toEnvExtension_2601_; uint8_t v_logWrites_2602_; 
v___x_2600_ = lean_st_ref_take(v___y_2599_);
v_toEnvExtension_2601_ = lean_ctor_get(v___x_2586_, 0);
v_logWrites_2602_ = lean_ctor_get_uint8(v_toEnvExtension_2601_, sizeof(void*)*6);
if (v_logWrites_2602_ == 0)
{
lean_object* v_env_2603_; lean_object* v_nextMacroScope_2604_; lean_object* v_ngen_2605_; lean_object* v_auxDeclNGen_2606_; lean_object* v_traceState_2607_; lean_object* v_recordedDeps_2608_; lean_object* v_messages_2609_; lean_object* v_infoState_2610_; lean_object* v_snapshotTasks_2611_; lean_object* v_asyncMode_2612_; lean_object* v___x_2613_; 
v_env_2603_ = lean_ctor_get(v___x_2600_, 0);
lean_inc_ref(v_env_2603_);
v_nextMacroScope_2604_ = lean_ctor_get(v___x_2600_, 1);
lean_inc(v_nextMacroScope_2604_);
v_ngen_2605_ = lean_ctor_get(v___x_2600_, 2);
lean_inc_ref(v_ngen_2605_);
v_auxDeclNGen_2606_ = lean_ctor_get(v___x_2600_, 3);
lean_inc_ref(v_auxDeclNGen_2606_);
v_traceState_2607_ = lean_ctor_get(v___x_2600_, 4);
lean_inc_ref(v_traceState_2607_);
v_recordedDeps_2608_ = lean_ctor_get(v___x_2600_, 6);
lean_inc_ref(v_recordedDeps_2608_);
v_messages_2609_ = lean_ctor_get(v___x_2600_, 7);
lean_inc_ref(v_messages_2609_);
v_infoState_2610_ = lean_ctor_get(v___x_2600_, 8);
lean_inc_ref(v_infoState_2610_);
v_snapshotTasks_2611_ = lean_ctor_get(v___x_2600_, 9);
lean_inc_ref(v_snapshotTasks_2611_);
lean_dec(v___x_2600_);
v_asyncMode_2612_ = lean_ctor_get(v_toEnvExtension_2601_, 2);
lean_inc_ref(v_toEnvExtension_2601_);
v___x_2613_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2601_, v_env_2603_, v___f_2595_, v_asyncMode_2612_, v___x_2588_, v___x_2596_);
v___y_2548_ = v_snapshotTasks_2611_;
v___y_2549_ = v___y_2599_;
v___y_2550_ = v_auxDeclNGen_2606_;
v___y_2551_ = v_infoState_2610_;
v___y_2552_ = v_nextMacroScope_2604_;
v___y_2553_ = v_messages_2609_;
v___y_2554_ = v___y_2598_;
v___y_2555_ = v_recordedDeps_2608_;
v___y_2556_ = v_traceState_2607_;
v___y_2557_ = v_ngen_2605_;
v___y_2558_ = v___x_2613_;
goto v___jp_2547_;
}
else
{
lean_object* v_env_2614_; lean_object* v_nextMacroScope_2615_; lean_object* v_ngen_2616_; lean_object* v_auxDeclNGen_2617_; lean_object* v_traceState_2618_; lean_object* v_recordedDeps_2619_; lean_object* v_messages_2620_; lean_object* v_infoState_2621_; lean_object* v_snapshotTasks_2622_; lean_object* v_asyncMode_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v_env_2614_ = lean_ctor_get(v___x_2600_, 0);
lean_inc_ref(v_env_2614_);
v_nextMacroScope_2615_ = lean_ctor_get(v___x_2600_, 1);
lean_inc(v_nextMacroScope_2615_);
v_ngen_2616_ = lean_ctor_get(v___x_2600_, 2);
lean_inc_ref(v_ngen_2616_);
v_auxDeclNGen_2617_ = lean_ctor_get(v___x_2600_, 3);
lean_inc_ref(v_auxDeclNGen_2617_);
v_traceState_2618_ = lean_ctor_get(v___x_2600_, 4);
lean_inc_ref(v_traceState_2618_);
v_recordedDeps_2619_ = lean_ctor_get(v___x_2600_, 6);
lean_inc_ref(v_recordedDeps_2619_);
v_messages_2620_ = lean_ctor_get(v___x_2600_, 7);
lean_inc_ref(v_messages_2620_);
v_infoState_2621_ = lean_ctor_get(v___x_2600_, 8);
lean_inc_ref(v_infoState_2621_);
v_snapshotTasks_2622_ = lean_ctor_get(v___x_2600_, 9);
lean_inc_ref(v_snapshotTasks_2622_);
lean_dec(v___x_2600_);
v_asyncMode_2623_ = lean_ctor_get(v_toEnvExtension_2601_, 2);
lean_inc_ref_n(v_toEnvExtension_2601_, 2);
v___x_2624_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2601_, v_env_2614_);
lean_dec_ref(v_env_2614_);
v___x_2625_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2601_, v___x_2624_, v___f_2595_, v_asyncMode_2623_, v___x_2588_, v___x_2596_);
v___y_2548_ = v_snapshotTasks_2622_;
v___y_2549_ = v___y_2599_;
v___y_2550_ = v_auxDeclNGen_2617_;
v___y_2551_ = v_infoState_2621_;
v___y_2552_ = v_nextMacroScope_2615_;
v___y_2553_ = v_messages_2620_;
v___y_2554_ = v___y_2598_;
v___y_2555_ = v_recordedDeps_2619_;
v___y_2556_ = v_traceState_2618_;
v___y_2557_ = v_ngen_2616_;
v___y_2558_ = v___x_2625_;
goto v___jp_2547_;
}
}
}
else
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
lean_dec_ref_known(v_entry_2583_, 1);
lean_dec(v_hint_2537_);
lean_dec(v_mod_2535_);
v___x_2659_ = lean_box(0);
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
return v___x_2660_;
}
v___jp_2547_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v_mctx_2563_; lean_object* v_zetaDeltaFVarIds_2564_; lean_object* v_postponed_2565_; lean_object* v_diag_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2577_; 
v___x_2559_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2);
v___x_2560_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2560_, 0, v___y_2558_);
lean_ctor_set(v___x_2560_, 1, v___y_2552_);
lean_ctor_set(v___x_2560_, 2, v___y_2557_);
lean_ctor_set(v___x_2560_, 3, v___y_2550_);
lean_ctor_set(v___x_2560_, 4, v___y_2556_);
lean_ctor_set(v___x_2560_, 5, v___x_2559_);
lean_ctor_set(v___x_2560_, 6, v___y_2555_);
lean_ctor_set(v___x_2560_, 7, v___y_2553_);
lean_ctor_set(v___x_2560_, 8, v___y_2551_);
lean_ctor_set(v___x_2560_, 9, v___y_2548_);
v___x_2561_ = lean_st_ref_put(v___y_2549_, v___x_2560_);
v___x_2562_ = lean_st_ref_take(v___y_2554_);
v_mctx_2563_ = lean_ctor_get(v___x_2562_, 0);
v_zetaDeltaFVarIds_2564_ = lean_ctor_get(v___x_2562_, 2);
v_postponed_2565_ = lean_ctor_get(v___x_2562_, 3);
v_diag_2566_ = lean_ctor_get(v___x_2562_, 4);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2577_ == 0)
{
lean_object* v_unused_2578_; 
v_unused_2578_ = lean_ctor_get(v___x_2562_, 1);
lean_dec(v_unused_2578_);
v___x_2568_ = v___x_2562_;
v_isShared_2569_ = v_isSharedCheck_2577_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_diag_2566_);
lean_inc(v_postponed_2565_);
lean_inc(v_zetaDeltaFVarIds_2564_);
lean_inc(v_mctx_2563_);
lean_dec(v___x_2562_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2577_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2573_; 
v___x_2570_ = lean_box(0);
v___x_2571_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 1, v___x_2571_);
v___x_2573_ = v___x_2568_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_mctx_2563_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v___x_2571_);
lean_ctor_set(v_reuseFailAlloc_2576_, 2, v_zetaDeltaFVarIds_2564_);
lean_ctor_set(v_reuseFailAlloc_2576_, 3, v_postponed_2565_);
lean_ctor_set(v_reuseFailAlloc_2576_, 4, v_diag_2566_);
v___x_2573_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2574_ = lean_st_ref_put(v___y_2554_, v___x_2573_);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2570_);
return v___x_2575_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_2535_ = stack[0].m_obj;
uint8_t v_isMeta_2536_ = stack[1].m_num;
lean_object* v_hint_2537_ = stack[2].m_obj;
lean_object* v___y_2538_ = stack[3].m_obj;
lean_object* v___y_2539_ = stack[4].m_obj;
lean_object* v___y_2540_ = stack[5].m_obj;
lean_object* v___y_2541_ = stack[6].m_obj;
lean_object* v___y_2542_ = stack[7].m_obj;
lean_object* v___y_2543_ = stack[8].m_obj;
lean_object* v___y_2544_ = stack[9].m_obj;
lean_object* v___y_2545_ = stack[10].m_obj;
lean_object* v_res_2661_;
v_res_2661_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_mod_2535_, v_isMeta_2536_, v_hint_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
stack->m_obj
 = v_res_2661_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___boxed(lean_object* v_mod_2662_, lean_object* v_isMeta_2663_, lean_object* v_hint_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
uint8_t v_isMeta_boxed_2674_; lean_object* v_res_2675_; 
v_isMeta_boxed_2674_ = lean_unbox(v_isMeta_2663_);
v_res_2675_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_mod_2662_, v_isMeta_boxed_2674_, v_hint_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(lean_object* v_a_2676_, lean_object* v_x_2677_){
_start:
{
if (lean_obj_tag(v_x_2677_) == 0)
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_box(0);
return v___x_2678_;
}
else
{
lean_object* v_key_2679_; lean_object* v_value_2680_; lean_object* v_tail_2681_; uint8_t v___x_2682_; 
v_key_2679_ = lean_ctor_get(v_x_2677_, 0);
v_value_2680_ = lean_ctor_get(v_x_2677_, 1);
v_tail_2681_ = lean_ctor_get(v_x_2677_, 2);
v___x_2682_ = lean_name_eq(v_key_2679_, v_a_2676_);
if (v___x_2682_ == 0)
{
v_x_2677_ = v_tail_2681_;
goto _start;
}
else
{
lean_object* v___x_2684_; 
lean_inc(v_value_2680_);
v___x_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2684_, 0, v_value_2680_);
return v___x_2684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_a_2685_, lean_object* v_x_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_2685_, v_x_2686_);
lean_dec(v_x_2686_);
lean_dec(v_a_2685_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(lean_object* v_m_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_buckets_2690_; lean_object* v___x_2691_; uint64_t v___y_2693_; 
v_buckets_2690_ = lean_ctor_get(v_m_2688_, 1);
v___x_2691_ = lean_array_get_size(v_buckets_2690_);
if (lean_obj_tag(v_a_2689_) == 0)
{
uint64_t v___x_2707_; 
v___x_2707_ = 1723ULL;
v___y_2693_ = v___x_2707_;
goto v___jp_2692_;
}
else
{
uint64_t v_hash_2708_; 
v_hash_2708_ = lean_ctor_get_uint64(v_a_2689_, sizeof(void*)*2);
v___y_2693_ = v_hash_2708_;
goto v___jp_2692_;
}
v___jp_2692_:
{
uint64_t v___x_2694_; uint64_t v___x_2695_; uint64_t v_fold_2696_; uint64_t v___x_2697_; uint64_t v___x_2698_; uint64_t v___x_2699_; size_t v___x_2700_; size_t v___x_2701_; size_t v___x_2702_; size_t v___x_2703_; size_t v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2694_ = 32ULL;
v___x_2695_ = lean_uint64_shift_right(v___y_2693_, v___x_2694_);
v_fold_2696_ = lean_uint64_xor(v___y_2693_, v___x_2695_);
v___x_2697_ = 16ULL;
v___x_2698_ = lean_uint64_shift_right(v_fold_2696_, v___x_2697_);
v___x_2699_ = lean_uint64_xor(v_fold_2696_, v___x_2698_);
v___x_2700_ = lean_uint64_to_usize(v___x_2699_);
v___x_2701_ = lean_usize_of_nat(v___x_2691_);
v___x_2702_ = ((size_t)1ULL);
v___x_2703_ = lean_usize_sub(v___x_2701_, v___x_2702_);
v___x_2704_ = lean_usize_land(v___x_2700_, v___x_2703_);
v___x_2705_ = lean_array_uget_borrowed(v_buckets_2690_, v___x_2704_);
v___x_2706_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_2689_, v___x_2705_);
return v___x_2706_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_m_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v_m_2709_, v_a_2710_);
lean_dec(v_a_2710_);
lean_dec_ref(v_m_2709_);
return v_res_2711_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(lean_object* v___x_2712_, lean_object* v_declName_2713_, lean_object* v_as_2714_, size_t v_sz_2715_, size_t v_i_2716_, lean_object* v_b_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
uint8_t v___x_2727_; 
v___x_2727_ = lean_usize_dec_lt(v_i_2716_, v_sz_2715_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2728_; 
lean_dec(v_declName_2713_);
v___x_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2728_, 0, v_b_2717_);
return v___x_2728_;
}
else
{
lean_object* v___x_2729_; lean_object* v_modules_2730_; lean_object* v___x_2731_; lean_object* v_a_2732_; lean_object* v___x_2733_; lean_object* v_toImport_2734_; lean_object* v_module_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; lean_object* v___x_2738_; 
v___x_2729_ = l_Lean_Environment_header(v___x_2712_);
v_modules_2730_ = lean_ctor_get(v___x_2729_, 3);
lean_inc_ref(v_modules_2730_);
lean_dec_ref(v___x_2729_);
v___x_2731_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2732_ = lean_array_uget_borrowed(v_as_2714_, v_i_2716_);
v___x_2733_ = lean_array_get(v___x_2731_, v_modules_2730_, v_a_2732_);
lean_dec_ref(v_modules_2730_);
v_toImport_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc_ref(v_toImport_2734_);
lean_dec(v___x_2733_);
v_module_2735_ = lean_ctor_get(v_toImport_2734_, 0);
lean_inc(v_module_2735_);
lean_dec_ref(v_toImport_2734_);
v___x_2736_ = lean_box(0);
v___x_2737_ = 0;
lean_inc(v_declName_2713_);
v___x_2738_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_module_2735_, v___x_2737_, v_declName_2713_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
if (lean_obj_tag(v___x_2738_) == 0)
{
size_t v___x_2739_; size_t v___x_2740_; 
lean_dec_ref_known(v___x_2738_, 1);
v___x_2739_ = ((size_t)1ULL);
v___x_2740_ = lean_usize_add(v_i_2716_, v___x_2739_);
v_i_2716_ = v___x_2740_;
v_b_2717_ = v___x_2736_;
goto _start;
}
else
{
lean_dec(v_declName_2713_);
return v___x_2738_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2712_ = stack[0].m_obj;
lean_object* v_declName_2713_ = stack[1].m_obj;
lean_object* v_as_2714_ = stack[2].m_obj;
size_t v_sz_2715_ = stack[3].m_num;
size_t v_i_2716_ = stack[4].m_num;
lean_object* v_b_2717_ = stack[5].m_obj;
lean_object* v___y_2718_ = stack[6].m_obj;
lean_object* v___y_2719_ = stack[7].m_obj;
lean_object* v___y_2720_ = stack[8].m_obj;
lean_object* v___y_2721_ = stack[9].m_obj;
lean_object* v___y_2722_ = stack[10].m_obj;
lean_object* v___y_2723_ = stack[11].m_obj;
lean_object* v___y_2724_ = stack[12].m_obj;
lean_object* v___y_2725_ = stack[13].m_obj;
lean_object* v_res_2742_;
v_res_2742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(v___x_2712_, v_declName_2713_, v_as_2714_, v_sz_2715_, v_i_2716_, v_b_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
stack->m_obj
 = v_res_2742_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6___boxed(lean_object* v___x_2743_, lean_object* v_declName_2744_, lean_object* v_as_2745_, lean_object* v_sz_2746_, lean_object* v_i_2747_, lean_object* v_b_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
size_t v_sz_boxed_2758_; size_t v_i_boxed_2759_; lean_object* v_res_2760_; 
v_sz_boxed_2758_ = lean_unbox_usize(v_sz_2746_);
lean_dec(v_sz_2746_);
v_i_boxed_2759_ = lean_unbox_usize(v_i_2747_);
lean_dec(v_i_2747_);
v_res_2760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(v___x_2743_, v_declName_2744_, v_as_2745_, v_sz_boxed_2758_, v_i_boxed_2759_, v_b_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec_ref(v_as_2745_);
lean_dec_ref(v___x_2743_);
return v_res_2760_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2761_;
}
}
lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(lean_object* v_declName_2764_, uint8_t v_isMeta_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v_env_2780_; lean_object* v___y_2782_; lean_object* v___x_2795_; 
v___x_2775_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0);
v___x_2776_ = lean_st_ref_get(v___y_2773_);
v_env_2780_ = lean_ctor_get(v___x_2776_, 0);
lean_inc_ref(v_env_2780_);
lean_dec(v___x_2776_);
v___x_2795_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2780_, v_declName_2764_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_dec_ref(v_env_2780_);
lean_dec(v_declName_2764_);
goto v___jp_2777_;
}
else
{
lean_object* v_val_2796_; lean_object* v___x_2797_; lean_object* v_modules_2798_; lean_object* v___x_2799_; uint8_t v___x_2800_; 
v_val_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_val_2796_);
lean_dec_ref_known(v___x_2795_, 1);
v___x_2797_ = l_Lean_Environment_header(v_env_2780_);
v_modules_2798_ = lean_ctor_get(v___x_2797_, 3);
lean_inc_ref(v_modules_2798_);
lean_dec_ref(v___x_2797_);
v___x_2799_ = lean_array_get_size(v_modules_2798_);
v___x_2800_ = lean_nat_dec_lt(v_val_2796_, v___x_2799_);
if (v___x_2800_ == 0)
{
lean_dec_ref(v_modules_2798_);
lean_dec(v_val_2796_);
lean_dec_ref(v_env_2780_);
lean_dec(v_declName_2764_);
goto v___jp_2777_;
}
else
{
lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___y_2804_; 
v___x_2801_ = lean_array_fget(v_modules_2798_, v_val_2796_);
lean_dec(v_val_2796_);
lean_dec_ref(v_modules_2798_);
v___x_2802_ = lean_st_ref_get(v___y_2773_);
if (v_isMeta_2765_ == 0)
{
lean_dec(v___x_2802_);
v___y_2804_ = v_isMeta_2765_;
goto v___jp_2803_;
}
else
{
lean_object* v_env_2815_; uint8_t v___x_2816_; 
v_env_2815_ = lean_ctor_get(v___x_2802_, 0);
lean_inc_ref(v_env_2815_);
lean_dec(v___x_2802_);
lean_inc(v_declName_2764_);
v___x_2816_ = l_Lean_isMarkedMeta(v_env_2815_, v_declName_2764_);
if (v___x_2816_ == 0)
{
v___y_2804_ = v_isMeta_2765_;
goto v___jp_2803_;
}
else
{
uint8_t v___x_2817_; 
v___x_2817_ = 0;
v___y_2804_ = v___x_2817_;
goto v___jp_2803_;
}
}
v___jp_2803_:
{
lean_object* v_toImport_2805_; lean_object* v_module_2806_; lean_object* v___x_2807_; 
v_toImport_2805_ = lean_ctor_get(v___x_2801_, 0);
lean_inc_ref(v_toImport_2805_);
lean_dec(v___x_2801_);
v_module_2806_ = lean_ctor_get(v_toImport_2805_, 0);
lean_inc(v_module_2806_);
lean_dec_ref(v_toImport_2805_);
lean_inc(v_declName_2764_);
v___x_2807_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_module_2806_, v___y_2804_, v_declName_2764_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
lean_dec_ref_known(v___x_2807_, 1);
v___x_2808_ = l_Lean_indirectModUseExt;
v___x_2809_ = lean_box(1);
v___x_2810_ = lean_box(0);
lean_inc_ref(v_env_2780_);
v___x_2811_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2775_, v___x_2808_, v_env_2780_, v___x_2809_, v___x_2810_);
v___x_2812_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v___x_2811_, v_declName_2764_);
lean_dec(v___x_2811_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v___x_2813_; 
v___x_2813_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1));
v___y_2782_ = v___x_2813_;
goto v___jp_2781_;
}
else
{
lean_object* v_val_2814_; 
v_val_2814_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_val_2814_);
lean_dec_ref_known(v___x_2812_, 1);
v___y_2782_ = v_val_2814_;
goto v___jp_2781_;
}
}
else
{
lean_dec_ref(v_env_2780_);
lean_dec(v_declName_2764_);
return v___x_2807_;
}
}
}
}
v___jp_2777_:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2778_ = lean_box(0);
v___x_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
return v___x_2779_;
}
v___jp_2781_:
{
lean_object* v___x_2783_; size_t v_sz_2784_; size_t v___x_2785_; lean_object* v___x_2786_; 
v___x_2783_ = lean_box(0);
v_sz_2784_ = lean_array_size(v___y_2782_);
v___x_2785_ = ((size_t)0ULL);
v___x_2786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(v_env_2780_, v_declName_2764_, v___y_2782_, v_sz_2784_, v___x_2785_, v___x_2783_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec_ref(v___y_2782_);
lean_dec_ref(v_env_2780_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2793_ == 0)
{
lean_object* v_unused_2794_; 
v_unused_2794_ = lean_ctor_get(v___x_2786_, 0);
lean_dec(v_unused_2794_);
v___x_2788_ = v___x_2786_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_dec(v___x_2786_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 0, v___x_2783_);
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2783_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
else
{
return v___x_2786_;
}
}
}
}
LEAN_EXPORT void l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2764_ = stack[0].m_obj;
uint8_t v_isMeta_2765_ = stack[1].m_num;
lean_object* v___y_2766_ = stack[2].m_obj;
lean_object* v___y_2767_ = stack[3].m_obj;
lean_object* v___y_2768_ = stack[4].m_obj;
lean_object* v___y_2769_ = stack[5].m_obj;
lean_object* v___y_2770_ = stack[6].m_obj;
lean_object* v___y_2771_ = stack[7].m_obj;
lean_object* v___y_2772_ = stack[8].m_obj;
lean_object* v___y_2773_ = stack[9].m_obj;
lean_object* v_res_2818_;
v_res_2818_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(v_declName_2764_, v_isMeta_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
stack->m_obj
 = v_res_2818_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___boxed(lean_object* v_declName_2819_, lean_object* v_isMeta_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
uint8_t v_isMeta_boxed_2830_; lean_object* v_res_2831_; 
v_isMeta_boxed_2830_ = lean_unbox(v_isMeta_2820_);
v_res_2831_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(v_declName_2819_, v_isMeta_boxed_2830_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
return v_res_2831_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(lean_object* v_as_x27_2832_, lean_object* v_b_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
if (lean_obj_tag(v_as_x27_2832_) == 0)
{
lean_object* v___x_2843_; 
v___x_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2843_, 0, v_b_2833_);
return v___x_2843_;
}
else
{
lean_object* v_head_2844_; lean_object* v_tail_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; lean_object* v___x_2848_; 
v_head_2844_ = lean_ctor_get(v_as_x27_2832_, 0);
v_tail_2845_ = lean_ctor_get(v_as_x27_2832_, 1);
v___x_2846_ = lean_box(0);
v___x_2847_ = 1;
lean_inc(v_head_2844_);
v___x_2848_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(v_head_2844_, v___x_2847_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_dec_ref_known(v___x_2848_, 1);
v_as_x27_2832_ = v_tail_2845_;
v_b_2833_ = v___x_2846_;
goto _start;
}
else
{
return v___x_2848_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_2832_ = stack[0].m_obj;
lean_object* v_b_2833_ = stack[1].m_obj;
lean_object* v___y_2834_ = stack[2].m_obj;
lean_object* v___y_2835_ = stack[3].m_obj;
lean_object* v___y_2836_ = stack[4].m_obj;
lean_object* v___y_2837_ = stack[5].m_obj;
lean_object* v___y_2838_ = stack[6].m_obj;
lean_object* v___y_2839_ = stack[7].m_obj;
lean_object* v___y_2840_ = stack[8].m_obj;
lean_object* v___y_2841_ = stack[9].m_obj;
lean_object* v_res_2850_;
v_res_2850_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_as_x27_2832_, v_b_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
stack->m_obj
 = v_res_2850_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2851_, lean_object* v_b_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_as_x27_2851_, v_b_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v_as_x27_2851_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(lean_object* v_x_2863_, lean_object* v___y_2864_){
_start:
{
if (lean_obj_tag(v_x_2863_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2866_; 
v_a_2865_ = lean_ctor_get(v_x_2863_, 0);
lean_inc(v_a_2865_);
v___x_2866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2866_, 0, v_a_2865_);
lean_ctor_set(v___x_2866_, 1, v___y_2864_);
return v___x_2866_;
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2868_; 
v_a_2867_ = lean_ctor_get(v_x_2863_, 0);
lean_inc(v_a_2867_);
v___x_2868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2868_, 0, v_a_2867_);
lean_ctor_set(v___x_2868_, 1, v___y_2864_);
return v___x_2868_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___boxed(lean_object* v_x_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v_x_2869_, v___y_2870_);
lean_dec_ref(v_x_2869_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1(lean_object* v_env_2872_, lean_object* v_stx_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2872_, v_stx_2873_, v___y_2874_, v___y_2875_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
if (lean_obj_tag(v_a_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2886_; 
v_a_2878_ = lean_ctor_get(v___x_2876_, 1);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2886_ == 0)
{
lean_object* v_unused_2887_; 
v_unused_2887_ = lean_ctor_get(v___x_2876_, 0);
lean_dec(v_unused_2887_);
v___x_2880_ = v___x_2876_;
v_isShared_2881_ = v_isSharedCheck_2886_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2876_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2886_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2882_; lean_object* v___x_2884_; 
v___x_2882_ = lean_box(0);
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 0, v___x_2882_);
v___x_2884_ = v___x_2880_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2882_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v_a_2878_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
else
{
lean_object* v_val_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2916_; 
v_val_2888_ = lean_ctor_get(v_a_2877_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_a_2877_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2890_ = v_a_2877_;
v_isShared_2891_ = v_isSharedCheck_2916_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_val_2888_);
lean_dec(v_a_2877_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2916_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v_snd_2892_; 
v_snd_2892_ = lean_ctor_get(v_val_2888_, 1);
lean_inc(v_snd_2892_);
lean_dec(v_val_2888_);
if (lean_obj_tag(v_snd_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2902_; 
lean_del_object(v___x_2890_);
v_a_2893_ = lean_ctor_get(v___x_2876_, 1);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2876_, 2);
v_a_2894_ = lean_ctor_get(v_snd_2892_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_snd_2892_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2896_ = v_snd_2892_;
v_isShared_2897_ = v_isSharedCheck_2902_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v_snd_2892_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2902_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v___x_2899_, v_a_2893_);
lean_dec_ref(v___x_2899_);
return v___x_2900_;
}
}
}
else
{
lean_object* v_a_2903_; lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2915_; 
v_a_2903_ = lean_ctor_get(v___x_2876_, 1);
lean_inc(v_a_2903_);
lean_dec_ref_known(v___x_2876_, 2);
v_a_2904_ = lean_ctor_get(v_snd_2892_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v_snd_2892_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2906_ = v_snd_2892_;
v_isShared_2907_ = v_isSharedCheck_2915_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v_snd_2892_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2915_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v_a_2904_);
v___x_2909_ = v___x_2890_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
lean_object* v___x_2911_; 
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2909_);
v___x_2911_ = v___x_2906_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
lean_object* v___x_2912_; 
v___x_2912_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v___x_2911_, v_a_2903_);
lean_dec_ref(v___x_2911_);
return v___x_2912_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2917_; lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
v_a_2917_ = lean_ctor_get(v___x_2876_, 0);
v_a_2918_ = lean_ctor_get(v___x_2876_, 1);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2876_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_inc(v_a_2917_);
lean_dec(v___x_2876_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2917_);
lean_ctor_set(v_reuseFailAlloc_2924_, 1, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1___boxed(lean_object* v_env_2926_, lean_object* v_stx_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1(v_env_2926_, v_stx_2927_, v___y_2928_, v___y_2929_);
lean_dec_ref(v___y_2928_);
return v_res_2930_;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(lean_object* v_x_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v___x_2942_; lean_object* v_toCold_2943_; lean_object* v_env_2944_; lean_object* v_currRecDepth_2945_; lean_object* v_ref_2946_; lean_object* v_maxRecDepth_2947_; lean_object* v_currNamespace_2948_; lean_object* v_openDecls_2949_; lean_object* v_quotContext_2950_; lean_object* v_currMacroScope_2951_; lean_object* v___f_2952_; lean_object* v___f_2953_; lean_object* v___x_2954_; lean_object* v___f_2955_; lean_object* v___f_2956_; lean_object* v___f_2957_; lean_object* v_methods_2958_; lean_object* v___x_2959_; lean_object* v_nextMacroScope_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2942_ = lean_st_ref_get(v___y_2940_);
v_toCold_2943_ = lean_ctor_get(v___y_2939_, 0);
v_env_2944_ = lean_ctor_get(v___x_2942_, 0);
lean_inc_ref_n(v_env_2944_, 4);
lean_dec(v___x_2942_);
v_currRecDepth_2945_ = lean_ctor_get(v___y_2939_, 1);
v_ref_2946_ = lean_ctor_get(v___y_2939_, 2);
v_maxRecDepth_2947_ = lean_ctor_get(v_toCold_2943_, 3);
v_currNamespace_2948_ = lean_ctor_get(v_toCold_2943_, 4);
v_openDecls_2949_ = lean_ctor_get(v_toCold_2943_, 5);
v_quotContext_2950_ = lean_ctor_get(v_toCold_2943_, 8);
v_currMacroScope_2951_ = lean_ctor_get(v_toCold_2943_, 9);
v___f_2952_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2952_, 0, v_env_2944_);
v___f_2953_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2953_, 0, v_env_2944_);
v___x_2954_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2939_);
lean_inc_n(v_currNamespace_2948_, 3);
v___f_2955_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2955_, 0, v_currNamespace_2948_);
lean_inc_n(v_openDecls_2949_, 2);
v___f_2956_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_2956_, 0, v_env_2944_);
lean_closure_set(v___f_2956_, 1, v___x_2954_);
lean_closure_set(v___f_2956_, 2, v_currNamespace_2948_);
lean_closure_set(v___f_2956_, 3, v_openDecls_2949_);
v___f_2957_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2957_, 0, v_env_2944_);
lean_closure_set(v___f_2957_, 1, v_currNamespace_2948_);
lean_closure_set(v___f_2957_, 2, v_openDecls_2949_);
v_methods_2958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2958_, 0, v___f_2953_);
lean_ctor_set(v_methods_2958_, 1, v___f_2955_);
lean_ctor_set(v_methods_2958_, 2, v___f_2952_);
lean_ctor_set(v_methods_2958_, 3, v___f_2957_);
lean_ctor_set(v_methods_2958_, 4, v___f_2956_);
v___x_2959_ = lean_st_ref_get(v___y_2940_);
v_nextMacroScope_2960_ = lean_ctor_get(v___x_2959_, 1);
lean_inc(v_nextMacroScope_2960_);
lean_dec(v___x_2959_);
lean_inc(v_ref_2946_);
lean_inc(v_maxRecDepth_2947_);
lean_inc(v_currRecDepth_2945_);
lean_inc(v_currMacroScope_2951_);
lean_inc(v_quotContext_2950_);
v___x_2961_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2961_, 0, v_methods_2958_);
lean_ctor_set(v___x_2961_, 1, v_quotContext_2950_);
lean_ctor_set(v___x_2961_, 2, v_currMacroScope_2951_);
lean_ctor_set(v___x_2961_, 3, v_currRecDepth_2945_);
lean_ctor_set(v___x_2961_, 4, v_maxRecDepth_2947_);
lean_ctor_set(v___x_2961_, 5, v_ref_2946_);
v___x_2962_ = lean_box(0);
v___x_2963_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2963_, 0, v_nextMacroScope_2960_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
lean_ctor_set(v___x_2963_, 2, v___x_2962_);
v___x_2964_ = lean_apply_2(v_x_2932_, v___x_2961_, v___x_2963_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v_a_2966_; lean_object* v_macroScope_2967_; lean_object* v_traceMsgs_2968_; lean_object* v_expandedMacroDecls_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 1);
lean_inc(v_a_2965_);
v_a_2966_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2966_);
lean_dec_ref_known(v___x_2964_, 2);
v_macroScope_2967_ = lean_ctor_get(v_a_2965_, 0);
lean_inc(v_macroScope_2967_);
v_traceMsgs_2968_ = lean_ctor_get(v_a_2965_, 1);
lean_inc(v_traceMsgs_2968_);
v_expandedMacroDecls_2969_ = lean_ctor_get(v_a_2965_, 2);
lean_inc(v_expandedMacroDecls_2969_);
lean_dec(v_a_2965_);
v___x_2970_ = lean_box(0);
v___x_2971_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_expandedMacroDecls_2969_, v___x_2970_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
lean_dec(v_expandedMacroDecls_2969_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v___x_2972_; lean_object* v_env_2973_; lean_object* v_ngen_2974_; lean_object* v_auxDeclNGen_2975_; lean_object* v_traceState_2976_; lean_object* v_cache_2977_; lean_object* v_recordedDeps_2978_; lean_object* v_messages_2979_; lean_object* v_infoState_2980_; lean_object* v_snapshotTasks_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_3007_; 
lean_dec_ref_known(v___x_2971_, 1);
v___x_2972_ = lean_st_ref_take(v___y_2940_);
v_env_2973_ = lean_ctor_get(v___x_2972_, 0);
v_ngen_2974_ = lean_ctor_get(v___x_2972_, 2);
v_auxDeclNGen_2975_ = lean_ctor_get(v___x_2972_, 3);
v_traceState_2976_ = lean_ctor_get(v___x_2972_, 4);
v_cache_2977_ = lean_ctor_get(v___x_2972_, 5);
v_recordedDeps_2978_ = lean_ctor_get(v___x_2972_, 6);
v_messages_2979_ = lean_ctor_get(v___x_2972_, 7);
v_infoState_2980_ = lean_ctor_get(v___x_2972_, 8);
v_snapshotTasks_2981_ = lean_ctor_get(v___x_2972_, 9);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3007_ == 0)
{
lean_object* v_unused_3008_; 
v_unused_3008_ = lean_ctor_get(v___x_2972_, 1);
lean_dec(v_unused_3008_);
v___x_2983_ = v___x_2972_;
v_isShared_2984_ = v_isSharedCheck_3007_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_snapshotTasks_2981_);
lean_inc(v_infoState_2980_);
lean_inc(v_messages_2979_);
lean_inc(v_recordedDeps_2978_);
lean_inc(v_cache_2977_);
lean_inc(v_traceState_2976_);
lean_inc(v_auxDeclNGen_2975_);
lean_inc(v_ngen_2974_);
lean_inc(v_env_2973_);
lean_dec(v___x_2972_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_3007_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 1, v_macroScope_2967_);
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_env_2973_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_macroScope_2967_);
lean_ctor_set(v_reuseFailAlloc_3006_, 2, v_ngen_2974_);
lean_ctor_set(v_reuseFailAlloc_3006_, 3, v_auxDeclNGen_2975_);
lean_ctor_set(v_reuseFailAlloc_3006_, 4, v_traceState_2976_);
lean_ctor_set(v_reuseFailAlloc_3006_, 5, v_cache_2977_);
lean_ctor_set(v_reuseFailAlloc_3006_, 6, v_recordedDeps_2978_);
lean_ctor_set(v_reuseFailAlloc_3006_, 7, v_messages_2979_);
lean_ctor_set(v_reuseFailAlloc_3006_, 8, v_infoState_2980_);
lean_ctor_set(v_reuseFailAlloc_3006_, 9, v_snapshotTasks_2981_);
v___x_2986_ = v_reuseFailAlloc_3006_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2987_ = lean_st_ref_put(v___y_2940_, v___x_2986_);
v___x_2988_ = l_List_reverse___redArg(v_traceMsgs_2968_);
v___x_2989_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(v___x_2988_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_2996_ == 0)
{
lean_object* v_unused_2997_; 
v_unused_2997_ = lean_ctor_get(v___x_2989_, 0);
lean_dec(v_unused_2997_);
v___x_2991_ = v___x_2989_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_dec(v___x_2989_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 0, v_a_2966_);
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2966_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec(v_a_2966_);
v_a_2998_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2989_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2989_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec(v_traceMsgs_2968_);
lean_dec(v_macroScope_2967_);
lean_dec(v_a_2966_);
v_a_3009_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_2971_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_2971_);
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
lean_object* v_a_3017_; 
v_a_3017_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_2964_, 2);
if (lean_obj_tag(v_a_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v_a_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; 
v_a_3018_ = lean_ctor_get(v_a_3017_, 0);
lean_inc(v_a_3018_);
v_a_3019_ = lean_ctor_get(v_a_3017_, 1);
lean_inc_ref(v_a_3019_);
lean_dec_ref_known(v_a_3017_, 2);
v___x_3020_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0));
v___x_3021_ = lean_string_dec_eq(v_a_3019_, v___x_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3022_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3022_, 0, v_a_3019_);
v___x_3023_ = l_Lean_MessageData_ofFormat(v___x_3022_);
v___x_3024_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_a_3018_, v___x_3023_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
lean_dec(v_a_3018_);
return v___x_3024_;
}
else
{
lean_object* v___x_3025_; 
lean_dec_ref(v_a_3019_);
v___x_3025_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_a_3018_);
return v___x_3025_;
}
}
else
{
lean_object* v___x_3026_; 
v___x_3026_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_3026_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2932_ = stack[0].m_obj;
lean_object* v___y_2933_ = stack[1].m_obj;
lean_object* v___y_2934_ = stack[2].m_obj;
lean_object* v___y_2935_ = stack[3].m_obj;
lean_object* v___y_2936_ = stack[4].m_obj;
lean_object* v___y_2937_ = stack[5].m_obj;
lean_object* v___y_2938_ = stack[6].m_obj;
lean_object* v___y_2939_ = stack[7].m_obj;
lean_object* v___y_2940_ = stack[8].m_obj;
lean_object* v_res_3027_;
v_res_3027_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v_x_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
stack->m_obj
 = v_res_3027_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___boxed(lean_object* v_x_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v_x_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
return v_res_3038_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(lean_object* v_x_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_){
_start:
{
lean_object* v___x_3059_; uint8_t v___x_3060_; 
v___x_3059_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2));
lean_inc(v_x_3049_);
v___x_3060_ = l_Lean_Syntax_isOfKind(v_x_3049_, v___x_3059_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; 
lean_dec(v_x_3049_);
v___x_3061_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_3061_;
}
else
{
lean_object* v___x_3062_; lean_object* v_hyp_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; 
v___x_3062_ = lean_unsigned_to_nat(1u);
v_hyp_3063_ = l_Lean_Syntax_getArg(v_x_3049_, v___x_3062_);
v___x_3064_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4));
lean_inc(v_hyp_3063_);
v___x_3065_ = l_Lean_Syntax_isOfKind(v_hyp_3063_, v___x_3064_);
if (v___x_3065_ == 0)
{
lean_object* v___x_3066_; 
lean_dec(v_hyp_3063_);
lean_dec(v_x_3049_);
v___x_3066_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_3066_;
}
else
{
lean_object* v___x_3067_; lean_object* v_pat_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3067_ = lean_unsigned_to_nat(3u);
v_pat_3068_ = l_Lean_Syntax_getArg(v_x_3049_, v___x_3067_);
lean_dec(v_x_3049_);
v___x_3069_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_MCasesPat_parse___boxed), 3, 1);
lean_closure_set(v___x_3069_, 0, v_pat_3068_);
v___x_3070_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v___x_3069_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; lean_object* v___x_3072_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3071_);
lean_dec_ref_known(v___x_3070_, 1);
v___x_3072_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_3051_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v_fst_3074_; lean_object* v_snd_3075_; lean_object* v___f_3076_; lean_object* v___x_3077_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3073_);
lean_dec_ref_known(v___x_3072_, 1);
v_fst_3074_ = lean_ctor_get(v_a_3073_, 0);
lean_inc_n(v_fst_3074_, 2);
v_snd_3075_ = lean_ctor_get(v_a_3073_, 1);
lean_inc(v_snd_3075_);
lean_dec(v_a_3073_);
v___f_3076_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___boxed), 13, 4);
lean_closure_set(v___f_3076_, 0, v_snd_3075_);
lean_closure_set(v___f_3076_, 1, v_hyp_3063_);
lean_closure_set(v___f_3076_, 2, v_a_3071_);
lean_closure_set(v___f_3076_, 3, v_fst_3074_);
v___x_3077_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_fst_3074_, v___f_3076_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
return v___x_3077_;
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v_a_3071_);
lean_dec(v_hyp_3063_);
v_a_3078_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3072_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3072_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec(v_hyp_3063_);
v_a_3086_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3070_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3070_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMCases_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3049_ = stack[0].m_obj;
lean_object* v_a_3050_ = stack[1].m_obj;
lean_object* v_a_3051_ = stack[2].m_obj;
lean_object* v_a_3052_ = stack[3].m_obj;
lean_object* v_a_3053_ = stack[4].m_obj;
lean_object* v_a_3054_ = stack[5].m_obj;
lean_object* v_a_3055_ = stack[6].m_obj;
lean_object* v_a_3056_ = stack[7].m_obj;
lean_object* v_a_3057_ = stack[8].m_obj;
lean_object* v_res_3094_;
v_res_3094_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(v_x_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
stack->m_obj
 = v_res_3094_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___boxed(lean_object* v_x_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(v_x_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_);
lean_dec(v_a_3103_);
lean_dec_ref(v_a_3102_);
lean_dec(v_a_3101_);
lean_dec_ref(v_a_3100_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(lean_object* v_00_u03b1_3106_, lean_object* v_x_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v_x_3107_, v___y_3109_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3111_, lean_object* v_x_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(v_00_u03b1_3111_, v_x_3112_, v___y_3113_, v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec_ref(v_x_3112_);
return v_res_3115_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(lean_object* v_00_u03b1_3116_, lean_object* v_ref_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_ref_3117_);
return v___x_3127_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3117_ = stack[1].m_obj;
lean_object* v___y_3118_ = stack[2].m_obj;
lean_object* v___y_3119_ = stack[3].m_obj;
lean_object* v___y_3120_ = stack[4].m_obj;
lean_object* v___y_3121_ = stack[5].m_obj;
lean_object* v___y_3122_ = stack[6].m_obj;
lean_object* v___y_3123_ = stack[7].m_obj;
lean_object* v___y_3124_ = stack[8].m_obj;
lean_object* v___y_3125_ = stack[9].m_obj;
lean_object* v_res_3128_;
v_res_3128_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(lean_box(0), v_ref_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
stack->m_obj
 = v_res_3128_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3129_, lean_object* v_ref_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(v_00_u03b1_3129_, v_ref_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
return v_res_3140_;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(lean_object* v_00_u03b1_3141_, lean_object* v_x_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v_x_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
return v___x_3152_;
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3142_ = stack[1].m_obj;
lean_object* v___y_3143_ = stack[2].m_obj;
lean_object* v___y_3144_ = stack[3].m_obj;
lean_object* v___y_3145_ = stack[4].m_obj;
lean_object* v___y_3146_ = stack[5].m_obj;
lean_object* v___y_3147_ = stack[6].m_obj;
lean_object* v___y_3148_ = stack[7].m_obj;
lean_object* v___y_3149_ = stack[8].m_obj;
lean_object* v___y_3150_ = stack[9].m_obj;
lean_object* v_res_3153_;
v_res_3153_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(lean_box(0), v_x_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
stack->m_obj
 = v_res_3153_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___boxed(lean_object* v_00_u03b1_3154_, lean_object* v_x_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(v_00_u03b1_3154_, v_x_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
return v_res_3165_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(lean_object* v_mvarId_3166_, lean_object* v_val_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v___x_3177_; 
v___x_3177_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_mvarId_3166_, v_val_3167_, v___y_3173_);
return v___x_3177_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3166_ = stack[0].m_obj;
lean_object* v_val_3167_ = stack[1].m_obj;
lean_object* v___y_3168_ = stack[2].m_obj;
lean_object* v___y_3169_ = stack[3].m_obj;
lean_object* v___y_3170_ = stack[4].m_obj;
lean_object* v___y_3171_ = stack[5].m_obj;
lean_object* v___y_3172_ = stack[6].m_obj;
lean_object* v___y_3173_ = stack[7].m_obj;
lean_object* v___y_3174_ = stack[8].m_obj;
lean_object* v___y_3175_ = stack[9].m_obj;
lean_object* v_res_3178_;
v_res_3178_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(v_mvarId_3166_, v_val_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
stack->m_obj
 = v_res_3178_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___boxed(lean_object* v_mvarId_3179_, lean_object* v_val_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(v_mvarId_3179_, v_val_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
return v_res_3190_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(lean_object* v_cls_3191_, lean_object* v_msg_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v___x_3202_; 
v___x_3202_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_3191_, v_msg_3192_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
return v___x_3202_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3191_ = stack[0].m_obj;
lean_object* v_msg_3192_ = stack[1].m_obj;
lean_object* v___y_3193_ = stack[2].m_obj;
lean_object* v___y_3194_ = stack[3].m_obj;
lean_object* v___y_3195_ = stack[4].m_obj;
lean_object* v___y_3196_ = stack[5].m_obj;
lean_object* v___y_3197_ = stack[6].m_obj;
lean_object* v___y_3198_ = stack[7].m_obj;
lean_object* v___y_3199_ = stack[8].m_obj;
lean_object* v___y_3200_ = stack[9].m_obj;
lean_object* v_res_3203_;
v_res_3203_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(v_cls_3191_, v_msg_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
stack->m_obj
 = v_res_3203_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___boxed(lean_object* v_cls_3204_, lean_object* v_msg_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(v_cls_3204_, v_msg_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
return v_res_3215_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(lean_object* v_as_3216_, lean_object* v_as_x27_3217_, lean_object* v_b_3218_, lean_object* v_a_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_as_x27_3217_, v_b_3218_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
return v___x_3229_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3216_ = stack[0].m_obj;
lean_object* v_as_x27_3217_ = stack[1].m_obj;
lean_object* v_b_3218_ = stack[2].m_obj;
lean_object* v___y_3220_ = stack[4].m_obj;
lean_object* v___y_3221_ = stack[5].m_obj;
lean_object* v___y_3222_ = stack[6].m_obj;
lean_object* v___y_3223_ = stack[7].m_obj;
lean_object* v___y_3224_ = stack[8].m_obj;
lean_object* v___y_3225_ = stack[9].m_obj;
lean_object* v___y_3226_ = stack[10].m_obj;
lean_object* v___y_3227_ = stack[11].m_obj;
lean_object* v_res_3230_;
v_res_3230_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(v_as_3216_, v_as_x27_3217_, v_b_3218_, lean_box(0), v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
stack->m_obj
 = v_res_3230_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___boxed(lean_object* v_as_3231_, lean_object* v_as_x27_3232_, lean_object* v_b_3233_, lean_object* v_a_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(v_as_3231_, v_as_x27_3232_, v_b_3233_, v_a_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v_as_x27_3232_);
lean_dec(v_as_3231_);
return v_res_3244_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(lean_object* v_00_u03b1_3245_, lean_object* v_ref_3246_, lean_object* v_msg_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v___x_3257_; 
v___x_3257_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_ref_3246_, v_msg_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
return v___x_3257_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3246_ = stack[1].m_obj;
lean_object* v_msg_3247_ = stack[2].m_obj;
lean_object* v___y_3248_ = stack[3].m_obj;
lean_object* v___y_3249_ = stack[4].m_obj;
lean_object* v___y_3250_ = stack[5].m_obj;
lean_object* v___y_3251_ = stack[6].m_obj;
lean_object* v___y_3252_ = stack[7].m_obj;
lean_object* v___y_3253_ = stack[8].m_obj;
lean_object* v___y_3254_ = stack[9].m_obj;
lean_object* v___y_3255_ = stack[10].m_obj;
lean_object* v_res_3258_;
v_res_3258_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(lean_box(0), v_ref_3246_, v_msg_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
stack->m_obj
 = v_res_3258_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3259_, lean_object* v_ref_3260_, lean_object* v_msg_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(v_00_u03b1_3259_, v_ref_3260_, v_msg_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v_ref_3260_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9(lean_object* v_00_u03b2_3272_, lean_object* v_x_3273_, lean_object* v_x_3274_, lean_object* v_x_3275_){
_start:
{
lean_object* v___x_3276_; 
v___x_3276_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(v_x_3273_, v_x_3274_, v_x_3275_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3277_, lean_object* v_m_3278_, lean_object* v_a_3279_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v_m_3278_, v_a_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3281_, lean_object* v_m_3282_, lean_object* v_a_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7(v_00_u03b2_3281_, v_m_3282_, v_a_3283_);
lean_dec(v_a_3283_);
lean_dec_ref(v_m_3282_);
return v_res_3284_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11(lean_object* v_00_u03b1_3285_, lean_object* v_msg_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_3286_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
return v___x_3296_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3286_ = stack[1].m_obj;
lean_object* v___y_3287_ = stack[2].m_obj;
lean_object* v___y_3288_ = stack[3].m_obj;
lean_object* v___y_3289_ = stack[4].m_obj;
lean_object* v___y_3290_ = stack[5].m_obj;
lean_object* v___y_3291_ = stack[6].m_obj;
lean_object* v___y_3292_ = stack[7].m_obj;
lean_object* v___y_3293_ = stack[8].m_obj;
lean_object* v___y_3294_ = stack[9].m_obj;
lean_object* v_res_3297_;
v_res_3297_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11(lean_box(0), v_msg_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
stack->m_obj
 = v_res_3297_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___boxed(lean_object* v_00_u03b1_3298_, lean_object* v_msg_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11(v_00_u03b1_3298_, v_msg_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
return v_res_3309_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15(lean_object* v_00_u03b2_3310_, lean_object* v_x_3311_, size_t v_x_3312_, size_t v_x_3313_, lean_object* v_x_3314_, lean_object* v_x_3315_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_3311_, v_x_3312_, v_x_3313_, v_x_3314_, v_x_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3311_ = stack[1].m_obj;
size_t v_x_3312_ = stack[2].m_num;
size_t v_x_3313_ = stack[3].m_num;
lean_object* v_x_3314_ = stack[4].m_obj;
lean_object* v_x_3315_ = stack[5].m_obj;
lean_object* v_res_3317_;
v_res_3317_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15(lean_box(0), v_x_3311_, v_x_3312_, v_x_3313_, v_x_3314_, v_x_3315_);
stack->m_obj
 = v_res_3317_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___boxed(lean_object* v_00_u03b2_3318_, lean_object* v_x_3319_, lean_object* v_x_3320_, lean_object* v_x_3321_, lean_object* v_x_3322_, lean_object* v_x_3323_){
_start:
{
size_t v_x_22762__boxed_3324_; size_t v_x_22763__boxed_3325_; lean_object* v_res_3326_; 
v_x_22762__boxed_3324_ = lean_unbox_usize(v_x_3320_);
lean_dec(v_x_3320_);
v_x_22763__boxed_3325_ = lean_unbox_usize(v_x_3321_);
lean_dec(v_x_3321_);
v_res_3326_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15(v_00_u03b2_3318_, v_x_3319_, v_x_22762__boxed_3324_, v_x_22763__boxed_3325_, v_x_3322_, v_x_3323_);
return v_res_3326_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_3327_, lean_object* v_x_3328_, lean_object* v_x_3329_){
_start:
{
uint8_t v___x_3330_; 
v___x_3330_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v_x_3328_, v_x_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3328_ = stack[1].m_obj;
lean_object* v_x_3329_ = stack[2].m_obj;
uint8_t v_res_3331_;
v_res_3331_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8(lean_box(0), v_x_3328_, v_x_3329_);
stack->m_num = v_res_3331_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3332_, lean_object* v_x_3333_, lean_object* v_x_3334_){
_start:
{
uint8_t v_res_3335_; lean_object* v_r_3336_; 
v_res_3335_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8(v_00_u03b2_3332_, v_x_3333_, v_x_3334_);
lean_dec_ref(v_x_3334_);
lean_dec_ref(v_x_3333_);
v_r_3336_ = lean_box(v_res_3335_);
return v_r_3336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11(lean_object* v_00_u03b2_3337_, lean_object* v_a_3338_, lean_object* v_x_3339_){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_3338_, v_x_3339_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3341_, lean_object* v_a_3342_, lean_object* v_x_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11(v_00_u03b2_3341_, v_a_3342_, v_x_3343_);
lean_dec(v_x_3343_);
lean_dec(v_a_3342_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18(lean_object* v_00_u03b2_3345_, lean_object* v_n_3346_, lean_object* v_k_3347_, lean_object* v_v_3348_){
_start:
{
lean_object* v___x_3349_; 
v___x_3349_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(v_n_3346_, v_k_3347_, v_v_3348_);
return v___x_3349_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19(lean_object* v_00_u03b2_3350_, size_t v_depth_3351_, lean_object* v_keys_3352_, lean_object* v_vals_3353_, lean_object* v_heq_3354_, lean_object* v_i_3355_, lean_object* v_entries_3356_){
_start:
{
lean_object* v___x_3357_; 
v___x_3357_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_depth_3351_, v_keys_3352_, v_vals_3353_, v_i_3355_, v_entries_3356_);
return v___x_3357_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19_0interp(lean_interpreter_value* stack)
{
size_t v_depth_3351_ = stack[1].m_num;
lean_object* v_keys_3352_ = stack[2].m_obj;
lean_object* v_vals_3353_ = stack[3].m_obj;
lean_object* v_i_3355_ = stack[5].m_obj;
lean_object* v_entries_3356_ = stack[6].m_obj;
lean_object* v_res_3358_;
v_res_3358_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19(lean_box(0), v_depth_3351_, v_keys_3352_, v_vals_3353_, lean_box(0), v_i_3355_, v_entries_3356_);
stack->m_obj
 = v_res_3358_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___boxed(lean_object* v_00_u03b2_3359_, lean_object* v_depth_3360_, lean_object* v_keys_3361_, lean_object* v_vals_3362_, lean_object* v_heq_3363_, lean_object* v_i_3364_, lean_object* v_entries_3365_){
_start:
{
size_t v_depth_boxed_3366_; lean_object* v_res_3367_; 
v_depth_boxed_3366_ = lean_unbox_usize(v_depth_3360_);
lean_dec(v_depth_3360_);
v_res_3367_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19(v_00_u03b2_3359_, v_depth_boxed_3366_, v_keys_3361_, v_vals_3362_, v_heq_3363_, v_i_3364_, v_entries_3365_);
lean_dec_ref(v_vals_3362_);
lean_dec_ref(v_keys_3361_);
return v_res_3367_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13(lean_object* v_00_u03b2_3368_, lean_object* v_x_3369_, size_t v_x_3370_, lean_object* v_x_3371_){
_start:
{
uint8_t v___x_3372_; 
v___x_3372_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_3369_, v_x_3370_, v_x_3371_);
return v___x_3372_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3369_ = stack[1].m_obj;
size_t v_x_3370_ = stack[2].m_num;
lean_object* v_x_3371_ = stack[3].m_obj;
uint8_t v_res_3373_;
v_res_3373_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13(lean_box(0), v_x_3369_, v_x_3370_, v_x_3371_);
stack->m_num = v_res_3373_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___boxed(lean_object* v_00_u03b2_3374_, lean_object* v_x_3375_, lean_object* v_x_3376_, lean_object* v_x_3377_){
_start:
{
size_t v_x_22817__boxed_3378_; uint8_t v_res_3379_; lean_object* v_r_3380_; 
v_x_22817__boxed_3378_ = lean_unbox_usize(v_x_3376_);
lean_dec(v_x_3376_);
v_res_3379_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13(v_00_u03b2_3374_, v_x_3375_, v_x_22817__boxed_3378_, v_x_3377_);
lean_dec_ref(v_x_3377_);
lean_dec_ref(v_x_3375_);
v_r_3380_ = lean_box(v_res_3379_);
return v_r_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20(lean_object* v_00_u03b2_3381_, lean_object* v_x_3382_, lean_object* v_x_3383_, lean_object* v_x_3384_, lean_object* v_x_3385_){
_start:
{
lean_object* v___x_3386_; 
v___x_3386_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(v_x_3382_, v_x_3383_, v_x_3384_, v_x_3385_);
return v___x_3386_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18(lean_object* v_00_u03b2_3387_, lean_object* v_keys_3388_, lean_object* v_vals_3389_, lean_object* v_heq_3390_, lean_object* v_i_3391_, lean_object* v_k_3392_){
_start:
{
uint8_t v___x_3393_; 
v___x_3393_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_keys_3388_, v_i_3391_, v_k_3392_);
return v___x_3393_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_3388_ = stack[1].m_obj;
lean_object* v_vals_3389_ = stack[2].m_obj;
lean_object* v_i_3391_ = stack[4].m_obj;
lean_object* v_k_3392_ = stack[5].m_obj;
uint8_t v_res_3394_;
v_res_3394_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18(lean_box(0), v_keys_3388_, v_vals_3389_, lean_box(0), v_i_3391_, v_k_3392_);
stack->m_num = v_res_3394_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___boxed(lean_object* v_00_u03b2_3395_, lean_object* v_keys_3396_, lean_object* v_vals_3397_, lean_object* v_heq_3398_, lean_object* v_i_3399_, lean_object* v_k_3400_){
_start:
{
uint8_t v_res_3401_; lean_object* v_r_3402_; 
v_res_3401_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18(v_00_u03b2_3395_, v_keys_3396_, v_vals_3397_, v_heq_3398_, v_i_3399_, v_k_3400_);
lean_dec_ref(v_k_3400_);
lean_dec_ref(v_vals_3397_);
lean_dec_ref(v_keys_3396_);
v_r_3402_ = lean_box(v_res_3401_);
return v_r_3402_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1(){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3412_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3413_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2));
v___x_3414_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1));
v___x_3415_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___boxed), 10, 0);
v___x_3416_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3412_, v___x_3413_, v___x_3414_, v___x_3415_);
return v___x_3416_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3417_;
v_res_3417_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1();
stack->m_obj
 = v_res_3417_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___boxed(lean_object* v_a_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1();
return v_res_3419_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1();
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
